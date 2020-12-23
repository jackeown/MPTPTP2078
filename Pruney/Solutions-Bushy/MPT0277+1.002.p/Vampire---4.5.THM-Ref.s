%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0277+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:40 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 109 expanded)
%              Number of leaves         :   10 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :  157 ( 309 expanded)
%              Number of equality atoms :   69 ( 187 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f47,f52,f64,f73,f74,f84,f100,f112,f122])).

fof(f122,plain,
    ( spl3_2
    | spl3_4
    | ~ spl3_5
    | spl3_6
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl3_2
    | spl3_4
    | ~ spl3_5
    | spl3_6
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f113,f58,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f58,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_5
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f113,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | spl3_2
    | spl3_4
    | spl3_6
    | spl3_7 ),
    inference(unit_resulting_resolution,[],[f46,f63,f33,f72,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f72,plain,
    ( sK0 != k1_tarski(sK2)
    | spl3_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl3_7
  <=> sK0 = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f33,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_2
  <=> sK0 = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f63,plain,
    ( sK0 != k1_tarski(sK1)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl3_6
  <=> sK0 = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f46,plain,
    ( k1_xboole_0 != sK0
    | spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl3_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f112,plain,
    ( spl3_5
    | ~ spl3_7 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f65,f102])).

fof(f102,plain,
    ( ! [X1] : r1_tarski(sK0,k2_tarski(X1,sK2))
    | ~ spl3_7 ),
    inference(superposition,[],[f21,f71])).

fof(f71,plain,
    ( sK0 = k1_tarski(sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f21,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f65,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f59,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f59,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f100,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f29,f92,f18])).

fof(f92,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl3_2 ),
    inference(superposition,[],[f20,f32])).

fof(f32,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f20,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f29,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f84,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f59,f75,f18])).

fof(f75,plain,
    ( ! [X0] : r1_tarski(sK0,k2_tarski(sK1,X0))
    | ~ spl3_6 ),
    inference(superposition,[],[f22,f62])).

fof(f62,plain,
    ( sK0 = k1_tarski(sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f61])).

fof(f22,plain,(
    ! [X2,X1] : r1_tarski(k1_tarski(X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f74,plain,
    ( spl3_5
    | spl3_2
    | spl3_7
    | spl3_6
    | spl3_4 ),
    inference(avatar_split_clause,[],[f12,f44,f61,f70,f31,f57])).

fof(f12,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f73,plain,
    ( ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f10,f70,f57])).

fof(f10,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f64,plain,
    ( ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f9,f61,f57])).

fof(f9,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f52,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f49])).

fof(f49,plain,
    ( $false
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f23,f42,f18])).

fof(f42,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_3
  <=> k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f23,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f47,plain,
    ( ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f25,f44,f40])).

fof(f25,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1,sK2)) ),
    inference(inner_rewriting,[],[f8])).

fof(f8,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f34,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f24,f31,f27])).

fof(f24,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,sK0) ),
    inference(inner_rewriting,[],[f11])).

fof(f11,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

%------------------------------------------------------------------------------
