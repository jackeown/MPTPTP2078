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
% DateTime   : Thu Dec  3 12:41:32 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 160 expanded)
%              Number of leaves         :   15 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  206 ( 398 expanded)
%              Number of equality atoms :   89 ( 222 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f82,f95,f107,f115,f172,f173,f203,f221,f224,f226,f228,f229,f254,f280])).

fof(f280,plain,
    ( spl4_3
    | ~ spl4_5 ),
    inference(avatar_contradiction_clause,[],[f275])).

fof(f275,plain,
    ( $false
    | spl4_3
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f81,f257])).

fof(f257,plain,
    ( ! [X1] : r1_tarski(sK0,k2_tarski(X1,sK2))
    | ~ spl4_5 ),
    inference(superposition,[],[f64,f90])).

fof(f90,plain,
    ( sK0 = k2_tarski(sK2,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl4_5
  <=> sK0 = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f64,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X2,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f46,f27])).

fof(f27,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f81,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | spl4_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl4_3
  <=> r1_tarski(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f254,plain,
    ( spl4_3
    | ~ spl4_6 ),
    inference(avatar_contradiction_clause,[],[f249])).

fof(f249,plain,
    ( $false
    | spl4_3
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f81,f232])).

fof(f232,plain,
    ( ! [X0] : r1_tarski(sK0,k2_tarski(sK1,X0))
    | ~ spl4_6 ),
    inference(superposition,[],[f65,f94])).

fof(f94,plain,
    ( sK0 = k2_tarski(sK1,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl4_6
  <=> sK0 = k2_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f65,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f45,f27])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X1) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f229,plain,
    ( ~ spl4_1
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f50,f92,f68])).

fof(f68,plain,
    ( spl4_1
  <=> k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f50,plain,
    ( sK0 != k2_tarski(sK1,sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f21,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f228,plain,
    ( spl4_2
    | ~ spl4_3
    | spl4_4
    | spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f227])).

fof(f227,plain,
    ( $false
    | spl4_2
    | ~ spl4_3
    | spl4_4
    | spl4_5
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f74,f85,f80,f93,f89,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_tarski(X1,X2))
      | k2_tarski(X1,X1) = X0
      | k2_tarski(X2,X2) = X0
      | k2_tarski(X1,X2) = X0
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f43,f27,f27])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | k1_tarski(X1) = X0
      | k1_tarski(X2) = X0
      | k2_tarski(X1,X2) = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f89,plain,
    ( sK0 != k2_tarski(sK2,sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f93,plain,
    ( sK0 != k2_tarski(sK1,sK1)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f80,plain,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f79])).

fof(f85,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl4_4
  <=> sK0 = k2_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f74,plain,
    ( k1_xboole_0 != sK0
    | spl4_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f226,plain,
    ( ~ spl4_1
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f49,f88,f68])).

fof(f49,plain,
    ( sK0 != k2_tarski(sK2,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f22,f27])).

fof(f22,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f224,plain,
    ( spl4_3
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f223,f68,f79])).

fof(f223,plain,
    ( r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ spl4_1 ),
    inference(trivial_inequality_removal,[],[f222])).

fof(f222,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ spl4_1 ),
    inference(superposition,[],[f33,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f221,plain,
    ( ~ spl4_15
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f220,f84,f200])).

fof(f200,plain,
    ( spl4_15
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f220,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK0)
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f219,f86])).

fof(f86,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f219,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f218])).

fof(f218,plain,
    ( sK0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f23,f86])).

fof(f23,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f203,plain,
    ( spl4_15
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f174,f84,f68,f200])).

fof(f174,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK0)
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(forward_demodulation,[],[f69,f86])).

fof(f173,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | r1_tarski(sK0,k2_tarski(sK1,sK2))
    | ~ r1_tarski(sK0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f172,plain,
    ( spl4_11
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f163,f84,f169])).

fof(f169,plain,
    ( spl4_11
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f163,plain,
    ( r1_tarski(sK0,sK0)
    | ~ spl4_4 ),
    inference(superposition,[],[f63,f86])).

fof(f63,plain,(
    ! [X2,X1] : r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2)) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f115,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl4_8 ),
    inference(unit_resulting_resolution,[],[f26,f106,f33])).

fof(f106,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2))
    | spl4_8 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_8
  <=> r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f107,plain,
    ( ~ spl4_8
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f96,f79,f72,f104])).

fof(f96,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2))
    | ~ spl4_2
    | spl4_3 ),
    inference(backward_demodulation,[],[f81,f73])).

fof(f73,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f95,plain,
    ( spl4_1
    | spl4_4
    | spl4_5
    | spl4_6
    | spl4_2 ),
    inference(avatar_split_clause,[],[f48,f72,f92,f88,f84,f68])).

fof(f48,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k2_tarski(sK1,sK1)
    | sK0 = k2_tarski(sK2,sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(definition_unfolding,[],[f24,f27,f27])).

fof(f24,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | sK0 = k1_tarski(sK2)
    | sK0 = k2_tarski(sK1,sK2)
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f77,f68,f79])).

fof(f77,plain,
    ( ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | spl4_1 ),
    inference(trivial_inequality_removal,[],[f76])).

fof(f76,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_tarski(sK0,k2_tarski(sK1,sK2))
    | spl4_1 ),
    inference(superposition,[],[f70,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f70,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f75,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f20,f72,f68])).

fof(f20,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:38:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.48  % (13622)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.19/0.49  % (13629)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.19/0.49  % (13629)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f281,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(avatar_sat_refutation,[],[f75,f82,f95,f107,f115,f172,f173,f203,f221,f224,f226,f228,f229,f254,f280])).
% 0.19/0.50  fof(f280,plain,(
% 0.19/0.50    spl4_3 | ~spl4_5),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f275])).
% 0.19/0.50  fof(f275,plain,(
% 0.19/0.50    $false | (spl4_3 | ~spl4_5)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f81,f257])).
% 0.19/0.50  fof(f257,plain,(
% 0.19/0.50    ( ! [X1] : (r1_tarski(sK0,k2_tarski(X1,sK2))) ) | ~spl4_5),
% 0.19/0.50    inference(superposition,[],[f64,f90])).
% 0.19/0.50  fof(f90,plain,(
% 0.19/0.50    sK0 = k2_tarski(sK2,sK2) | ~spl4_5),
% 0.19/0.50    inference(avatar_component_clause,[],[f88])).
% 0.19/0.50  fof(f88,plain,(
% 0.19/0.50    spl4_5 <=> sK0 = k2_tarski(sK2,sK2)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.19/0.50  fof(f64,plain,(
% 0.19/0.50    ( ! [X2,X1] : (r1_tarski(k2_tarski(X2,X2),k2_tarski(X1,X2))) )),
% 0.19/0.50    inference(equality_resolution,[],[f55])).
% 0.19/0.50  fof(f55,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k2_tarski(X2,X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.19/0.50    inference(definition_unfolding,[],[f46,f27])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,axiom,(
% 0.19/0.50    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k1_tarski(X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,axiom,(
% 0.19/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 0.19/0.50  fof(f81,plain,(
% 0.19/0.50    ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | spl4_3),
% 0.19/0.50    inference(avatar_component_clause,[],[f79])).
% 0.19/0.50  fof(f79,plain,(
% 0.19/0.50    spl4_3 <=> r1_tarski(sK0,k2_tarski(sK1,sK2))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.19/0.50  fof(f254,plain,(
% 0.19/0.50    spl4_3 | ~spl4_6),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f249])).
% 0.19/0.50  fof(f249,plain,(
% 0.19/0.50    $false | (spl4_3 | ~spl4_6)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f81,f232])).
% 0.19/0.50  fof(f232,plain,(
% 0.19/0.50    ( ! [X0] : (r1_tarski(sK0,k2_tarski(sK1,X0))) ) | ~spl4_6),
% 0.19/0.50    inference(superposition,[],[f65,f94])).
% 0.19/0.50  fof(f94,plain,(
% 0.19/0.50    sK0 = k2_tarski(sK1,sK1) | ~spl4_6),
% 0.19/0.50    inference(avatar_component_clause,[],[f92])).
% 0.19/0.50  fof(f92,plain,(
% 0.19/0.50    spl4_6 <=> sK0 = k2_tarski(sK1,sK1)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.19/0.50  fof(f65,plain,(
% 0.19/0.50    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X1),k2_tarski(X1,X2))) )),
% 0.19/0.50    inference(equality_resolution,[],[f56])).
% 0.19/0.50  fof(f56,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k2_tarski(X1,X1) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.19/0.50    inference(definition_unfolding,[],[f45,f27])).
% 0.19/0.50  fof(f45,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k1_tarski(X1) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  fof(f229,plain,(
% 0.19/0.50    ~spl4_1 | ~spl4_6),
% 0.19/0.50    inference(avatar_split_clause,[],[f50,f92,f68])).
% 0.19/0.50  fof(f68,plain,(
% 0.19/0.50    spl4_1 <=> k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.50  fof(f50,plain,(
% 0.19/0.50    sK0 != k2_tarski(sK1,sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.19/0.50    inference(definition_unfolding,[],[f21,f27])).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,negated_conjecture,(
% 0.19/0.50    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.19/0.50    inference(negated_conjecture,[],[f13])).
% 0.19/0.50  fof(f13,conjecture,(
% 0.19/0.50    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 0.19/0.50  fof(f228,plain,(
% 0.19/0.50    spl4_2 | ~spl4_3 | spl4_4 | spl4_5 | spl4_6),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f227])).
% 0.19/0.50  fof(f227,plain,(
% 0.19/0.50    $false | (spl4_2 | ~spl4_3 | spl4_4 | spl4_5 | spl4_6)),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f74,f85,f80,f93,f89,f57])).
% 0.19/0.50  fof(f57,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_tarski(X1,X2)) | k2_tarski(X1,X1) = X0 | k2_tarski(X2,X2) = X0 | k2_tarski(X1,X2) = X0 | k1_xboole_0 = X0) )),
% 0.19/0.50    inference(definition_unfolding,[],[f43,f27,f27])).
% 0.19/0.50  fof(f43,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | k1_tarski(X1) = X0 | k1_tarski(X2) = X0 | k2_tarski(X1,X2) = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  fof(f89,plain,(
% 0.19/0.50    sK0 != k2_tarski(sK2,sK2) | spl4_5),
% 0.19/0.50    inference(avatar_component_clause,[],[f88])).
% 0.19/0.50  fof(f93,plain,(
% 0.19/0.50    sK0 != k2_tarski(sK1,sK1) | spl4_6),
% 0.19/0.50    inference(avatar_component_clause,[],[f92])).
% 0.19/0.50  fof(f80,plain,(
% 0.19/0.50    r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~spl4_3),
% 0.19/0.50    inference(avatar_component_clause,[],[f79])).
% 0.19/0.50  fof(f85,plain,(
% 0.19/0.50    sK0 != k2_tarski(sK1,sK2) | spl4_4),
% 0.19/0.50    inference(avatar_component_clause,[],[f84])).
% 0.19/0.50  fof(f84,plain,(
% 0.19/0.50    spl4_4 <=> sK0 = k2_tarski(sK1,sK2)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.19/0.50  fof(f74,plain,(
% 0.19/0.50    k1_xboole_0 != sK0 | spl4_2),
% 0.19/0.50    inference(avatar_component_clause,[],[f72])).
% 0.19/0.50  fof(f72,plain,(
% 0.19/0.50    spl4_2 <=> k1_xboole_0 = sK0),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.50  fof(f226,plain,(
% 0.19/0.50    ~spl4_1 | ~spl4_5),
% 0.19/0.50    inference(avatar_split_clause,[],[f49,f88,f68])).
% 0.19/0.50  fof(f49,plain,(
% 0.19/0.50    sK0 != k2_tarski(sK2,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.19/0.50    inference(definition_unfolding,[],[f22,f27])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  fof(f224,plain,(
% 0.19/0.50    spl4_3 | ~spl4_1),
% 0.19/0.50    inference(avatar_split_clause,[],[f223,f68,f79])).
% 0.19/0.50  fof(f223,plain,(
% 0.19/0.50    r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~spl4_1),
% 0.19/0.50    inference(trivial_inequality_removal,[],[f222])).
% 0.19/0.50  fof(f222,plain,(
% 0.19/0.50    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~spl4_1),
% 0.19/0.50    inference(superposition,[],[f33,f69])).
% 0.19/0.50  fof(f69,plain,(
% 0.19/0.50    k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | ~spl4_1),
% 0.19/0.50    inference(avatar_component_clause,[],[f68])).
% 0.19/0.50  fof(f33,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.19/0.50  fof(f221,plain,(
% 0.19/0.50    ~spl4_15 | ~spl4_4),
% 0.19/0.50    inference(avatar_split_clause,[],[f220,f84,f200])).
% 0.19/0.50  fof(f200,plain,(
% 0.19/0.50    spl4_15 <=> k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.19/0.50  fof(f220,plain,(
% 0.19/0.50    k1_xboole_0 != k4_xboole_0(sK0,sK0) | ~spl4_4),
% 0.19/0.50    inference(forward_demodulation,[],[f219,f86])).
% 0.19/0.50  fof(f86,plain,(
% 0.19/0.50    sK0 = k2_tarski(sK1,sK2) | ~spl4_4),
% 0.19/0.50    inference(avatar_component_clause,[],[f84])).
% 0.19/0.50  fof(f219,plain,(
% 0.19/0.50    k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | ~spl4_4),
% 0.19/0.50    inference(trivial_inequality_removal,[],[f218])).
% 0.19/0.50  fof(f218,plain,(
% 0.19/0.50    sK0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | ~spl4_4),
% 0.19/0.50    inference(forward_demodulation,[],[f23,f86])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  fof(f203,plain,(
% 0.19/0.50    spl4_15 | ~spl4_1 | ~spl4_4),
% 0.19/0.50    inference(avatar_split_clause,[],[f174,f84,f68,f200])).
% 0.19/0.50  fof(f174,plain,(
% 0.19/0.50    k1_xboole_0 = k4_xboole_0(sK0,sK0) | (~spl4_1 | ~spl4_4)),
% 0.19/0.50    inference(forward_demodulation,[],[f69,f86])).
% 0.19/0.50  fof(f173,plain,(
% 0.19/0.50    sK0 != k2_tarski(sK1,sK2) | r1_tarski(sK0,k2_tarski(sK1,sK2)) | ~r1_tarski(sK0,sK0)),
% 0.19/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.50  fof(f172,plain,(
% 0.19/0.50    spl4_11 | ~spl4_4),
% 0.19/0.50    inference(avatar_split_clause,[],[f163,f84,f169])).
% 0.19/0.50  fof(f169,plain,(
% 0.19/0.50    spl4_11 <=> r1_tarski(sK0,sK0)),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.19/0.50  fof(f163,plain,(
% 0.19/0.50    r1_tarski(sK0,sK0) | ~spl4_4),
% 0.19/0.50    inference(superposition,[],[f63,f86])).
% 0.19/0.50  fof(f63,plain,(
% 0.19/0.50    ( ! [X2,X1] : (r1_tarski(k2_tarski(X1,X2),k2_tarski(X1,X2))) )),
% 0.19/0.50    inference(equality_resolution,[],[f47])).
% 0.19/0.50  fof(f47,plain,(
% 0.19/0.50    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f19])).
% 0.19/0.50  fof(f115,plain,(
% 0.19/0.50    spl4_8),
% 0.19/0.50    inference(avatar_contradiction_clause,[],[f109])).
% 0.19/0.50  fof(f109,plain,(
% 0.19/0.50    $false | spl4_8),
% 0.19/0.50    inference(unit_resulting_resolution,[],[f26,f106,f33])).
% 0.19/0.50  fof(f106,plain,(
% 0.19/0.50    ~r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2)) | spl4_8),
% 0.19/0.50    inference(avatar_component_clause,[],[f104])).
% 0.19/0.50  fof(f104,plain,(
% 0.19/0.50    spl4_8 <=> r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2))),
% 0.19/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,axiom,(
% 0.19/0.50    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.19/0.50  fof(f107,plain,(
% 0.19/0.50    ~spl4_8 | ~spl4_2 | spl4_3),
% 0.19/0.50    inference(avatar_split_clause,[],[f96,f79,f72,f104])).
% 0.19/0.50  fof(f96,plain,(
% 0.19/0.50    ~r1_tarski(k1_xboole_0,k2_tarski(sK1,sK2)) | (~spl4_2 | spl4_3)),
% 0.19/0.50    inference(backward_demodulation,[],[f81,f73])).
% 0.19/0.50  fof(f73,plain,(
% 0.19/0.50    k1_xboole_0 = sK0 | ~spl4_2),
% 0.19/0.50    inference(avatar_component_clause,[],[f72])).
% 0.19/0.50  fof(f95,plain,(
% 0.19/0.50    spl4_1 | spl4_4 | spl4_5 | spl4_6 | spl4_2),
% 0.19/0.50    inference(avatar_split_clause,[],[f48,f72,f92,f88,f84,f68])).
% 0.19/0.50  fof(f48,plain,(
% 0.19/0.50    k1_xboole_0 = sK0 | sK0 = k2_tarski(sK1,sK1) | sK0 = k2_tarski(sK2,sK2) | sK0 = k2_tarski(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.19/0.50    inference(definition_unfolding,[],[f24,f27,f27])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | sK0 = k1_tarski(sK2) | sK0 = k2_tarski(sK1,sK2) | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  fof(f82,plain,(
% 0.19/0.50    ~spl4_3 | spl4_1),
% 0.19/0.50    inference(avatar_split_clause,[],[f77,f68,f79])).
% 0.19/0.50  fof(f77,plain,(
% 0.19/0.50    ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | spl4_1),
% 0.19/0.50    inference(trivial_inequality_removal,[],[f76])).
% 0.19/0.50  fof(f76,plain,(
% 0.19/0.50    k1_xboole_0 != k1_xboole_0 | ~r1_tarski(sK0,k2_tarski(sK1,sK2)) | spl4_1),
% 0.19/0.50    inference(superposition,[],[f70,f32])).
% 0.19/0.50  fof(f32,plain,(
% 0.19/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f3])).
% 0.19/0.50  fof(f70,plain,(
% 0.19/0.50    k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) | spl4_1),
% 0.19/0.50    inference(avatar_component_clause,[],[f68])).
% 0.19/0.50  fof(f75,plain,(
% 0.19/0.50    ~spl4_1 | ~spl4_2),
% 0.19/0.50    inference(avatar_split_clause,[],[f20,f72,f68])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 0.19/0.50    inference(cnf_transformation,[],[f16])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (13629)------------------------------
% 0.19/0.50  % (13629)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (13629)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (13629)Memory used [KB]: 10874
% 0.19/0.50  % (13629)Time elapsed: 0.090 s
% 0.19/0.50  % (13629)------------------------------
% 0.19/0.50  % (13629)------------------------------
% 0.19/0.50  % (13600)Success in time 0.15 s
%------------------------------------------------------------------------------
