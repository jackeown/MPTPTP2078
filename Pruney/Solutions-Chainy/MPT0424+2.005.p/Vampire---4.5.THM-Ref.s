%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:30 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 140 expanded)
%              Number of leaves         :   25 (  63 expanded)
%              Depth                    :    7
%              Number of atoms          :  218 ( 348 expanded)
%              Number of equality atoms :   35 (  55 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f68,f69,f73,f81,f127,f134,f142,f149,f194,f245,f254,f281])).

fof(f281,plain,
    ( spl3_1
    | ~ spl3_8
    | ~ spl3_39 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | spl3_1
    | ~ spl3_8
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f272,f36])).

fof(f36,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl3_1
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f272,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_8
    | ~ spl3_39 ),
    inference(trivial_inequality_removal,[],[f271])).

fof(f271,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK2,sK1)
    | ~ spl3_8
    | ~ spl3_39 ),
    inference(superposition,[],[f66,f253])).

fof(f253,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl3_39
  <=> k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f66,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f254,plain,
    ( spl3_39
    | ~ spl3_5
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f246,f242,f53,f251])).

fof(f53,plain,
    ( spl3_5
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f242,plain,
    ( spl3_38
  <=> r1_tarski(k4_xboole_0(sK2,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f246,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK1)
    | ~ spl3_5
    | ~ spl3_38 ),
    inference(resolution,[],[f244,f54])).

fof(f54,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f244,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),k1_xboole_0)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f242])).

fof(f245,plain,
    ( spl3_38
    | ~ spl3_21
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f223,f192,f146,f242])).

fof(f146,plain,
    ( spl3_21
  <=> k1_xboole_0 = k4_xboole_0(sK2,k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f192,plain,
    ( spl3_27
  <=> ! [X0] : r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k3_tarski(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f223,plain,
    ( r1_tarski(k4_xboole_0(sK2,sK1),k1_xboole_0)
    | ~ spl3_21
    | ~ spl3_27 ),
    inference(superposition,[],[f193,f148])).

fof(f148,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k3_tarski(sK0))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f146])).

fof(f193,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k3_tarski(sK0)))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f192])).

fof(f194,plain,
    ( spl3_27
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f184,f79,f44,f192])).

fof(f44,plain,
    ( spl3_3
  <=> r1_tarski(k3_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f79,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f184,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k3_tarski(sK0)))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(resolution,[],[f80,f46])).

fof(f46,plain,
    ( r1_tarski(k3_tarski(sK0),sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f80,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f149,plain,
    ( spl3_21
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f143,f139,f61,f146])).

fof(f61,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f139,plain,
    ( spl3_20
  <=> r1_tarski(sK2,k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f143,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k3_tarski(sK0))
    | ~ spl3_7
    | ~ spl3_20 ),
    inference(resolution,[],[f141,f62])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f141,plain,
    ( r1_tarski(sK2,k3_tarski(sK0))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f139])).

fof(f142,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f137,f131,f57,f49,f139])).

fof(f49,plain,
    ( spl3_4
  <=> ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f131,plain,
    ( spl3_19
  <=> r1_tarski(k1_tarski(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f137,plain,
    ( r1_tarski(sK2,k3_tarski(sK0))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(forward_demodulation,[],[f136,f50])).

fof(f50,plain,
    ( ! [X0] : k3_tarski(k1_tarski(X0)) = X0
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f49])).

fof(f136,plain,
    ( r1_tarski(k3_tarski(k1_tarski(sK2)),k3_tarski(sK0))
    | ~ spl3_6
    | ~ spl3_19 ),
    inference(resolution,[],[f133,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k3_tarski(X0),k3_tarski(X1)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f133,plain,
    ( r1_tarski(k1_tarski(sK2),sK0)
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f131])).

fof(f134,plain,
    ( spl3_19
    | ~ spl3_8
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f129,f124,f65,f131])).

fof(f124,plain,
    ( spl3_18
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f129,plain,
    ( r1_tarski(k1_tarski(sK2),sK0)
    | ~ spl3_8
    | ~ spl3_18 ),
    inference(trivial_inequality_removal,[],[f128])).

fof(f128,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(k1_tarski(sK2),sK0)
    | ~ spl3_8
    | ~ spl3_18 ),
    inference(superposition,[],[f66,f126])).

fof(f126,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),sK0)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f124])).

fof(f127,plain,
    ( spl3_18
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f122,f71,f39,f124])).

fof(f39,plain,
    ( spl3_2
  <=> r2_hidden(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f71,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f122,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),sK0)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f72,f41])).

fof(f41,plain,
    ( r2_hidden(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f71])).

fof(f81,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f32,f79])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f73,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f31,f71])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

fof(f69,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f28,f65])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f68,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f29,f61])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f59,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f25,f57])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),k3_tarski(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

fof(f55,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f51,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f23,f49])).

fof(f23,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f47,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    r1_tarski(k3_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(sK2,sK1)
    & r2_hidden(sK2,sK0)
    & r1_tarski(k3_tarski(sK0),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X2,X1)
        & r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
   => ( ~ r1_tarski(sK2,sK1)
      & r2_hidden(sK2,sK0)
      & r1_tarski(k3_tarski(sK0),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,X1)
      & r2_hidden(X2,X0)
      & r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,X1)
      & r2_hidden(X2,X0)
      & r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X0)
          & r1_tarski(k3_tarski(X0),X1) )
       => r1_tarski(X2,X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f34])).

fof(f22,plain,(
    ~ r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:36:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (6898)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.42  % (6899)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.42  % (6899)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f282,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(avatar_sat_refutation,[],[f37,f42,f47,f51,f55,f59,f68,f69,f73,f81,f127,f134,f142,f149,f194,f245,f254,f281])).
% 0.20/0.42  fof(f281,plain,(
% 0.20/0.42    spl3_1 | ~spl3_8 | ~spl3_39),
% 0.20/0.42    inference(avatar_contradiction_clause,[],[f280])).
% 0.20/0.42  fof(f280,plain,(
% 0.20/0.42    $false | (spl3_1 | ~spl3_8 | ~spl3_39)),
% 0.20/0.42    inference(subsumption_resolution,[],[f272,f36])).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    ~r1_tarski(sK2,sK1) | spl3_1),
% 0.20/0.42    inference(avatar_component_clause,[],[f34])).
% 0.20/0.42  fof(f34,plain,(
% 0.20/0.42    spl3_1 <=> r1_tarski(sK2,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.42  fof(f272,plain,(
% 0.20/0.42    r1_tarski(sK2,sK1) | (~spl3_8 | ~spl3_39)),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f271])).
% 0.20/0.42  fof(f271,plain,(
% 0.20/0.42    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK2,sK1) | (~spl3_8 | ~spl3_39)),
% 0.20/0.42    inference(superposition,[],[f66,f253])).
% 0.20/0.42  fof(f253,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK2,sK1) | ~spl3_39),
% 0.20/0.42    inference(avatar_component_clause,[],[f251])).
% 0.20/0.42  fof(f251,plain,(
% 0.20/0.42    spl3_39 <=> k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.42  fof(f66,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.20/0.42    inference(avatar_component_clause,[],[f65])).
% 0.20/0.42  fof(f65,plain,(
% 0.20/0.42    spl3_8 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.42  fof(f254,plain,(
% 0.20/0.42    spl3_39 | ~spl3_5 | ~spl3_38),
% 0.20/0.42    inference(avatar_split_clause,[],[f246,f242,f53,f251])).
% 0.20/0.42  fof(f53,plain,(
% 0.20/0.42    spl3_5 <=> ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.42  fof(f242,plain,(
% 0.20/0.42    spl3_38 <=> r1_tarski(k4_xboole_0(sK2,sK1),k1_xboole_0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.20/0.42  fof(f246,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK2,sK1) | (~spl3_5 | ~spl3_38)),
% 0.20/0.42    inference(resolution,[],[f244,f54])).
% 0.20/0.42  fof(f54,plain,(
% 0.20/0.42    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl3_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f53])).
% 0.20/0.42  fof(f244,plain,(
% 0.20/0.42    r1_tarski(k4_xboole_0(sK2,sK1),k1_xboole_0) | ~spl3_38),
% 0.20/0.42    inference(avatar_component_clause,[],[f242])).
% 0.20/0.42  fof(f245,plain,(
% 0.20/0.42    spl3_38 | ~spl3_21 | ~spl3_27),
% 0.20/0.42    inference(avatar_split_clause,[],[f223,f192,f146,f242])).
% 0.20/0.42  fof(f146,plain,(
% 0.20/0.42    spl3_21 <=> k1_xboole_0 = k4_xboole_0(sK2,k3_tarski(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.42  fof(f192,plain,(
% 0.20/0.42    spl3_27 <=> ! [X0] : r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k3_tarski(sK0)))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.42  fof(f223,plain,(
% 0.20/0.42    r1_tarski(k4_xboole_0(sK2,sK1),k1_xboole_0) | (~spl3_21 | ~spl3_27)),
% 0.20/0.42    inference(superposition,[],[f193,f148])).
% 0.20/0.42  fof(f148,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK2,k3_tarski(sK0)) | ~spl3_21),
% 0.20/0.42    inference(avatar_component_clause,[],[f146])).
% 0.20/0.42  fof(f193,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k3_tarski(sK0)))) ) | ~spl3_27),
% 0.20/0.42    inference(avatar_component_clause,[],[f192])).
% 0.20/0.42  fof(f194,plain,(
% 0.20/0.42    spl3_27 | ~spl3_3 | ~spl3_11),
% 0.20/0.42    inference(avatar_split_clause,[],[f184,f79,f44,f192])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    spl3_3 <=> r1_tarski(k3_tarski(sK0),sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.42  fof(f79,plain,(
% 0.20/0.42    spl3_11 <=> ! [X1,X0,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.42  fof(f184,plain,(
% 0.20/0.42    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,k3_tarski(sK0)))) ) | (~spl3_3 | ~spl3_11)),
% 0.20/0.42    inference(resolution,[],[f80,f46])).
% 0.20/0.42  fof(f46,plain,(
% 0.20/0.42    r1_tarski(k3_tarski(sK0),sK1) | ~spl3_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f44])).
% 0.20/0.42  fof(f80,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) ) | ~spl3_11),
% 0.20/0.42    inference(avatar_component_clause,[],[f79])).
% 0.20/0.42  fof(f149,plain,(
% 0.20/0.42    spl3_21 | ~spl3_7 | ~spl3_20),
% 0.20/0.42    inference(avatar_split_clause,[],[f143,f139,f61,f146])).
% 0.20/0.42  fof(f61,plain,(
% 0.20/0.42    spl3_7 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.42  fof(f139,plain,(
% 0.20/0.42    spl3_20 <=> r1_tarski(sK2,k3_tarski(sK0))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.42  fof(f143,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK2,k3_tarski(sK0)) | (~spl3_7 | ~spl3_20)),
% 0.20/0.42    inference(resolution,[],[f141,f62])).
% 0.20/0.42  fof(f62,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_7),
% 0.20/0.42    inference(avatar_component_clause,[],[f61])).
% 0.20/0.42  fof(f141,plain,(
% 0.20/0.42    r1_tarski(sK2,k3_tarski(sK0)) | ~spl3_20),
% 0.20/0.42    inference(avatar_component_clause,[],[f139])).
% 0.20/0.42  fof(f142,plain,(
% 0.20/0.42    spl3_20 | ~spl3_4 | ~spl3_6 | ~spl3_19),
% 0.20/0.42    inference(avatar_split_clause,[],[f137,f131,f57,f49,f139])).
% 0.20/0.42  fof(f49,plain,(
% 0.20/0.42    spl3_4 <=> ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.42  fof(f57,plain,(
% 0.20/0.42    spl3_6 <=> ! [X1,X0] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.42  fof(f131,plain,(
% 0.20/0.42    spl3_19 <=> r1_tarski(k1_tarski(sK2),sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.42  fof(f137,plain,(
% 0.20/0.42    r1_tarski(sK2,k3_tarski(sK0)) | (~spl3_4 | ~spl3_6 | ~spl3_19)),
% 0.20/0.42    inference(forward_demodulation,[],[f136,f50])).
% 0.20/0.42  fof(f50,plain,(
% 0.20/0.42    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) ) | ~spl3_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f49])).
% 0.20/0.42  fof(f136,plain,(
% 0.20/0.42    r1_tarski(k3_tarski(k1_tarski(sK2)),k3_tarski(sK0)) | (~spl3_6 | ~spl3_19)),
% 0.20/0.42    inference(resolution,[],[f133,f58])).
% 0.20/0.42  fof(f58,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_tarski(X0),k3_tarski(X1))) ) | ~spl3_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f57])).
% 0.20/0.42  fof(f133,plain,(
% 0.20/0.42    r1_tarski(k1_tarski(sK2),sK0) | ~spl3_19),
% 0.20/0.42    inference(avatar_component_clause,[],[f131])).
% 0.20/0.42  fof(f134,plain,(
% 0.20/0.42    spl3_19 | ~spl3_8 | ~spl3_18),
% 0.20/0.42    inference(avatar_split_clause,[],[f129,f124,f65,f131])).
% 0.20/0.42  fof(f124,plain,(
% 0.20/0.42    spl3_18 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.42  fof(f129,plain,(
% 0.20/0.42    r1_tarski(k1_tarski(sK2),sK0) | (~spl3_8 | ~spl3_18)),
% 0.20/0.42    inference(trivial_inequality_removal,[],[f128])).
% 0.20/0.42  fof(f128,plain,(
% 0.20/0.42    k1_xboole_0 != k1_xboole_0 | r1_tarski(k1_tarski(sK2),sK0) | (~spl3_8 | ~spl3_18)),
% 0.20/0.42    inference(superposition,[],[f66,f126])).
% 0.20/0.42  fof(f126,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),sK0) | ~spl3_18),
% 0.20/0.42    inference(avatar_component_clause,[],[f124])).
% 0.20/0.42  fof(f127,plain,(
% 0.20/0.42    spl3_18 | ~spl3_2 | ~spl3_9),
% 0.20/0.42    inference(avatar_split_clause,[],[f122,f71,f39,f124])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    spl3_2 <=> r2_hidden(sK2,sK0)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl3_9 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    k1_xboole_0 = k4_xboole_0(k1_tarski(sK2),sK0) | (~spl3_2 | ~spl3_9)),
% 0.20/0.43    inference(resolution,[],[f72,f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    r2_hidden(sK2,sK0) | ~spl3_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f39])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1)) ) | ~spl3_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f71])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    spl3_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f32,f79])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    spl3_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f31,f71])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1)))),
% 0.20/0.43    inference(nnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    spl3_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f65])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.43    inference(nnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    spl3_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f29,f61])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    spl3_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f57])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_tarski(k3_tarski(X0),k3_tarski(X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    spl3_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f53])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    spl3_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f49])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    spl3_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f20,f44])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    r1_tarski(k3_tarski(sK0),sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ~r1_tarski(sK2,sK1) & r2_hidden(sK2,sK0) & r1_tarski(k3_tarski(sK0),sK1)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => (~r1_tarski(sK2,sK1) & r2_hidden(sK2,sK0) & r1_tarski(k3_tarski(sK0),sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1))),
% 0.20/0.43    inference(flattening,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (~r1_tarski(X2,X1) & (r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.20/0.43    inference(negated_conjecture,[],[f8])).
% 0.20/0.43  fof(f8,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    spl3_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f21,f39])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    r2_hidden(sK2,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ~spl3_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f22,f34])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ~r1_tarski(sK2,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f16])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (6899)------------------------------
% 0.20/0.43  % (6899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (6899)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (6899)Memory used [KB]: 10746
% 0.20/0.43  % (6899)Time elapsed: 0.009 s
% 0.20/0.43  % (6899)------------------------------
% 0.20/0.43  % (6899)------------------------------
% 0.20/0.43  % (6893)Success in time 0.066 s
%------------------------------------------------------------------------------
