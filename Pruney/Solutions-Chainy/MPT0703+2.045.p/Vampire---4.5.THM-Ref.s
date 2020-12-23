%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:24 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 110 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   13
%              Number of atoms          :  156 ( 358 expanded)
%              Number of equality atoms :   36 (  46 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f326,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f273,f275,f277,f294,f319,f322,f325])).

fof(f325,plain,(
    ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f37,f309])).

fof(f309,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl3_11
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f37,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f32,f25])).

fof(f25,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_tarski(sK0,k2_relat_1(sK2))
    & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_tarski(X0,k2_relat_1(X2))
        & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_tarski(sK0,k2_relat_1(sK2))
      & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_tarski(X0,k2_relat_1(X2))
      & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r1_tarski(X0,k2_relat_1(X2))
            & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
         => r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r1_tarski(X0,k2_relat_1(X2))
          & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
       => r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f322,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f320])).

fof(f320,plain,
    ( $false
    | spl3_13 ),
    inference(resolution,[],[f318,f27])).

fof(f27,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f318,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f316])).

fof(f316,plain,
    ( spl3_13
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f319,plain,
    ( spl3_11
    | ~ spl3_13
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f302,f292,f270,f316,f307])).

fof(f270,plain,
    ( spl3_7
  <=> sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f292,plain,
    ( spl3_10
  <=> ! [X1,X0] : k9_relat_1(sK2,k3_xboole_0(X0,k10_relat_1(sK2,X1))) = k3_xboole_0(k9_relat_1(sK2,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f302,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK1),sK0)
    | k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(superposition,[],[f109,f300])).

fof(f300,plain,
    ( sK0 = k3_xboole_0(sK0,sK1)
    | ~ spl3_7
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f299,f272])).

fof(f272,plain,
    ( sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f270])).

fof(f299,plain,
    ( k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1)
    | ~ spl3_10 ),
    inference(superposition,[],[f293,f117])).

fof(f117,plain,(
    k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f105,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f105,plain,(
    k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k4_xboole_0(k10_relat_1(sK2,sK0),k1_xboole_0) ),
    inference(superposition,[],[f29,f42])).

fof(f42,plain,(
    k1_xboole_0 = k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(resolution,[],[f33,f23])).

fof(f23,plain,(
    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f293,plain,
    ( ! [X0,X1] : k9_relat_1(sK2,k3_xboole_0(X0,k10_relat_1(sK2,X1))) = k3_xboole_0(k9_relat_1(sK2,X0),X1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f292])).

fof(f109,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3))
      | k1_xboole_0 = k4_xboole_0(X2,X3) ) ),
    inference(superposition,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f294,plain,
    ( ~ spl3_5
    | spl3_10 ),
    inference(avatar_split_clause,[],[f290,f292,f262])).

fof(f262,plain,
    ( spl3_5
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f290,plain,(
    ! [X0,X1] :
      ( k9_relat_1(sK2,k3_xboole_0(X0,k10_relat_1(sK2,X1))) = k3_xboole_0(k9_relat_1(sK2,X0),X1)
      | ~ v1_relat_1(sK2) ) ),
    inference(resolution,[],[f34,f22])).

fof(f22,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).

fof(f277,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f276])).

fof(f276,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f22,f268])).

fof(f268,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f275,plain,(
    spl3_5 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | spl3_5 ),
    inference(subsumption_resolution,[],[f21,f264])).

fof(f264,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f262])).

fof(f21,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f273,plain,
    ( ~ spl3_5
    | ~ spl3_6
    | spl3_7 ),
    inference(avatar_split_clause,[],[f260,f270,f266,f262])).

fof(f260,plain,
    ( sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f31,f24])).

fof(f24,plain,(
    r1_tarski(sK0,k2_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_relat_1(X1))
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.42  % (13592)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.42  % (13592)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f326,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f273,f275,f277,f294,f319,f322,f325])).
% 0.19/0.42  fof(f325,plain,(
% 0.19/0.42    ~spl3_11),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f323])).
% 0.19/0.42  fof(f323,plain,(
% 0.19/0.42    $false | ~spl3_11),
% 0.19/0.42    inference(subsumption_resolution,[],[f37,f309])).
% 0.19/0.42  fof(f309,plain,(
% 0.19/0.42    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_11),
% 0.19/0.42    inference(avatar_component_clause,[],[f307])).
% 0.19/0.42  fof(f307,plain,(
% 0.19/0.42    spl3_11 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    k1_xboole_0 != k4_xboole_0(sK0,sK1)),
% 0.19/0.42    inference(resolution,[],[f32,f25])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    ~r1_tarski(sK0,sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    ~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.19/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f18])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(sK0,sK1) & r1_tarski(sK0,k2_relat_1(sK2)) & r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.19/0.42    introduced(choice_axiom,[])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.19/0.42    inference(flattening,[],[f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ? [X0,X1,X2] : ((~r1_tarski(X0,X1) & (r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.19/0.42    inference(ennf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.19/0.42    inference(negated_conjecture,[],[f9])).
% 0.19/0.42  fof(f9,conjecture,(
% 0.19/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r1_tarski(X0,k2_relat_1(X2)) & r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) => r1_tarski(X0,X1)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t158_funct_1)).
% 0.19/0.42  fof(f32,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f20])).
% 0.19/0.42  fof(f20,plain,(
% 0.19/0.42    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.19/0.42    inference(nnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.19/0.42  fof(f322,plain,(
% 0.19/0.42    spl3_13),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f320])).
% 0.19/0.42  fof(f320,plain,(
% 0.19/0.42    $false | spl3_13),
% 0.19/0.42    inference(resolution,[],[f318,f27])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.19/0.42  fof(f318,plain,(
% 0.19/0.42    ~r1_tarski(k4_xboole_0(sK0,sK1),sK0) | spl3_13),
% 0.19/0.42    inference(avatar_component_clause,[],[f316])).
% 0.19/0.42  fof(f316,plain,(
% 0.19/0.42    spl3_13 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.19/0.42  fof(f319,plain,(
% 0.19/0.42    spl3_11 | ~spl3_13 | ~spl3_7 | ~spl3_10),
% 0.19/0.42    inference(avatar_split_clause,[],[f302,f292,f270,f316,f307])).
% 0.19/0.42  fof(f270,plain,(
% 0.19/0.42    spl3_7 <=> sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0))),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.42  fof(f292,plain,(
% 0.19/0.42    spl3_10 <=> ! [X1,X0] : k9_relat_1(sK2,k3_xboole_0(X0,k10_relat_1(sK2,X1))) = k3_xboole_0(k9_relat_1(sK2,X0),X1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.42  fof(f302,plain,(
% 0.19/0.42    ~r1_tarski(k4_xboole_0(sK0,sK1),sK0) | k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_7 | ~spl3_10)),
% 0.19/0.42    inference(superposition,[],[f109,f300])).
% 0.19/0.42  fof(f300,plain,(
% 0.19/0.42    sK0 = k3_xboole_0(sK0,sK1) | (~spl3_7 | ~spl3_10)),
% 0.19/0.42    inference(forward_demodulation,[],[f299,f272])).
% 0.19/0.42  fof(f272,plain,(
% 0.19/0.42    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | ~spl3_7),
% 0.19/0.42    inference(avatar_component_clause,[],[f270])).
% 0.19/0.42  fof(f299,plain,(
% 0.19/0.42    k9_relat_1(sK2,k10_relat_1(sK2,sK0)) = k3_xboole_0(k9_relat_1(sK2,k10_relat_1(sK2,sK0)),sK1) | ~spl3_10),
% 0.19/0.42    inference(superposition,[],[f293,f117])).
% 0.19/0.42  fof(f117,plain,(
% 0.19/0.42    k10_relat_1(sK2,sK0) = k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.19/0.42    inference(forward_demodulation,[],[f105,f26])).
% 0.19/0.42  fof(f26,plain,(
% 0.19/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.19/0.42  fof(f105,plain,(
% 0.19/0.42    k3_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) = k4_xboole_0(k10_relat_1(sK2,sK0),k1_xboole_0)),
% 0.19/0.42    inference(superposition,[],[f29,f42])).
% 0.19/0.42  fof(f42,plain,(
% 0.19/0.42    k1_xboole_0 = k4_xboole_0(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.19/0.42    inference(resolution,[],[f33,f23])).
% 0.19/0.42  fof(f23,plain,(
% 0.19/0.42    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f20])).
% 0.19/0.42  fof(f29,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.19/0.42  fof(f293,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,k10_relat_1(sK2,X1))) = k3_xboole_0(k9_relat_1(sK2,X0),X1)) ) | ~spl3_10),
% 0.19/0.42    inference(avatar_component_clause,[],[f292])).
% 0.19/0.42  fof(f109,plain,(
% 0.19/0.42    ( ! [X2,X3] : (~r1_tarski(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) | k1_xboole_0 = k4_xboole_0(X2,X3)) )),
% 0.19/0.42    inference(superposition,[],[f30,f29])).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.19/0.42    inference(cnf_transformation,[],[f13])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.19/0.42    inference(ennf_transformation,[],[f3])).
% 0.19/0.42  fof(f3,axiom,(
% 0.19/0.42    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.19/0.42  fof(f294,plain,(
% 0.19/0.42    ~spl3_5 | spl3_10),
% 0.19/0.42    inference(avatar_split_clause,[],[f290,f292,f262])).
% 0.19/0.42  fof(f262,plain,(
% 0.19/0.42    spl3_5 <=> v1_relat_1(sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.42  fof(f290,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k9_relat_1(sK2,k3_xboole_0(X0,k10_relat_1(sK2,X1))) = k3_xboole_0(k9_relat_1(sK2,X0),X1) | ~v1_relat_1(sK2)) )),
% 0.19/0.42    inference(resolution,[],[f34,f22])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    v1_funct_1(sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  fof(f34,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f17])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 0.19/0.42    inference(flattening,[],[f16])).
% 0.19/0.42  fof(f16,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 0.19/0.42    inference(ennf_transformation,[],[f8])).
% 0.19/0.42  fof(f8,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => k9_relat_1(X2,k3_xboole_0(X0,k10_relat_1(X2,X1))) = k3_xboole_0(k9_relat_1(X2,X0),X1))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_funct_1)).
% 0.19/0.42  fof(f277,plain,(
% 0.19/0.42    spl3_6),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f276])).
% 0.19/0.42  fof(f276,plain,(
% 0.19/0.42    $false | spl3_6),
% 0.19/0.42    inference(subsumption_resolution,[],[f22,f268])).
% 0.19/0.42  fof(f268,plain,(
% 0.19/0.42    ~v1_funct_1(sK2) | spl3_6),
% 0.19/0.42    inference(avatar_component_clause,[],[f266])).
% 0.19/0.42  fof(f266,plain,(
% 0.19/0.42    spl3_6 <=> v1_funct_1(sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.42  fof(f275,plain,(
% 0.19/0.42    spl3_5),
% 0.19/0.42    inference(avatar_contradiction_clause,[],[f274])).
% 0.19/0.42  fof(f274,plain,(
% 0.19/0.42    $false | spl3_5),
% 0.19/0.42    inference(subsumption_resolution,[],[f21,f264])).
% 0.19/0.42  fof(f264,plain,(
% 0.19/0.42    ~v1_relat_1(sK2) | spl3_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f262])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    v1_relat_1(sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  fof(f273,plain,(
% 0.19/0.42    ~spl3_5 | ~spl3_6 | spl3_7),
% 0.19/0.42    inference(avatar_split_clause,[],[f260,f270,f266,f262])).
% 0.19/0.42  fof(f260,plain,(
% 0.19/0.42    sK0 = k9_relat_1(sK2,k10_relat_1(sK2,sK0)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 0.19/0.42    inference(resolution,[],[f31,f24])).
% 0.19/0.42  fof(f24,plain,(
% 0.19/0.42    r1_tarski(sK0,k2_relat_1(sK2))),
% 0.19/0.42    inference(cnf_transformation,[],[f19])).
% 0.19/0.42  fof(f31,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_tarski(X0,k2_relat_1(X1)) | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f15])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.19/0.42    inference(flattening,[],[f14])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.19/0.42    inference(ennf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,axiom,(
% 0.19/0.42    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (13592)------------------------------
% 0.19/0.42  % (13592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (13592)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (13592)Memory used [KB]: 6268
% 0.19/0.42  % (13592)Time elapsed: 0.033 s
% 0.19/0.42  % (13592)------------------------------
% 0.19/0.42  % (13592)------------------------------
% 0.19/0.43  % (13575)Success in time 0.075 s
%------------------------------------------------------------------------------
