%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:07:16 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 127 expanded)
%              Number of leaves         :   22 (  59 expanded)
%              Depth                    :    7
%              Number of atoms          :  198 ( 343 expanded)
%              Number of equality atoms :   53 (  93 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f126,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f45,f49,f53,f57,f61,f65,f71,f83,f89,f93,f99,f117,f125])).

fof(f125,plain,
    ( spl3_1
    | ~ spl3_11
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | spl3_1
    | ~ spl3_11
    | ~ spl3_17 ),
    inference(trivial_inequality_removal,[],[f123])).

fof(f123,plain,
    ( k9_relat_1(sK0,sK2) != k9_relat_1(sK0,sK2)
    | spl3_1
    | ~ spl3_11
    | ~ spl3_17 ),
    inference(forward_demodulation,[],[f122,f79])).

fof(f79,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl3_11
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f122,plain,
    ( k9_relat_1(sK0,sK2) != k9_relat_1(sK0,k3_xboole_0(sK1,sK2))
    | spl3_1
    | ~ spl3_17 ),
    inference(superposition,[],[f29,f116])).

fof(f116,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(sK0,k3_xboole_0(X0,X1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_17
  <=> ! [X1,X0] : k9_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(sK0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f29,plain,
    ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_1
  <=> k9_relat_1(sK0,sK2) = k9_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f117,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f113,f97,f91,f87,f42,f115])).

fof(f42,plain,
    ( spl3_4
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f87,plain,
    ( spl3_12
  <=> ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f91,plain,
    ( spl3_13
  <=> ! [X1,X3,X2] :
        ( k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f97,plain,
    ( spl3_14
  <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f113,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(sK0,k3_xboole_0(X0,X1))
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f112,f88])).

fof(f88,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f87])).

fof(f112,plain,
    ( ! [X0,X1] : k9_relat_1(k7_relat_1(sK0,X0),X1) = k2_relat_1(k7_relat_1(sK0,k3_xboole_0(X0,X1)))
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f110,f98])).

fof(f98,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f97])).

fof(f110,plain,
    ( ! [X0,X1] : k2_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1)
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(resolution,[],[f92,f44])).

fof(f44,plain,
    ( v1_relat_1(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f92,plain,
    ( ! [X2,X3,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f91])).

fof(f99,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f94,f63,f42,f97])).

fof(f63,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f94,plain,
    ( ! [X0,X1] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(resolution,[],[f64,f44])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f93,plain,
    ( spl3_13
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f85,f55,f51,f91])).

fof(f51,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f55,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f85,plain,
    ( ! [X2,X3,X1] :
        ( k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3)
        | ~ v1_relat_1(X1) )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(resolution,[],[f56,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f89,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f84,f55,f42,f87])).

fof(f84,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(resolution,[],[f56,f44])).

fof(f83,plain,
    ( spl3_11
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f75,f68,f47,f77])).

fof(f47,plain,
    ( spl3_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f68,plain,
    ( spl3_10
  <=> sK2 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f75,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(superposition,[],[f48,f70])).

fof(f70,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f48,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f71,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f66,f59,f32,f68])).

fof(f32,plain,
    ( spl3_2
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f59,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f66,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f60,f34])).

fof(f34,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f60,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f65,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f25,f63])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

fof(f61,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f24,f59])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f57,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f53,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f49,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f45,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)
    & r1_tarski(sK2,sK1)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
            & r1_tarski(X2,X1) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X2,X1] :
          ( k9_relat_1(sK0,X2) != k9_relat_1(k7_relat_1(sK0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2,X1] :
        ( k9_relat_1(sK0,X2) != k9_relat_1(k7_relat_1(sK0,X1),X2)
        & r1_tarski(X2,X1) )
   => ( k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)
      & r1_tarski(sK2,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2)
          & r1_tarski(X2,X1) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1,X2] :
            ( r1_tarski(X2,X1)
           => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( r1_tarski(X2,X1)
         => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_2)).

fof(f35,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f32])).

fof(f19,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f30,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f20,f27])).

fof(f20,plain,(
    k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:55:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (11906)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.42  % (11905)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.43  % (11905)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f126,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f30,f35,f45,f49,f53,f57,f61,f65,f71,f83,f89,f93,f99,f117,f125])).
% 0.21/0.43  fof(f125,plain,(
% 0.21/0.43    spl3_1 | ~spl3_11 | ~spl3_17),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f124])).
% 0.21/0.43  fof(f124,plain,(
% 0.21/0.43    $false | (spl3_1 | ~spl3_11 | ~spl3_17)),
% 0.21/0.43    inference(trivial_inequality_removal,[],[f123])).
% 0.21/0.43  fof(f123,plain,(
% 0.21/0.43    k9_relat_1(sK0,sK2) != k9_relat_1(sK0,sK2) | (spl3_1 | ~spl3_11 | ~spl3_17)),
% 0.21/0.43    inference(forward_demodulation,[],[f122,f79])).
% 0.21/0.43  fof(f79,plain,(
% 0.21/0.43    sK2 = k3_xboole_0(sK1,sK2) | ~spl3_11),
% 0.21/0.43    inference(avatar_component_clause,[],[f77])).
% 0.21/0.43  fof(f77,plain,(
% 0.21/0.43    spl3_11 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.43  fof(f122,plain,(
% 0.21/0.43    k9_relat_1(sK0,sK2) != k9_relat_1(sK0,k3_xboole_0(sK1,sK2)) | (spl3_1 | ~spl3_17)),
% 0.21/0.43    inference(superposition,[],[f29,f116])).
% 0.21/0.43  fof(f116,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(sK0,k3_xboole_0(X0,X1))) ) | ~spl3_17),
% 0.21/0.43    inference(avatar_component_clause,[],[f115])).
% 0.21/0.43  fof(f115,plain,(
% 0.21/0.43    spl3_17 <=> ! [X1,X0] : k9_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(sK0,k3_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) | spl3_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f27])).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    spl3_1 <=> k9_relat_1(sK0,sK2) = k9_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.43  fof(f117,plain,(
% 0.21/0.43    spl3_17 | ~spl3_4 | ~spl3_12 | ~spl3_13 | ~spl3_14),
% 0.21/0.43    inference(avatar_split_clause,[],[f113,f97,f91,f87,f42,f115])).
% 0.21/0.43  fof(f42,plain,(
% 0.21/0.43    spl3_4 <=> v1_relat_1(sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.43  fof(f87,plain,(
% 0.21/0.43    spl3_12 <=> ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.43  fof(f91,plain,(
% 0.21/0.43    spl3_13 <=> ! [X1,X3,X2] : (k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3) | ~v1_relat_1(X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.43  fof(f97,plain,(
% 0.21/0.43    spl3_14 <=> ! [X1,X0] : k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.43  fof(f113,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK0,X0),X1) = k9_relat_1(sK0,k3_xboole_0(X0,X1))) ) | (~spl3_4 | ~spl3_12 | ~spl3_13 | ~spl3_14)),
% 0.21/0.43    inference(forward_demodulation,[],[f112,f88])).
% 0.21/0.43  fof(f88,plain,(
% 0.21/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) ) | ~spl3_12),
% 0.21/0.43    inference(avatar_component_clause,[],[f87])).
% 0.21/0.43  fof(f112,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k9_relat_1(k7_relat_1(sK0,X0),X1) = k2_relat_1(k7_relat_1(sK0,k3_xboole_0(X0,X1)))) ) | (~spl3_4 | ~spl3_13 | ~spl3_14)),
% 0.21/0.43    inference(forward_demodulation,[],[f110,f98])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1))) ) | ~spl3_14),
% 0.21/0.43    inference(avatar_component_clause,[],[f97])).
% 0.21/0.43  fof(f110,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(sK0,X0),X1)) = k9_relat_1(k7_relat_1(sK0,X0),X1)) ) | (~spl3_4 | ~spl3_13)),
% 0.21/0.43    inference(resolution,[],[f92,f44])).
% 0.21/0.43  fof(f44,plain,(
% 0.21/0.43    v1_relat_1(sK0) | ~spl3_4),
% 0.21/0.43    inference(avatar_component_clause,[],[f42])).
% 0.21/0.43  fof(f92,plain,(
% 0.21/0.43    ( ! [X2,X3,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3)) ) | ~spl3_13),
% 0.21/0.43    inference(avatar_component_clause,[],[f91])).
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    spl3_14 | ~spl3_4 | ~spl3_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f94,f63,f42,f97])).
% 0.21/0.43  fof(f63,plain,(
% 0.21/0.43    spl3_9 <=> ! [X1,X0,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k7_relat_1(k7_relat_1(sK0,X0),X1) = k7_relat_1(sK0,k3_xboole_0(X0,X1))) ) | (~spl3_4 | ~spl3_9)),
% 0.21/0.43    inference(resolution,[],[f64,f44])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1))) ) | ~spl3_9),
% 0.21/0.43    inference(avatar_component_clause,[],[f63])).
% 0.21/0.43  fof(f93,plain,(
% 0.21/0.43    spl3_13 | ~spl3_6 | ~spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f85,f55,f51,f91])).
% 0.21/0.43  fof(f51,plain,(
% 0.21/0.43    spl3_6 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.43  fof(f55,plain,(
% 0.21/0.43    spl3_7 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    ( ! [X2,X3,X1] : (k2_relat_1(k7_relat_1(k7_relat_1(X1,X2),X3)) = k9_relat_1(k7_relat_1(X1,X2),X3) | ~v1_relat_1(X1)) ) | (~spl3_6 | ~spl3_7)),
% 0.21/0.43    inference(resolution,[],[f56,f52])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f51])).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl3_7),
% 0.21/0.43    inference(avatar_component_clause,[],[f55])).
% 0.21/0.43  fof(f89,plain,(
% 0.21/0.43    spl3_12 | ~spl3_4 | ~spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f84,f55,f42,f87])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) ) | (~spl3_4 | ~spl3_7)),
% 0.21/0.43    inference(resolution,[],[f56,f44])).
% 0.21/0.43  fof(f83,plain,(
% 0.21/0.43    spl3_11 | ~spl3_5 | ~spl3_10),
% 0.21/0.43    inference(avatar_split_clause,[],[f75,f68,f47,f77])).
% 0.21/0.43  fof(f47,plain,(
% 0.21/0.43    spl3_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.43  fof(f68,plain,(
% 0.21/0.43    spl3_10 <=> sK2 = k3_xboole_0(sK2,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    sK2 = k3_xboole_0(sK1,sK2) | (~spl3_5 | ~spl3_10)),
% 0.21/0.43    inference(superposition,[],[f48,f70])).
% 0.21/0.43  fof(f70,plain,(
% 0.21/0.43    sK2 = k3_xboole_0(sK2,sK1) | ~spl3_10),
% 0.21/0.43    inference(avatar_component_clause,[],[f68])).
% 0.21/0.43  fof(f48,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f47])).
% 0.21/0.43  fof(f71,plain,(
% 0.21/0.43    spl3_10 | ~spl3_2 | ~spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f66,f59,f32,f68])).
% 0.21/0.43  fof(f32,plain,(
% 0.21/0.43    spl3_2 <=> r1_tarski(sK2,sK1)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.43  fof(f59,plain,(
% 0.21/0.43    spl3_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    sK2 = k3_xboole_0(sK2,sK1) | (~spl3_2 | ~spl3_8)),
% 0.21/0.43    inference(resolution,[],[f60,f34])).
% 0.21/0.43  fof(f34,plain,(
% 0.21/0.43    r1_tarski(sK2,sK1) | ~spl3_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f32])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl3_8),
% 0.21/0.43    inference(avatar_component_clause,[],[f59])).
% 0.21/0.43  fof(f65,plain,(
% 0.21/0.43    spl3_9),
% 0.21/0.43    inference(avatar_split_clause,[],[f25,f63])).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X2,X0,X1] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.21/0.43    inference(ennf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(k7_relat_1(X2,X0),X1) = k7_relat_1(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).
% 0.21/0.43  fof(f61,plain,(
% 0.21/0.43    spl3_8),
% 0.21/0.43    inference(avatar_split_clause,[],[f24,f59])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f12])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl3_7),
% 0.21/0.43    inference(avatar_split_clause,[],[f23,f55])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,plain,(
% 0.21/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.43  fof(f53,plain,(
% 0.21/0.43    spl3_6),
% 0.21/0.43    inference(avatar_split_clause,[],[f22,f51])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f10])).
% 0.21/0.43  fof(f10,plain,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.43  fof(f49,plain,(
% 0.21/0.43    spl3_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f47])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    spl3_4),
% 0.21/0.43    inference(avatar_split_clause,[],[f17,f42])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    v1_relat_1(sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    (k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(sK2,sK1)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15,f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ? [X0] : (? [X1,X2] : (k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(X2,X1)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X2,X1] : (k9_relat_1(sK0,X2) != k9_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(X2,X1)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ? [X2,X1] : (k9_relat_1(sK0,X2) != k9_relat_1(k7_relat_1(sK0,X1),X2) & r1_tarski(X2,X1)) => (k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2) & r1_tarski(sK2,sK1))),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f9,plain,(
% 0.21/0.43    ? [X0] : (? [X1,X2] : (k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(X2,X1)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.43    inference(flattening,[],[f8])).
% 0.21/0.43  fof(f8,plain,(
% 0.21/0.43    ? [X0] : (? [X1,X2] : (k9_relat_1(X0,X2) != k9_relat_1(k7_relat_1(X0,X1),X2) & r1_tarski(X2,X1)) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,negated_conjecture,(
% 0.21/0.43    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(X2,X1) => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.21/0.43    inference(negated_conjecture,[],[f6])).
% 0.21/0.43  fof(f6,conjecture,(
% 0.21/0.43    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (r1_tarski(X2,X1) => k9_relat_1(X0,X2) = k9_relat_1(k7_relat_1(X0,X1),X2)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_funct_2)).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    spl3_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f19,f32])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    r1_tarski(sK2,sK1)),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ~spl3_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f20,f27])).
% 0.21/0.43  fof(f20,plain,(
% 0.21/0.43    k9_relat_1(sK0,sK2) != k9_relat_1(k7_relat_1(sK0,sK1),sK2)),
% 0.21/0.43    inference(cnf_transformation,[],[f16])).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (11905)------------------------------
% 0.21/0.43  % (11905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (11905)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (11905)Memory used [KB]: 10618
% 0.21/0.43  % (11905)Time elapsed: 0.010 s
% 0.21/0.43  % (11905)------------------------------
% 0.21/0.43  % (11905)------------------------------
% 0.21/0.43  % (11898)Success in time 0.074 s
%------------------------------------------------------------------------------
