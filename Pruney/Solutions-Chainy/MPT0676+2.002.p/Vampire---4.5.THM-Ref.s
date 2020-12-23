%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 108 expanded)
%              Number of leaves         :   19 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :  195 ( 299 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f118,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f39,f43,f47,f51,f55,f59,f74,f81,f96,f107,f113,f117])).

fof(f117,plain,
    ( spl3_1
    | ~ spl3_17 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl3_1
    | ~ spl3_17 ),
    inference(resolution,[],[f112,f28])).

fof(f28,plain,
    ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl3_1
  <=> r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f112,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(k8_relat_1(X0,sK2),X1),k9_relat_1(sK2,X1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl3_17
  <=> ! [X1,X0] : r1_tarski(k9_relat_1(k8_relat_1(X0,sK2),X1),k9_relat_1(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f113,plain,
    ( spl3_17
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f109,f105,f94,f36,f111])).

fof(f36,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f94,plain,
    ( spl3_14
  <=> ! [X3] : v1_relat_1(k8_relat_1(X3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f105,plain,
    ( spl3_16
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k9_relat_1(k8_relat_1(X0,X1),X2),k9_relat_1(X1,X2))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k8_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f109,plain,
    ( ! [X0,X1] : r1_tarski(k9_relat_1(k8_relat_1(X0,sK2),X1),k9_relat_1(sK2,X1))
    | ~ spl3_3
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f108,f38])).

fof(f38,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(sK2)
        | r1_tarski(k9_relat_1(k8_relat_1(X0,sK2),X1),k9_relat_1(sK2,X1)) )
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(resolution,[],[f106,f95])).

fof(f95,plain,
    ( ! [X3] : v1_relat_1(k8_relat_1(X3,sK2))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f106,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1)
        | r1_tarski(k9_relat_1(k8_relat_1(X0,X1),X2),k9_relat_1(X1,X2)) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f105])).

fof(f107,plain,
    ( spl3_16
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f103,f53,f49,f105])).

fof(f49,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f53,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
        | ~ r1_tarski(X1,X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f103,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k9_relat_1(k8_relat_1(X0,X1),X2),k9_relat_1(X1,X2))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k8_relat_1(X0,X1)) )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k9_relat_1(k8_relat_1(X0,X1),X2),k9_relat_1(X1,X2))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(resolution,[],[f54,f50])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f54,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X1,X2)
        | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f96,plain,
    ( spl3_14
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f92,f79,f45,f36,f94])).

fof(f45,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f79,plain,
    ( spl3_11
  <=> ! [X0] : k8_relat_1(X0,sK2) = k3_xboole_0(sK2,k8_relat_1(X0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f92,plain,
    ( ! [X3] : v1_relat_1(k8_relat_1(X3,sK2))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f91,f38])).

fof(f91,plain,
    ( ! [X3] :
        ( v1_relat_1(k8_relat_1(X3,sK2))
        | ~ v1_relat_1(sK2) )
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(superposition,[],[f46,f80])).

fof(f80,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k3_xboole_0(sK2,k8_relat_1(X0,sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f81,plain,
    ( spl3_11
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f75,f72,f36,f79])).

fof(f72,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f75,plain,
    ( ! [X0] : k8_relat_1(X0,sK2) = k3_xboole_0(sK2,k8_relat_1(X0,sK2))
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(resolution,[],[f73,f38])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k8_relat_1(X0,X1) = k3_xboole_0(X1,k8_relat_1(X0,X1)) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f72])).

fof(f74,plain,
    ( spl3_10
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f70,f57,f49,f41,f72])).

fof(f41,plain,
    ( spl3_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f57,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = k3_xboole_0(X1,k8_relat_1(X0,X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f69,f42])).

fof(f42,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f69,plain,
    ( ! [X0,X1] :
        ( k8_relat_1(X0,X1) = k3_xboole_0(k8_relat_1(X0,X1),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_6
    | ~ spl3_8 ),
    inference(resolution,[],[f58,f50])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f55,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(f51,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f47,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f43,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))
    & v1_funct_1(sK2)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
        & v1_funct_1(X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))
      & v1_funct_1(sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_funct_1)).

fof(f29,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f19,f26])).

fof(f19,plain,(
    ~ r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:30:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.41  % (11452)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.41  % (11453)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (11452)Refutation found. Thanks to Tanya!
% 0.22/0.42  % SZS status Theorem for theBenchmark
% 0.22/0.42  % SZS output start Proof for theBenchmark
% 0.22/0.42  fof(f118,plain,(
% 0.22/0.42    $false),
% 0.22/0.42    inference(avatar_sat_refutation,[],[f29,f39,f43,f47,f51,f55,f59,f74,f81,f96,f107,f113,f117])).
% 0.22/0.42  fof(f117,plain,(
% 0.22/0.42    spl3_1 | ~spl3_17),
% 0.22/0.42    inference(avatar_contradiction_clause,[],[f114])).
% 0.22/0.42  fof(f114,plain,(
% 0.22/0.42    $false | (spl3_1 | ~spl3_17)),
% 0.22/0.42    inference(resolution,[],[f112,f28])).
% 0.22/0.42  fof(f28,plain,(
% 0.22/0.42    ~r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) | spl3_1),
% 0.22/0.42    inference(avatar_component_clause,[],[f26])).
% 0.22/0.42  fof(f26,plain,(
% 0.22/0.42    spl3_1 <=> r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.42  fof(f112,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k8_relat_1(X0,sK2),X1),k9_relat_1(sK2,X1))) ) | ~spl3_17),
% 0.22/0.42    inference(avatar_component_clause,[],[f111])).
% 0.22/0.42  fof(f111,plain,(
% 0.22/0.42    spl3_17 <=> ! [X1,X0] : r1_tarski(k9_relat_1(k8_relat_1(X0,sK2),X1),k9_relat_1(sK2,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.42  fof(f113,plain,(
% 0.22/0.42    spl3_17 | ~spl3_3 | ~spl3_14 | ~spl3_16),
% 0.22/0.42    inference(avatar_split_clause,[],[f109,f105,f94,f36,f111])).
% 0.22/0.42  fof(f36,plain,(
% 0.22/0.42    spl3_3 <=> v1_relat_1(sK2)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.42  fof(f94,plain,(
% 0.22/0.42    spl3_14 <=> ! [X3] : v1_relat_1(k8_relat_1(X3,sK2))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.42  fof(f105,plain,(
% 0.22/0.42    spl3_16 <=> ! [X1,X0,X2] : (r1_tarski(k9_relat_1(k8_relat_1(X0,X1),X2),k9_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1)))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.42  fof(f109,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(k9_relat_1(k8_relat_1(X0,sK2),X1),k9_relat_1(sK2,X1))) ) | (~spl3_3 | ~spl3_14 | ~spl3_16)),
% 0.22/0.42    inference(subsumption_resolution,[],[f108,f38])).
% 0.22/0.42  fof(f38,plain,(
% 0.22/0.42    v1_relat_1(sK2) | ~spl3_3),
% 0.22/0.42    inference(avatar_component_clause,[],[f36])).
% 0.22/0.42  fof(f108,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(sK2) | r1_tarski(k9_relat_1(k8_relat_1(X0,sK2),X1),k9_relat_1(sK2,X1))) ) | (~spl3_14 | ~spl3_16)),
% 0.22/0.42    inference(resolution,[],[f106,f95])).
% 0.22/0.42  fof(f95,plain,(
% 0.22/0.42    ( ! [X3] : (v1_relat_1(k8_relat_1(X3,sK2))) ) | ~spl3_14),
% 0.22/0.42    inference(avatar_component_clause,[],[f94])).
% 0.22/0.42  fof(f106,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1) | r1_tarski(k9_relat_1(k8_relat_1(X0,X1),X2),k9_relat_1(X1,X2))) ) | ~spl3_16),
% 0.22/0.42    inference(avatar_component_clause,[],[f105])).
% 0.22/0.42  fof(f107,plain,(
% 0.22/0.42    spl3_16 | ~spl3_6 | ~spl3_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f103,f53,f49,f105])).
% 0.22/0.42  fof(f49,plain,(
% 0.22/0.42    spl3_6 <=> ! [X1,X0] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.42  fof(f53,plain,(
% 0.22/0.42    spl3_7 <=> ! [X1,X0,X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.42  fof(f103,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(k8_relat_1(X0,X1),X2),k9_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1))) ) | (~spl3_6 | ~spl3_7)),
% 0.22/0.42    inference(duplicate_literal_removal,[],[f102])).
% 0.22/0.42  fof(f102,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(k8_relat_1(X0,X1),X2),k9_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | (~spl3_6 | ~spl3_7)),
% 0.22/0.42    inference(resolution,[],[f54,f50])).
% 0.22/0.42  fof(f50,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) ) | ~spl3_6),
% 0.22/0.42    inference(avatar_component_clause,[],[f49])).
% 0.22/0.42  fof(f54,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) ) | ~spl3_7),
% 0.22/0.42    inference(avatar_component_clause,[],[f53])).
% 0.22/0.42  fof(f96,plain,(
% 0.22/0.42    spl3_14 | ~spl3_3 | ~spl3_5 | ~spl3_11),
% 0.22/0.42    inference(avatar_split_clause,[],[f92,f79,f45,f36,f94])).
% 0.22/0.42  fof(f45,plain,(
% 0.22/0.42    spl3_5 <=> ! [X1,X0] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.42  fof(f79,plain,(
% 0.22/0.42    spl3_11 <=> ! [X0] : k8_relat_1(X0,sK2) = k3_xboole_0(sK2,k8_relat_1(X0,sK2))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.42  fof(f92,plain,(
% 0.22/0.42    ( ! [X3] : (v1_relat_1(k8_relat_1(X3,sK2))) ) | (~spl3_3 | ~spl3_5 | ~spl3_11)),
% 0.22/0.42    inference(subsumption_resolution,[],[f91,f38])).
% 0.22/0.42  fof(f91,plain,(
% 0.22/0.42    ( ! [X3] : (v1_relat_1(k8_relat_1(X3,sK2)) | ~v1_relat_1(sK2)) ) | (~spl3_5 | ~spl3_11)),
% 0.22/0.42    inference(superposition,[],[f46,f80])).
% 0.22/0.42  fof(f80,plain,(
% 0.22/0.42    ( ! [X0] : (k8_relat_1(X0,sK2) = k3_xboole_0(sK2,k8_relat_1(X0,sK2))) ) | ~spl3_11),
% 0.22/0.42    inference(avatar_component_clause,[],[f79])).
% 0.22/0.42  fof(f46,plain,(
% 0.22/0.42    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_5),
% 0.22/0.42    inference(avatar_component_clause,[],[f45])).
% 0.22/0.42  fof(f81,plain,(
% 0.22/0.42    spl3_11 | ~spl3_3 | ~spl3_10),
% 0.22/0.42    inference(avatar_split_clause,[],[f75,f72,f36,f79])).
% 0.22/0.42  fof(f72,plain,(
% 0.22/0.42    spl3_10 <=> ! [X1,X0] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.42  fof(f75,plain,(
% 0.22/0.42    ( ! [X0] : (k8_relat_1(X0,sK2) = k3_xboole_0(sK2,k8_relat_1(X0,sK2))) ) | (~spl3_3 | ~spl3_10)),
% 0.22/0.42    inference(resolution,[],[f73,f38])).
% 0.22/0.42  fof(f73,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k3_xboole_0(X1,k8_relat_1(X0,X1))) ) | ~spl3_10),
% 0.22/0.42    inference(avatar_component_clause,[],[f72])).
% 0.22/0.42  fof(f74,plain,(
% 0.22/0.42    spl3_10 | ~spl3_4 | ~spl3_6 | ~spl3_8),
% 0.22/0.42    inference(avatar_split_clause,[],[f70,f57,f49,f41,f72])).
% 0.22/0.42  fof(f41,plain,(
% 0.22/0.42    spl3_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.42  fof(f57,plain,(
% 0.22/0.42    spl3_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.42  fof(f70,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(X1,k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) ) | (~spl3_4 | ~spl3_6 | ~spl3_8)),
% 0.22/0.42    inference(forward_demodulation,[],[f69,f42])).
% 0.22/0.42  fof(f42,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.22/0.42    inference(avatar_component_clause,[],[f41])).
% 0.22/0.42  fof(f69,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k8_relat_1(X0,X1) = k3_xboole_0(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) ) | (~spl3_6 | ~spl3_8)),
% 0.22/0.42    inference(resolution,[],[f58,f50])).
% 0.22/0.42  fof(f58,plain,(
% 0.22/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl3_8),
% 0.22/0.42    inference(avatar_component_clause,[],[f57])).
% 0.22/0.42  fof(f59,plain,(
% 0.22/0.42    spl3_8),
% 0.22/0.42    inference(avatar_split_clause,[],[f24,f57])).
% 0.22/0.42  fof(f24,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f14])).
% 0.22/0.42  fof(f14,plain,(
% 0.22/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f2])).
% 0.22/0.42  fof(f2,axiom,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.42  fof(f55,plain,(
% 0.22/0.42    spl3_7),
% 0.22/0.42    inference(avatar_split_clause,[],[f23,f53])).
% 0.22/0.42  fof(f23,plain,(
% 0.22/0.42    ( ! [X2,X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f13])).
% 0.22/0.42  fof(f13,plain,(
% 0.22/0.42    ! [X0,X1] : (! [X2] : (r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(flattening,[],[f12])).
% 0.22/0.42  fof(f12,plain,(
% 0.22/0.42    ! [X0,X1] : (! [X2] : ((r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f5])).
% 0.22/0.42  fof(f5,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).
% 0.22/0.42  fof(f51,plain,(
% 0.22/0.42    spl3_6),
% 0.22/0.42    inference(avatar_split_clause,[],[f22,f49])).
% 0.22/0.42  fof(f22,plain,(
% 0.22/0.42    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f11])).
% 0.22/0.42  fof(f11,plain,(
% 0.22/0.42    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.42    inference(ennf_transformation,[],[f4])).
% 0.22/0.42  fof(f4,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.22/0.42  fof(f47,plain,(
% 0.22/0.42    spl3_5),
% 0.22/0.42    inference(avatar_split_clause,[],[f21,f45])).
% 0.22/0.42  fof(f21,plain,(
% 0.22/0.42    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f10])).
% 0.22/0.42  fof(f10,plain,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.42    inference(ennf_transformation,[],[f3])).
% 0.22/0.42  fof(f3,axiom,(
% 0.22/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.22/0.42  fof(f43,plain,(
% 0.22/0.42    spl3_4),
% 0.22/0.42    inference(avatar_split_clause,[],[f20,f41])).
% 0.22/0.42  fof(f20,plain,(
% 0.22/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.42    inference(cnf_transformation,[],[f1])).
% 0.22/0.42  fof(f1,axiom,(
% 0.22/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.42  fof(f39,plain,(
% 0.22/0.42    spl3_3),
% 0.22/0.42    inference(avatar_split_clause,[],[f17,f36])).
% 0.22/0.42  fof(f17,plain,(
% 0.22/0.42    v1_relat_1(sK2)),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  fof(f16,plain,(
% 0.22/0.42    ~r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2)),
% 0.22/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).
% 0.22/0.42  fof(f15,plain,(
% 0.22/0.42    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1)) & v1_funct_1(sK2) & v1_relat_1(sK2))),
% 0.22/0.42    introduced(choice_axiom,[])).
% 0.22/0.42  fof(f9,plain,(
% 0.22/0.42    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.42    inference(flattening,[],[f8])).
% 0.22/0.42  fof(f8,plain,(
% 0.22/0.42    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.42    inference(ennf_transformation,[],[f7])).
% 0.22/0.42  fof(f7,negated_conjecture,(
% 0.22/0.42    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)))),
% 0.22/0.42    inference(negated_conjecture,[],[f6])).
% 0.22/0.42  fof(f6,conjecture,(
% 0.22/0.42    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => r1_tarski(k9_relat_1(k8_relat_1(X0,X2),X1),k9_relat_1(X2,X1)))),
% 0.22/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_funct_1)).
% 0.22/0.42  fof(f29,plain,(
% 0.22/0.42    ~spl3_1),
% 0.22/0.42    inference(avatar_split_clause,[],[f19,f26])).
% 0.22/0.42  fof(f19,plain,(
% 0.22/0.42    ~r1_tarski(k9_relat_1(k8_relat_1(sK0,sK2),sK1),k9_relat_1(sK2,sK1))),
% 0.22/0.42    inference(cnf_transformation,[],[f16])).
% 0.22/0.42  % SZS output end Proof for theBenchmark
% 0.22/0.42  % (11452)------------------------------
% 0.22/0.42  % (11452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (11452)Termination reason: Refutation
% 0.22/0.42  
% 0.22/0.42  % (11452)Memory used [KB]: 10618
% 0.22/0.42  % (11452)Time elapsed: 0.007 s
% 0.22/0.42  % (11452)------------------------------
% 0.22/0.42  % (11452)------------------------------
% 0.22/0.42  % (11446)Success in time 0.066 s
%------------------------------------------------------------------------------
