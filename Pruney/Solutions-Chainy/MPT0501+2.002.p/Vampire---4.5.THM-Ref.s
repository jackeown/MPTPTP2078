%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:33 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 106 expanded)
%              Number of leaves         :   19 (  49 expanded)
%              Depth                    :    6
%              Number of atoms          :  189 ( 284 expanded)
%              Number of equality atoms :   16 (  24 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f123,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f37,f45,f49,f53,f57,f72,f79,f94,f105,f117,f122])).

fof(f122,plain,
    ( spl2_1
    | ~ spl2_18 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl2_1
    | ~ spl2_18 ),
    inference(resolution,[],[f116,f27])).

fof(f27,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl2_1
  <=> r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f116,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(sK1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl2_18
  <=> ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f117,plain,
    ( spl2_18
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f113,f103,f92,f30,f115])).

fof(f30,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f92,plain,
    ( spl2_14
  <=> ! [X3] : v1_relat_1(k7_relat_1(sK1,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f103,plain,
    ( spl2_16
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f113,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(sK1))
    | ~ spl2_2
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(subsumption_resolution,[],[f112,f32])).

fof(f32,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK1)
        | r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(sK1)) )
    | ~ spl2_14
    | ~ spl2_16 ),
    inference(resolution,[],[f104,f93])).

fof(f93,plain,
    ( ! [X3] : v1_relat_1(k7_relat_1(sK1,X3))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f92])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0)
        | r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f103])).

fof(f105,plain,
    ( spl2_16
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f101,f51,f35,f103])).

fof(f35,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f51,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f101,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1)) )
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(duplicate_literal_removal,[],[f100])).

fof(f100,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f36,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k7_relat_1(X1,X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f94,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f90,f77,f47,f30,f92])).

fof(f47,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f77,plain,
    ( spl2_11
  <=> ! [X0] : k7_relat_1(sK1,X0) = k3_xboole_0(sK1,k7_relat_1(sK1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f90,plain,
    ( ! [X3] : v1_relat_1(k7_relat_1(sK1,X3))
    | ~ spl2_2
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f89,f32])).

fof(f89,plain,
    ( ! [X3] :
        ( v1_relat_1(k7_relat_1(sK1,X3))
        | ~ v1_relat_1(sK1) )
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(superposition,[],[f48,f78])).

fof(f78,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k3_xboole_0(sK1,k7_relat_1(sK1,X0))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f77])).

fof(f48,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f79,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f73,f70,f30,f77])).

fof(f70,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k7_relat_1(X0,X1) = k3_xboole_0(X0,k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f73,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k3_xboole_0(sK1,k7_relat_1(sK1,X0))
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(resolution,[],[f71,f32])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k7_relat_1(X0,X1) = k3_xboole_0(X0,k7_relat_1(X0,X1)) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f72,plain,
    ( spl2_10
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f68,f55,f51,f43,f70])).

fof(f43,plain,
    ( spl2_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f55,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k3_xboole_0(X0,k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_5
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f67,f44])).

fof(f44,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X0,X1) = k3_xboole_0(k7_relat_1(X0,X1),X0)
        | ~ v1_relat_1(X0) )
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(resolution,[],[f56,f52])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f55])).

fof(f57,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f53,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f22,f51])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f49,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f45,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f37,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f35])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

% (8654)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f33,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

fof(f28,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f17,f25])).

fof(f17,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:09:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.42  % (8656)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.13/0.42  % (8657)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.13/0.42  % (8656)Refutation found. Thanks to Tanya!
% 0.13/0.42  % SZS status Theorem for theBenchmark
% 0.13/0.42  % SZS output start Proof for theBenchmark
% 0.13/0.42  fof(f123,plain,(
% 0.13/0.42    $false),
% 0.13/0.42    inference(avatar_sat_refutation,[],[f28,f33,f37,f45,f49,f53,f57,f72,f79,f94,f105,f117,f122])).
% 0.13/0.42  fof(f122,plain,(
% 0.13/0.42    spl2_1 | ~spl2_18),
% 0.13/0.42    inference(avatar_contradiction_clause,[],[f118])).
% 0.13/0.42  fof(f118,plain,(
% 0.13/0.42    $false | (spl2_1 | ~spl2_18)),
% 0.13/0.42    inference(resolution,[],[f116,f27])).
% 0.13/0.42  fof(f27,plain,(
% 0.13/0.42    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1)) | spl2_1),
% 0.13/0.42    inference(avatar_component_clause,[],[f25])).
% 0.13/0.42  fof(f25,plain,(
% 0.13/0.42    spl2_1 <=> r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.13/0.42  fof(f116,plain,(
% 0.13/0.42    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(sK1))) ) | ~spl2_18),
% 0.13/0.42    inference(avatar_component_clause,[],[f115])).
% 0.13/0.42  fof(f115,plain,(
% 0.13/0.42    spl2_18 <=> ! [X0] : r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(sK1))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.13/0.42  fof(f117,plain,(
% 0.13/0.42    spl2_18 | ~spl2_2 | ~spl2_14 | ~spl2_16),
% 0.13/0.42    inference(avatar_split_clause,[],[f113,f103,f92,f30,f115])).
% 0.13/0.42  fof(f30,plain,(
% 0.13/0.42    spl2_2 <=> v1_relat_1(sK1)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.13/0.42  fof(f92,plain,(
% 0.13/0.42    spl2_14 <=> ! [X3] : v1_relat_1(k7_relat_1(sK1,X3))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.13/0.42  fof(f103,plain,(
% 0.13/0.42    spl2_16 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.13/0.42  fof(f113,plain,(
% 0.13/0.42    ( ! [X0] : (r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(sK1))) ) | (~spl2_2 | ~spl2_14 | ~spl2_16)),
% 0.13/0.42    inference(subsumption_resolution,[],[f112,f32])).
% 0.13/0.42  fof(f32,plain,(
% 0.13/0.42    v1_relat_1(sK1) | ~spl2_2),
% 0.13/0.42    inference(avatar_component_clause,[],[f30])).
% 0.13/0.42  fof(f112,plain,(
% 0.13/0.42    ( ! [X0] : (~v1_relat_1(sK1) | r1_tarski(k2_relat_1(k7_relat_1(sK1,X0)),k2_relat_1(sK1))) ) | (~spl2_14 | ~spl2_16)),
% 0.13/0.42    inference(resolution,[],[f104,f93])).
% 0.13/0.42  fof(f93,plain,(
% 0.13/0.42    ( ! [X3] : (v1_relat_1(k7_relat_1(sK1,X3))) ) | ~spl2_14),
% 0.13/0.42    inference(avatar_component_clause,[],[f92])).
% 0.13/0.42  fof(f104,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0) | r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0))) ) | ~spl2_16),
% 0.13/0.42    inference(avatar_component_clause,[],[f103])).
% 0.13/0.42  fof(f105,plain,(
% 0.13/0.42    spl2_16 | ~spl2_3 | ~spl2_7),
% 0.13/0.42    inference(avatar_split_clause,[],[f101,f51,f35,f103])).
% 0.13/0.42  fof(f35,plain,(
% 0.13/0.42    spl2_3 <=> ! [X1,X0] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.13/0.42  fof(f51,plain,(
% 0.13/0.42    spl2_7 <=> ! [X1,X0] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.13/0.42  fof(f101,plain,(
% 0.13/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1))) ) | (~spl2_3 | ~spl2_7)),
% 0.13/0.42    inference(duplicate_literal_removal,[],[f100])).
% 0.13/0.42  fof(f100,plain,(
% 0.13/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k7_relat_1(X0,X1)),k2_relat_1(X0)) | ~v1_relat_1(X0) | ~v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | (~spl2_3 | ~spl2_7)),
% 0.13/0.42    inference(resolution,[],[f36,f52])).
% 0.13/0.42  fof(f52,plain,(
% 0.13/0.42    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) ) | ~spl2_7),
% 0.13/0.42    inference(avatar_component_clause,[],[f51])).
% 0.13/0.42  fof(f36,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_3),
% 0.13/0.42    inference(avatar_component_clause,[],[f35])).
% 0.13/0.42  fof(f94,plain,(
% 0.13/0.42    spl2_14 | ~spl2_2 | ~spl2_6 | ~spl2_11),
% 0.13/0.42    inference(avatar_split_clause,[],[f90,f77,f47,f30,f92])).
% 0.13/0.42  fof(f47,plain,(
% 0.13/0.42    spl2_6 <=> ! [X1,X0] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.13/0.42  fof(f77,plain,(
% 0.13/0.42    spl2_11 <=> ! [X0] : k7_relat_1(sK1,X0) = k3_xboole_0(sK1,k7_relat_1(sK1,X0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.13/0.42  fof(f90,plain,(
% 0.13/0.42    ( ! [X3] : (v1_relat_1(k7_relat_1(sK1,X3))) ) | (~spl2_2 | ~spl2_6 | ~spl2_11)),
% 0.13/0.42    inference(subsumption_resolution,[],[f89,f32])).
% 0.13/0.42  fof(f89,plain,(
% 0.13/0.42    ( ! [X3] : (v1_relat_1(k7_relat_1(sK1,X3)) | ~v1_relat_1(sK1)) ) | (~spl2_6 | ~spl2_11)),
% 0.13/0.42    inference(superposition,[],[f48,f78])).
% 0.13/0.42  fof(f78,plain,(
% 0.13/0.42    ( ! [X0] : (k7_relat_1(sK1,X0) = k3_xboole_0(sK1,k7_relat_1(sK1,X0))) ) | ~spl2_11),
% 0.13/0.42    inference(avatar_component_clause,[],[f77])).
% 0.13/0.42  fof(f48,plain,(
% 0.13/0.42    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_6),
% 0.13/0.42    inference(avatar_component_clause,[],[f47])).
% 0.13/0.42  fof(f79,plain,(
% 0.13/0.42    spl2_11 | ~spl2_2 | ~spl2_10),
% 0.13/0.42    inference(avatar_split_clause,[],[f73,f70,f30,f77])).
% 0.13/0.42  fof(f70,plain,(
% 0.13/0.42    spl2_10 <=> ! [X1,X0] : (k7_relat_1(X0,X1) = k3_xboole_0(X0,k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.13/0.42  fof(f73,plain,(
% 0.13/0.42    ( ! [X0] : (k7_relat_1(sK1,X0) = k3_xboole_0(sK1,k7_relat_1(sK1,X0))) ) | (~spl2_2 | ~spl2_10)),
% 0.13/0.42    inference(resolution,[],[f71,f32])).
% 0.13/0.42  fof(f71,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~v1_relat_1(X0) | k7_relat_1(X0,X1) = k3_xboole_0(X0,k7_relat_1(X0,X1))) ) | ~spl2_10),
% 0.13/0.42    inference(avatar_component_clause,[],[f70])).
% 0.13/0.42  fof(f72,plain,(
% 0.13/0.42    spl2_10 | ~spl2_5 | ~spl2_7 | ~spl2_8),
% 0.13/0.42    inference(avatar_split_clause,[],[f68,f55,f51,f43,f70])).
% 0.13/0.42  fof(f43,plain,(
% 0.13/0.42    spl2_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.13/0.42  fof(f55,plain,(
% 0.13/0.42    spl2_8 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.13/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.13/0.42  fof(f68,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k3_xboole_0(X0,k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | (~spl2_5 | ~spl2_7 | ~spl2_8)),
% 0.13/0.42    inference(forward_demodulation,[],[f67,f44])).
% 0.13/0.42  fof(f44,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_5),
% 0.13/0.42    inference(avatar_component_clause,[],[f43])).
% 0.13/0.42  fof(f67,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k7_relat_1(X0,X1) = k3_xboole_0(k7_relat_1(X0,X1),X0) | ~v1_relat_1(X0)) ) | (~spl2_7 | ~spl2_8)),
% 0.13/0.42    inference(resolution,[],[f56,f52])).
% 0.13/0.42  fof(f56,plain,(
% 0.13/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl2_8),
% 0.13/0.42    inference(avatar_component_clause,[],[f55])).
% 0.13/0.42  fof(f57,plain,(
% 0.13/0.42    spl2_8),
% 0.13/0.42    inference(avatar_split_clause,[],[f23,f55])).
% 0.13/0.42  fof(f23,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f13])).
% 0.13/0.42  fof(f13,plain,(
% 0.13/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f2])).
% 0.13/0.42  fof(f2,axiom,(
% 0.13/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.13/0.42  fof(f53,plain,(
% 0.13/0.42    spl2_7),
% 0.13/0.42    inference(avatar_split_clause,[],[f22,f51])).
% 0.13/0.42  fof(f22,plain,(
% 0.13/0.42    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f12])).
% 0.13/0.42  fof(f12,plain,(
% 0.13/0.42    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f5])).
% 0.13/0.42  fof(f5,axiom,(
% 0.13/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 0.13/0.42  fof(f49,plain,(
% 0.13/0.42    spl2_6),
% 0.13/0.42    inference(avatar_split_clause,[],[f21,f47])).
% 0.13/0.42  fof(f21,plain,(
% 0.13/0.42    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f11])).
% 0.13/0.42  fof(f11,plain,(
% 0.13/0.42    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.13/0.42    inference(ennf_transformation,[],[f3])).
% 0.13/0.42  fof(f3,axiom,(
% 0.13/0.42    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.13/0.42  fof(f45,plain,(
% 0.13/0.42    spl2_5),
% 0.13/0.42    inference(avatar_split_clause,[],[f20,f43])).
% 0.13/0.42  fof(f20,plain,(
% 0.13/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f1])).
% 0.13/0.42  fof(f1,axiom,(
% 0.13/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.13/0.42  fof(f37,plain,(
% 0.13/0.42    spl2_3),
% 0.13/0.42    inference(avatar_split_clause,[],[f19,f35])).
% 0.13/0.42  fof(f19,plain,(
% 0.13/0.42    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.13/0.42    inference(cnf_transformation,[],[f10])).
% 0.13/0.42  fof(f10,plain,(
% 0.13/0.42    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.13/0.42    inference(flattening,[],[f9])).
% 0.13/0.42  % (8654)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.13/0.42  fof(f9,plain,(
% 0.13/0.42    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.13/0.42    inference(ennf_transformation,[],[f4])).
% 0.13/0.42  fof(f4,axiom,(
% 0.13/0.42    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.13/0.42  fof(f33,plain,(
% 0.13/0.42    spl2_2),
% 0.13/0.42    inference(avatar_split_clause,[],[f16,f30])).
% 0.13/0.42  fof(f16,plain,(
% 0.13/0.42    v1_relat_1(sK1)),
% 0.13/0.42    inference(cnf_transformation,[],[f15])).
% 0.13/0.42  fof(f15,plain,(
% 0.13/0.42    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.13/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f14])).
% 0.13/0.42  fof(f14,plain,(
% 0.13/0.42    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.13/0.42    introduced(choice_axiom,[])).
% 0.13/0.42  fof(f8,plain,(
% 0.13/0.42    ? [X0,X1] : (~r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)) & v1_relat_1(X1))),
% 0.13/0.42    inference(ennf_transformation,[],[f7])).
% 0.13/0.42  fof(f7,negated_conjecture,(
% 0.13/0.42    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.13/0.42    inference(negated_conjecture,[],[f6])).
% 0.13/0.42  fof(f6,conjecture,(
% 0.13/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k7_relat_1(X1,X0)),k2_relat_1(X1)))),
% 0.13/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).
% 0.13/0.42  fof(f28,plain,(
% 0.13/0.42    ~spl2_1),
% 0.13/0.42    inference(avatar_split_clause,[],[f17,f25])).
% 0.13/0.42  fof(f17,plain,(
% 0.13/0.42    ~r1_tarski(k2_relat_1(k7_relat_1(sK1,sK0)),k2_relat_1(sK1))),
% 0.13/0.42    inference(cnf_transformation,[],[f15])).
% 0.13/0.42  % SZS output end Proof for theBenchmark
% 0.13/0.42  % (8656)------------------------------
% 0.13/0.42  % (8656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.13/0.42  % (8656)Termination reason: Refutation
% 0.13/0.42  
% 0.13/0.42  % (8656)Memory used [KB]: 10618
% 0.13/0.42  % (8656)Time elapsed: 0.007 s
% 0.13/0.42  % (8656)------------------------------
% 0.13/0.42  % (8656)------------------------------
% 0.13/0.42  % (8650)Success in time 0.064 s
%------------------------------------------------------------------------------
