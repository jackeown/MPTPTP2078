%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:54:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 128 expanded)
%              Number of leaves         :   27 (  61 expanded)
%              Depth                    :    6
%              Number of atoms          :  195 ( 281 expanded)
%              Number of equality atoms :   57 (  85 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f48,f52,f60,f64,f68,f72,f76,f84,f91,f97,f109,f114,f119,f126,f153,f416])).

fof(f416,plain,
    ( spl2_1
    | ~ spl2_5
    | ~ spl2_18
    | ~ spl2_22 ),
    inference(avatar_contradiction_clause,[],[f415])).

fof(f415,plain,
    ( $false
    | spl2_1
    | ~ spl2_5
    | ~ spl2_18
    | ~ spl2_22 ),
    inference(subsumption_resolution,[],[f414,f34])).

fof(f34,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl2_1
  <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f414,plain,
    ( sK1 = k9_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_5
    | ~ spl2_18
    | ~ spl2_22 ),
    inference(forward_demodulation,[],[f401,f51])).

fof(f51,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl2_5
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f401,plain,
    ( k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl2_18
    | ~ spl2_22 ),
    inference(superposition,[],[f118,f152])).

fof(f152,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_22 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl2_22
  <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f118,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl2_18
  <=> ! [X1,X0] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f153,plain,
    ( spl2_22
    | ~ spl2_16
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f130,f123,f103,f150])).

fof(f103,plain,
    ( spl2_16
  <=> sK1 = k3_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f123,plain,
    ( spl2_19
  <=> ! [X3,X2] : k6_relat_1(k3_xboole_0(X3,X2)) = k7_relat_1(k6_relat_1(X3),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f130,plain,
    ( k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl2_16
    | ~ spl2_19 ),
    inference(superposition,[],[f124,f105])).

fof(f105,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f103])).

fof(f124,plain,
    ( ! [X2,X3] : k6_relat_1(k3_xboole_0(X3,X2)) = k7_relat_1(k6_relat_1(X3),X2)
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f123])).

fof(f126,plain,
    ( spl2_19
    | ~ spl2_8
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f121,f112,f62,f123])).

fof(f62,plain,
    ( spl2_8
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f112,plain,
    ( spl2_17
  <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f121,plain,
    ( ! [X0,X1] : k6_relat_1(k3_xboole_0(X1,X0)) = k7_relat_1(k6_relat_1(X1),X0)
    | ~ spl2_8
    | ~ spl2_17 ),
    inference(superposition,[],[f63,f113])).

fof(f113,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f112])).

fof(f63,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f119,plain,
    ( spl2_18
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f115,f70,f46,f117])).

fof(f46,plain,
    ( spl2_4
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f70,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f115,plain,
    ( ! [X0,X1] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(resolution,[],[f71,f47])).

fof(f47,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f70])).

fof(f114,plain,
    ( spl2_17
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f110,f66,f46,f112])).

fof(f66,plain,
    ( spl2_9
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f110,plain,
    ( ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(resolution,[],[f67,f47])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) )
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f109,plain,
    ( spl2_16
    | ~ spl2_7
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f101,f94,f58,f103])).

fof(f58,plain,
    ( spl2_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f94,plain,
    ( spl2_15
  <=> sK1 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f101,plain,
    ( sK1 = k3_xboole_0(sK0,sK1)
    | ~ spl2_7
    | ~ spl2_15 ),
    inference(superposition,[],[f59,f96])).

fof(f96,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f94])).

fof(f59,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f58])).

fof(f97,plain,
    ( spl2_15
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f92,f88,f74,f94])).

fof(f74,plain,
    ( spl2_11
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f88,plain,
    ( spl2_14
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f92,plain,
    ( sK1 = k3_xboole_0(sK1,sK0)
    | ~ spl2_11
    | ~ spl2_14 ),
    inference(resolution,[],[f75,f90])).

fof(f90,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f88])).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f91,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f85,f82,f37,f88])).

fof(f37,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f82,plain,
    ( spl2_13
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f85,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl2_2
    | ~ spl2_13 ),
    inference(resolution,[],[f83,f39])).

fof(f39,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
        | r1_tarski(X0,X1) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f82])).

fof(f84,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f29,f82])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f76,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f28,f74])).

fof(f28,plain,(
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

fof(f72,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f27,f70])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f68,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f26,f66])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f64,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f25,f62])).

fof(f25,plain,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

fof(f60,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f24,f58])).

fof(f24,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f52,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f23,f50])).

fof(f23,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f48,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

fof(f40,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1] :
        ( k9_relat_1(k6_relat_1(X0),X1) != X1
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
   => ( sK1 != k9_relat_1(k6_relat_1(sK0),sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k9_relat_1(k6_relat_1(X0),X1) != X1
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,k1_zfmisc_1(X0))
       => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k9_relat_1(k6_relat_1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

fof(f35,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f19,f32])).

fof(f19,plain,(
    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:40:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.41  % (29332)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.42  % (29332)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f419,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f35,f40,f48,f52,f60,f64,f68,f72,f76,f84,f91,f97,f109,f114,f119,f126,f153,f416])).
% 0.21/0.42  fof(f416,plain,(
% 0.21/0.42    spl2_1 | ~spl2_5 | ~spl2_18 | ~spl2_22),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f415])).
% 0.21/0.42  fof(f415,plain,(
% 0.21/0.42    $false | (spl2_1 | ~spl2_5 | ~spl2_18 | ~spl2_22)),
% 0.21/0.42    inference(subsumption_resolution,[],[f414,f34])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) | spl2_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl2_1 <=> sK1 = k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.42  fof(f414,plain,(
% 0.21/0.42    sK1 = k9_relat_1(k6_relat_1(sK0),sK1) | (~spl2_5 | ~spl2_18 | ~spl2_22)),
% 0.21/0.42    inference(forward_demodulation,[],[f401,f51])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl2_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f50])).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl2_5 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.42  fof(f401,plain,(
% 0.21/0.42    k9_relat_1(k6_relat_1(sK0),sK1) = k2_relat_1(k6_relat_1(sK1)) | (~spl2_18 | ~spl2_22)),
% 0.21/0.42    inference(superposition,[],[f118,f152])).
% 0.21/0.42  fof(f152,plain,(
% 0.21/0.42    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | ~spl2_22),
% 0.21/0.42    inference(avatar_component_clause,[],[f150])).
% 0.21/0.42  fof(f150,plain,(
% 0.21/0.42    spl2_22 <=> k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | ~spl2_18),
% 0.21/0.42    inference(avatar_component_clause,[],[f117])).
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    spl2_18 <=> ! [X1,X0] : k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.42  fof(f153,plain,(
% 0.21/0.42    spl2_22 | ~spl2_16 | ~spl2_19),
% 0.21/0.42    inference(avatar_split_clause,[],[f130,f123,f103,f150])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    spl2_16 <=> sK1 = k3_xboole_0(sK0,sK1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.42  fof(f123,plain,(
% 0.21/0.42    spl2_19 <=> ! [X3,X2] : k6_relat_1(k3_xboole_0(X3,X2)) = k7_relat_1(k6_relat_1(X3),X2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    k6_relat_1(sK1) = k7_relat_1(k6_relat_1(sK0),sK1) | (~spl2_16 | ~spl2_19)),
% 0.21/0.42    inference(superposition,[],[f124,f105])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    sK1 = k3_xboole_0(sK0,sK1) | ~spl2_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f103])).
% 0.21/0.42  fof(f124,plain,(
% 0.21/0.42    ( ! [X2,X3] : (k6_relat_1(k3_xboole_0(X3,X2)) = k7_relat_1(k6_relat_1(X3),X2)) ) | ~spl2_19),
% 0.21/0.42    inference(avatar_component_clause,[],[f123])).
% 0.21/0.42  fof(f126,plain,(
% 0.21/0.42    spl2_19 | ~spl2_8 | ~spl2_17),
% 0.21/0.42    inference(avatar_split_clause,[],[f121,f112,f62,f123])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    spl2_8 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    spl2_17 <=> ! [X1,X0] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.42  fof(f121,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k6_relat_1(k3_xboole_0(X1,X0)) = k7_relat_1(k6_relat_1(X1),X0)) ) | (~spl2_8 | ~spl2_17)),
% 0.21/0.42    inference(superposition,[],[f63,f113])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f112])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) ) | ~spl2_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f62])).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    spl2_18 | ~spl2_4 | ~spl2_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f115,f70,f46,f117])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl2_4 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    spl2_10 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) = k2_relat_1(k7_relat_1(k6_relat_1(X0),X1))) ) | (~spl2_4 | ~spl2_10)),
% 0.21/0.42    inference(resolution,[],[f71,f47])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl2_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f46])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f70])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    spl2_17 | ~spl2_4 | ~spl2_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f110,f66,f46,f112])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl2_9 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.42  fof(f110,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k7_relat_1(k6_relat_1(X0),X1)) ) | (~spl2_4 | ~spl2_9)),
% 0.21/0.42    inference(resolution,[],[f67,f47])).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) ) | ~spl2_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f66])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    spl2_16 | ~spl2_7 | ~spl2_15),
% 0.21/0.42    inference(avatar_split_clause,[],[f101,f94,f58,f103])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl2_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    spl2_15 <=> sK1 = k3_xboole_0(sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    sK1 = k3_xboole_0(sK0,sK1) | (~spl2_7 | ~spl2_15)),
% 0.21/0.42    inference(superposition,[],[f59,f96])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    sK1 = k3_xboole_0(sK1,sK0) | ~spl2_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f94])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f58])).
% 0.21/0.42  fof(f97,plain,(
% 0.21/0.42    spl2_15 | ~spl2_11 | ~spl2_14),
% 0.21/0.42    inference(avatar_split_clause,[],[f92,f88,f74,f94])).
% 0.21/0.42  fof(f74,plain,(
% 0.21/0.42    spl2_11 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    spl2_14 <=> r1_tarski(sK1,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    sK1 = k3_xboole_0(sK1,sK0) | (~spl2_11 | ~spl2_14)),
% 0.21/0.42    inference(resolution,[],[f75,f90])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    r1_tarski(sK1,sK0) | ~spl2_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f88])).
% 0.21/0.42  fof(f75,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl2_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f74])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    spl2_14 | ~spl2_2 | ~spl2_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f85,f82,f37,f88])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    spl2_13 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    r1_tarski(sK1,sK0) | (~spl2_2 | ~spl2_13)),
% 0.21/0.42    inference(resolution,[],[f83,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0)) | ~spl2_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f37])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) ) | ~spl2_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f82])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    spl2_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f29,f82])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.42    inference(nnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl2_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f28,f74])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.42  fof(f72,plain,(
% 0.21/0.42    spl2_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f27,f70])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl2_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f26,f66])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    spl2_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f25,f62])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,axiom,(
% 0.21/0.42    ! [X0,X1] : k5_relat_1(k6_relat_1(X1),k6_relat_1(X0)) = k6_relat_1(k3_xboole_0(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl2_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f58])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    spl2_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f50])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl2_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f46])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0] : (v1_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl2_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f37])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0))) => (sK1 != k9_relat_1(k6_relat_1(sK0),sK1) & m1_subset_1(sK1,k1_zfmisc_1(sK0)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ? [X0,X1] : (k9_relat_1(k6_relat_1(X0),X1) != X1 & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.42    inference(negated_conjecture,[],[f9])).
% 0.21/0.42  fof(f9,conjecture,(
% 0.21/0.42    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k9_relat_1(k6_relat_1(X0),X1) = X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    ~spl2_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f32])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    sK1 != k9_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (29332)------------------------------
% 0.21/0.42  % (29332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (29332)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (29332)Memory used [KB]: 10746
% 0.21/0.42  % (29332)Time elapsed: 0.011 s
% 0.21/0.42  % (29332)------------------------------
% 0.21/0.42  % (29332)------------------------------
% 0.21/0.43  % (29324)Success in time 0.071 s
%------------------------------------------------------------------------------
