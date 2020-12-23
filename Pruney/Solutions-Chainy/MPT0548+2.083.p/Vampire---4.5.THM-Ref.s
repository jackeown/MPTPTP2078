%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   74 (  98 expanded)
%              Number of leaves         :   21 (  45 expanded)
%              Depth                    :    6
%              Number of atoms          :  175 ( 236 expanded)
%              Number of equality atoms :   42 (  60 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f124,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f39,f43,f47,f51,f59,f65,f69,f73,f96,f103,f113,f123])).

fof(f123,plain,
    ( ~ spl1_2
    | ~ spl1_8
    | spl1_18 ),
    inference(avatar_contradiction_clause,[],[f122])).

fof(f122,plain,
    ( $false
    | ~ spl1_2
    | ~ spl1_8
    | spl1_18 ),
    inference(subsumption_resolution,[],[f120,f34])).

fof(f34,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl1_2
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f120,plain,
    ( ~ r1_xboole_0(sK0,k1_xboole_0)
    | ~ spl1_8
    | spl1_18 ),
    inference(resolution,[],[f112,f58])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl1_8
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f112,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | spl1_18 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl1_18
  <=> r1_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f113,plain,
    ( ~ spl1_18
    | spl1_1
    | ~ spl1_16 ),
    inference(avatar_split_clause,[],[f105,f101,f29,f111])).

fof(f29,plain,
    ( spl1_1
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f101,plain,
    ( spl1_16
  <=> ! [X3] :
        ( ~ r1_xboole_0(k1_xboole_0,X3)
        | k1_xboole_0 = k9_relat_1(k1_xboole_0,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f105,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | spl1_1
    | ~ spl1_16 ),
    inference(trivial_inequality_removal,[],[f104])).

fof(f104,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,sK0)
    | spl1_1
    | ~ spl1_16 ),
    inference(superposition,[],[f30,f102])).

fof(f102,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)
        | ~ r1_xboole_0(k1_xboole_0,X3) )
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f101])).

fof(f30,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f103,plain,
    ( spl1_16
    | ~ spl1_3
    | ~ spl1_9
    | ~ spl1_15 ),
    inference(avatar_split_clause,[],[f99,f94,f63,f37,f101])).

fof(f37,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f63,plain,
    ( spl1_9
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f94,plain,
    ( spl1_15
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f99,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(k1_xboole_0,X3)
        | k1_xboole_0 = k9_relat_1(k1_xboole_0,X3) )
    | ~ spl1_3
    | ~ spl1_9
    | ~ spl1_15 ),
    inference(forward_demodulation,[],[f98,f38])).

fof(f38,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f98,plain,
    ( ! [X3] :
        ( k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)
        | ~ r1_xboole_0(k1_relat_1(k1_xboole_0),X3) )
    | ~ spl1_9
    | ~ spl1_15 ),
    inference(resolution,[],[f95,f64])).

fof(f64,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f95,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k9_relat_1(X0,X1)
        | ~ r1_xboole_0(k1_relat_1(X0),X1) )
    | ~ spl1_15 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,
    ( spl1_15
    | ~ spl1_4
    | ~ spl1_10
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f84,f71,f67,f41,f94])).

fof(f41,plain,
    ( spl1_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f67,plain,
    ( spl1_10
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f71,plain,
    ( spl1_11
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f84,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),X1) )
    | ~ spl1_4
    | ~ spl1_10
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f83,f42])).

fof(f42,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f83,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k1_xboole_0) = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),X1) )
    | ~ spl1_10
    | ~ spl1_11 ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k1_xboole_0) = k9_relat_1(X0,X1)
        | ~ v1_relat_1(X0)
        | ~ r1_xboole_0(k1_relat_1(X0),X1)
        | ~ v1_relat_1(X0) )
    | ~ spl1_10
    | ~ spl1_11 ),
    inference(superposition,[],[f68,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k7_relat_1(X1,X0)
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f71])).

fof(f68,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f67])).

fof(f73,plain,(
    spl1_11 ),
    inference(avatar_split_clause,[],[f20,f71])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f69,plain,(
    spl1_10 ),
    inference(avatar_split_clause,[],[f19,f67])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

fof(f65,plain,
    ( spl1_9
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f60,f49,f45,f63])).

fof(f45,plain,
    ( spl1_5
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f49,plain,
    ( spl1_6
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f60,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(superposition,[],[f46,f50])).

fof(f50,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f46,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f59,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f22,f57])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f51,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f47,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f18,f45])).

fof(f18,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f43,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f16,f41])).

fof(f16,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f39,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f15,f37])).

fof(f15,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f35,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f31,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f14,f29])).

fof(f14,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (4670)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (4670)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f124,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f31,f35,f39,f43,f47,f51,f59,f65,f69,f73,f96,f103,f113,f123])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    ~spl1_2 | ~spl1_8 | spl1_18),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f122])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    $false | (~spl1_2 | ~spl1_8 | spl1_18)),
% 0.21/0.47    inference(subsumption_resolution,[],[f120,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl1_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    spl1_2 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ~r1_xboole_0(sK0,k1_xboole_0) | (~spl1_8 | spl1_18)),
% 0.21/0.47    inference(resolution,[],[f112,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) ) | ~spl1_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f57])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    spl1_8 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.47  fof(f112,plain,(
% 0.21/0.47    ~r1_xboole_0(k1_xboole_0,sK0) | spl1_18),
% 0.21/0.47    inference(avatar_component_clause,[],[f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    spl1_18 <=> r1_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    ~spl1_18 | spl1_1 | ~spl1_16),
% 0.21/0.47    inference(avatar_split_clause,[],[f105,f101,f29,f111])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    spl1_1 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    spl1_16 <=> ! [X3] : (~r1_xboole_0(k1_xboole_0,X3) | k1_xboole_0 = k9_relat_1(k1_xboole_0,X3))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    ~r1_xboole_0(k1_xboole_0,sK0) | (spl1_1 | ~spl1_16)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f104])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,sK0) | (spl1_1 | ~spl1_16)),
% 0.21/0.47    inference(superposition,[],[f30,f102])).
% 0.21/0.47  fof(f102,plain,(
% 0.21/0.47    ( ! [X3] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X3) | ~r1_xboole_0(k1_xboole_0,X3)) ) | ~spl1_16),
% 0.21/0.47    inference(avatar_component_clause,[],[f101])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f29])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl1_16 | ~spl1_3 | ~spl1_9 | ~spl1_15),
% 0.21/0.47    inference(avatar_split_clause,[],[f99,f94,f63,f37,f101])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    spl1_9 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl1_15 <=> ! [X1,X0] : (k1_xboole_0 = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ( ! [X3] : (~r1_xboole_0(k1_xboole_0,X3) | k1_xboole_0 = k9_relat_1(k1_xboole_0,X3)) ) | (~spl1_3 | ~spl1_9 | ~spl1_15)),
% 0.21/0.47    inference(forward_demodulation,[],[f98,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f37])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X3] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X3) | ~r1_xboole_0(k1_relat_1(k1_xboole_0),X3)) ) | (~spl1_9 | ~spl1_15)),
% 0.21/0.47    inference(resolution,[],[f95,f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    v1_relat_1(k1_xboole_0) | ~spl1_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f63])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_xboole_0 = k9_relat_1(X0,X1) | ~r1_xboole_0(k1_relat_1(X0),X1)) ) | ~spl1_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f94])).
% 0.21/0.47  fof(f96,plain,(
% 0.21/0.47    spl1_15 | ~spl1_4 | ~spl1_10 | ~spl1_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f84,f71,f67,f41,f94])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    spl1_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl1_10 <=> ! [X1,X0] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.47  fof(f71,plain,(
% 0.21/0.47    spl1_11 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.47  fof(f84,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1)) ) | (~spl1_4 | ~spl1_10 | ~spl1_11)),
% 0.21/0.47    inference(forward_demodulation,[],[f83,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f41])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_relat_1(k1_xboole_0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1)) ) | (~spl1_10 | ~spl1_11)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f82])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_relat_1(k1_xboole_0) = k9_relat_1(X0,X1) | ~v1_relat_1(X0) | ~r1_xboole_0(k1_relat_1(X0),X1) | ~v1_relat_1(X0)) ) | (~spl1_10 | ~spl1_11)),
% 0.21/0.47    inference(superposition,[],[f68,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl1_11),
% 0.21/0.47    inference(avatar_component_clause,[],[f71])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) ) | ~spl1_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f67])).
% 0.21/0.47  fof(f73,plain,(
% 0.21/0.47    spl1_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f20,f71])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    spl1_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f19,f67])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    spl1_9 | ~spl1_5 | ~spl1_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f60,f49,f45,f63])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    spl1_5 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    spl1_6 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    v1_relat_1(k1_xboole_0) | (~spl1_5 | ~spl1_6)),
% 0.21/0.47    inference(superposition,[],[f46,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) ) | ~spl1_6),
% 0.21/0.47    inference(avatar_component_clause,[],[f49])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl1_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f45])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    spl1_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f22,f57])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl1_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f26,f49])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    spl1_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f18,f45])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    spl1_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f16,f41])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    spl1_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f15,f37])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.47    inference(cnf_transformation,[],[f6])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    spl1_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f17,f33])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ~spl1_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f14,f29])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (4670)------------------------------
% 0.21/0.47  % (4670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (4670)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (4670)Memory used [KB]: 10618
% 0.21/0.47  % (4670)Time elapsed: 0.058 s
% 0.21/0.47  % (4670)------------------------------
% 0.21/0.47  % (4670)------------------------------
% 0.21/0.47  % (4665)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.47  % (4660)Success in time 0.112 s
%------------------------------------------------------------------------------
