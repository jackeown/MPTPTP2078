%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 118 expanded)
%              Number of leaves         :   21 (  54 expanded)
%              Depth                    :    6
%              Number of atoms          :  210 ( 329 expanded)
%              Number of equality atoms :   54 (  88 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f47,f55,f59,f63,f71,f77,f84,f93,f100,f125,f128])).

fof(f128,plain,
    ( ~ spl2_3
    | ~ spl2_6
    | spl2_19 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_6
    | spl2_19 ),
    inference(subsumption_resolution,[],[f126,f42])).

fof(f42,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f126,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_6
    | spl2_19 ),
    inference(resolution,[],[f124,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_6
  <=> ! [X1,X0] :
        ( v1_relat_1(k7_relat_1(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f124,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK1))
    | spl2_19 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl2_19
  <=> v1_relat_1(k7_relat_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f125,plain,
    ( ~ spl2_19
    | spl2_1
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f120,f97,f91,f30,f122])).

fof(f30,plain,
    ( spl2_1
  <=> k1_xboole_0 = k7_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f91,plain,
    ( spl2_14
  <=> ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK0,X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0)
        | ~ v1_relat_1(k7_relat_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f97,plain,
    ( spl2_15
  <=> k1_xboole_0 = k9_relat_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f120,plain,
    ( ~ v1_relat_1(k7_relat_1(sK0,sK1))
    | spl2_1
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f119,f32])).

fof(f32,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f119,plain,
    ( k1_xboole_0 = k7_relat_1(sK0,sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK1))
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(trivial_inequality_removal,[],[f118])).

fof(f118,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k7_relat_1(sK0,sK1)
    | ~ v1_relat_1(k7_relat_1(sK0,sK1))
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(superposition,[],[f92,f99])).

fof(f99,plain,
    ( k1_xboole_0 = k9_relat_1(sK0,sK1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f97])).

fof(f92,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK0,X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0)
        | ~ v1_relat_1(k7_relat_1(sK0,X0)) )
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f100,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f95,f74,f61,f40,f97])).

fof(f61,plain,
    ( spl2_8
  <=> ! [X1,X0] :
        ( k9_relat_1(X1,X0) = k1_xboole_0
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f74,plain,
    ( spl2_11
  <=> r1_xboole_0(k1_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f95,plain,
    ( k1_xboole_0 = k9_relat_1(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(subsumption_resolution,[],[f94,f42])).

fof(f94,plain,
    ( k1_xboole_0 = k9_relat_1(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | ~ spl2_8
    | ~ spl2_11 ),
    inference(resolution,[],[f62,f76])).

fof(f76,plain,
    ( r1_xboole_0(k1_relat_1(sK0),sK1)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f74])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k9_relat_1(X1,X0) = k1_xboole_0
        | ~ v1_relat_1(X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f93,plain,
    ( spl2_14
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f89,f82,f45,f91])).

fof(f45,plain,
    ( spl2_4
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | k1_xboole_0 != k2_relat_1(X0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f82,plain,
    ( spl2_12
  <=> ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f89,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK0,X0)
        | k1_xboole_0 = k7_relat_1(sK0,X0)
        | ~ v1_relat_1(k7_relat_1(sK0,X0)) )
    | ~ spl2_4
    | ~ spl2_12 ),
    inference(superposition,[],[f46,f83])).

fof(f83,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f82])).

fof(f46,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k2_relat_1(X0)
        | k1_xboole_0 = X0
        | ~ v1_relat_1(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f84,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f79,f57,f40,f82])).

fof(f57,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f79,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)
    | ~ spl2_3
    | ~ spl2_7 ),
    inference(resolution,[],[f58,f42])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f57])).

fof(f77,plain,
    ( spl2_11
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f72,f69,f35,f74])).

fof(f35,plain,
    ( spl2_2
  <=> r1_xboole_0(sK1,k1_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f69,plain,
    ( spl2_10
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f72,plain,
    ( r1_xboole_0(k1_relat_1(sK0),sK1)
    | ~ spl2_2
    | ~ spl2_10 ),
    inference(resolution,[],[f70,f37])).

fof(f37,plain,
    ( r1_xboole_0(sK1,k1_relat_1(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f71,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f28,f69])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f63,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ( k9_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k9_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f59,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f25,f57])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f55,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f47,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f45])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

fof(f43,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f19,f40])).

fof(f19,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( k1_xboole_0 != k7_relat_1(sK0,sK1)
    & r1_xboole_0(sK1,k1_relat_1(sK0))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k7_relat_1(X0,X1) != k1_xboole_0
            & r1_xboole_0(X1,k1_relat_1(X0)) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k1_xboole_0 != k7_relat_1(sK0,X1)
          & r1_xboole_0(X1,k1_relat_1(sK0)) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( k1_xboole_0 != k7_relat_1(sK0,X1)
        & r1_xboole_0(X1,k1_relat_1(sK0)) )
   => ( k1_xboole_0 != k7_relat_1(sK0,sK1)
      & r1_xboole_0(sK1,k1_relat_1(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k7_relat_1(X0,X1) != k1_xboole_0
          & r1_xboole_0(X1,k1_relat_1(X0)) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( r1_xboole_0(X1,k1_relat_1(X0))
           => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k7_relat_1(X0,X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f38,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f20,f35])).

fof(f20,plain,(
    r1_xboole_0(sK1,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f33,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f21,f30])).

fof(f21,plain,(
    k1_xboole_0 != k7_relat_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:53:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (7805)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.20/0.43  % (7805)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f129,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f33,f38,f43,f47,f55,f59,f63,f71,f77,f84,f93,f100,f125,f128])).
% 0.20/0.43  fof(f128,plain,(
% 0.20/0.43    ~spl2_3 | ~spl2_6 | spl2_19),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f127])).
% 0.20/0.43  fof(f127,plain,(
% 0.20/0.43    $false | (~spl2_3 | ~spl2_6 | spl2_19)),
% 0.20/0.43    inference(subsumption_resolution,[],[f126,f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    v1_relat_1(sK0) | ~spl2_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    spl2_3 <=> v1_relat_1(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.43  fof(f126,plain,(
% 0.20/0.43    ~v1_relat_1(sK0) | (~spl2_6 | spl2_19)),
% 0.20/0.43    inference(resolution,[],[f124,f54])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f53])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    spl2_6 <=> ! [X1,X0] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.43  fof(f124,plain,(
% 0.20/0.43    ~v1_relat_1(k7_relat_1(sK0,sK1)) | spl2_19),
% 0.20/0.43    inference(avatar_component_clause,[],[f122])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    spl2_19 <=> v1_relat_1(k7_relat_1(sK0,sK1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.20/0.43  fof(f125,plain,(
% 0.20/0.43    ~spl2_19 | spl2_1 | ~spl2_14 | ~spl2_15),
% 0.20/0.43    inference(avatar_split_clause,[],[f120,f97,f91,f30,f122])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    spl2_1 <=> k1_xboole_0 = k7_relat_1(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    spl2_14 <=> ! [X0] : (k1_xboole_0 != k9_relat_1(sK0,X0) | k1_xboole_0 = k7_relat_1(sK0,X0) | ~v1_relat_1(k7_relat_1(sK0,X0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    spl2_15 <=> k1_xboole_0 = k9_relat_1(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.43  fof(f120,plain,(
% 0.20/0.43    ~v1_relat_1(k7_relat_1(sK0,sK1)) | (spl2_1 | ~spl2_14 | ~spl2_15)),
% 0.20/0.43    inference(subsumption_resolution,[],[f119,f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    k1_xboole_0 != k7_relat_1(sK0,sK1) | spl2_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f30])).
% 0.20/0.43  fof(f119,plain,(
% 0.20/0.43    k1_xboole_0 = k7_relat_1(sK0,sK1) | ~v1_relat_1(k7_relat_1(sK0,sK1)) | (~spl2_14 | ~spl2_15)),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f118])).
% 0.20/0.43  fof(f118,plain,(
% 0.20/0.43    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k7_relat_1(sK0,sK1) | ~v1_relat_1(k7_relat_1(sK0,sK1)) | (~spl2_14 | ~spl2_15)),
% 0.20/0.43    inference(superposition,[],[f92,f99])).
% 0.20/0.43  fof(f99,plain,(
% 0.20/0.43    k1_xboole_0 = k9_relat_1(sK0,sK1) | ~spl2_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f97])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK0,X0) | k1_xboole_0 = k7_relat_1(sK0,X0) | ~v1_relat_1(k7_relat_1(sK0,X0))) ) | ~spl2_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f91])).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    spl2_15 | ~spl2_3 | ~spl2_8 | ~spl2_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f95,f74,f61,f40,f97])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    spl2_8 <=> ! [X1,X0] : (k9_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    spl2_11 <=> r1_xboole_0(k1_relat_1(sK0),sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.43  fof(f95,plain,(
% 0.20/0.43    k1_xboole_0 = k9_relat_1(sK0,sK1) | (~spl2_3 | ~spl2_8 | ~spl2_11)),
% 0.20/0.43    inference(subsumption_resolution,[],[f94,f42])).
% 0.20/0.43  fof(f94,plain,(
% 0.20/0.43    k1_xboole_0 = k9_relat_1(sK0,sK1) | ~v1_relat_1(sK0) | (~spl2_8 | ~spl2_11)),
% 0.20/0.43    inference(resolution,[],[f62,f76])).
% 0.20/0.43  fof(f76,plain,(
% 0.20/0.43    r1_xboole_0(k1_relat_1(sK0),sK1) | ~spl2_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f74])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) = k1_xboole_0 | ~v1_relat_1(X1)) ) | ~spl2_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f61])).
% 0.20/0.43  fof(f93,plain,(
% 0.20/0.43    spl2_14 | ~spl2_4 | ~spl2_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f89,f82,f45,f91])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    spl2_4 <=> ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    spl2_12 <=> ! [X0] : k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK0,X0) | k1_xboole_0 = k7_relat_1(sK0,X0) | ~v1_relat_1(k7_relat_1(sK0,X0))) ) | (~spl2_4 | ~spl2_12)),
% 0.20/0.43    inference(superposition,[],[f46,f83])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) ) | ~spl2_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f82])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = X0 | ~v1_relat_1(X0)) ) | ~spl2_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f45])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    spl2_12 | ~spl2_3 | ~spl2_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f79,f57,f40,f82])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    spl2_7 <=> ! [X1,X0] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    ( ! [X0] : (k2_relat_1(k7_relat_1(sK0,X0)) = k9_relat_1(sK0,X0)) ) | (~spl2_3 | ~spl2_7)),
% 0.20/0.43    inference(resolution,[],[f58,f42])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) ) | ~spl2_7),
% 0.20/0.43    inference(avatar_component_clause,[],[f57])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    spl2_11 | ~spl2_2 | ~spl2_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f72,f69,f35,f74])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    spl2_2 <=> r1_xboole_0(sK1,k1_relat_1(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    spl2_10 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    r1_xboole_0(k1_relat_1(sK0),sK1) | (~spl2_2 | ~spl2_10)),
% 0.20/0.43    inference(resolution,[],[f70,f37])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    r1_xboole_0(sK1,k1_relat_1(sK0)) | ~spl2_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f35])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl2_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f69])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl2_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f28,f69])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    spl2_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f27,f61])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X0,X1] : (((k9_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k9_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(nnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1] : ((k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => (k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    spl2_7),
% 0.20/0.43    inference(avatar_split_clause,[],[f25,f57])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    spl2_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f24,f53])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    spl2_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f23,f45])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(flattening,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    spl2_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f19,f40])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    v1_relat_1(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    (k1_xboole_0 != k7_relat_1(sK0,sK1) & r1_xboole_0(sK1,k1_relat_1(sK0))) & v1_relat_1(sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f16,f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (k7_relat_1(X0,X1) != k1_xboole_0 & r1_xboole_0(X1,k1_relat_1(X0))) & v1_relat_1(X0)) => (? [X1] : (k1_xboole_0 != k7_relat_1(sK0,X1) & r1_xboole_0(X1,k1_relat_1(sK0))) & v1_relat_1(sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ? [X1] : (k1_xboole_0 != k7_relat_1(sK0,X1) & r1_xboole_0(X1,k1_relat_1(sK0))) => (k1_xboole_0 != k7_relat_1(sK0,sK1) & r1_xboole_0(sK1,k1_relat_1(sK0)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : (k7_relat_1(X0,X1) != k1_xboole_0 & r1_xboole_0(X1,k1_relat_1(X0))) & v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,negated_conjecture,(
% 0.20/0.43    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k7_relat_1(X0,X1) = k1_xboole_0))),
% 0.20/0.43    inference(negated_conjecture,[],[f6])).
% 0.20/0.43  fof(f6,conjecture,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k7_relat_1(X0,X1) = k1_xboole_0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    spl2_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f20,f35])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    r1_xboole_0(sK1,k1_relat_1(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ~spl2_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f21,f30])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    k1_xboole_0 != k7_relat_1(sK0,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (7805)------------------------------
% 0.20/0.43  % (7805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (7805)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (7805)Memory used [KB]: 6140
% 0.20/0.43  % (7805)Time elapsed: 0.030 s
% 0.20/0.43  % (7805)------------------------------
% 0.20/0.43  % (7805)------------------------------
% 0.20/0.44  % (7793)Success in time 0.086 s
%------------------------------------------------------------------------------
