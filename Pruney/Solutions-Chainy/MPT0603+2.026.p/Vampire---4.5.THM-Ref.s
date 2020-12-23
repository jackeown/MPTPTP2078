%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 125 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  209 ( 327 expanded)
%              Number of equality atoms :   30 (  53 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f53,f57,f61,f65,f77,f81,f97,f112,f117,f121,f154])).

fof(f154,plain,
    ( spl3_14
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | spl3_14
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f111,f151])).

fof(f151,plain,
    ( ! [X0] : v1_relat_1(k7_relat_1(sK2,X0))
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(superposition,[],[f116,f120])).

fof(f120,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_16
  <=> ! [X0] : k7_relat_1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f116,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK2,X0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl3_15
  <=> ! [X0] : v1_relat_1(k3_xboole_0(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f111,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl3_14
  <=> v1_relat_1(k7_relat_1(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f121,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f92,f79,f31,f119])).

fof(f31,plain,
    ( spl3_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f79,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f92,plain,
    ( ! [X0] : k7_relat_1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2)))
    | ~ spl3_1
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f33,f80])).

fof(f80,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
        | ~ v1_relat_1(X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f79])).

fof(f33,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f117,plain,
    ( spl3_15
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f84,f59,f55,f115])).

fof(f55,plain,
    ( spl3_6
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f59,plain,
    ( spl3_7
  <=> ! [X0] : v1_relat_1(k4_xboole_0(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f84,plain,
    ( ! [X0] : v1_relat_1(k3_xboole_0(sK2,X0))
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(superposition,[],[f60,f56])).

fof(f56,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f55])).

fof(f60,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK2,X0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f59])).

fof(f112,plain,
    ( ~ spl3_14
    | ~ spl3_2
    | spl3_3
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f100,f95,f75,f63,f41,f36,f109])).

fof(f36,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f41,plain,
    ( spl3_3
  <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f63,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f75,plain,
    ( spl3_10
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k1_xboole_0
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f95,plain,
    ( spl3_12
  <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f100,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ spl3_2
    | spl3_3
    | ~ spl3_8
    | ~ spl3_10
    | ~ spl3_12 ),
    inference(subsumption_resolution,[],[f91,f98])).

fof(f98,plain,
    ( r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
    | ~ spl3_2
    | ~ spl3_8
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f38,f96,f64])).

fof(f64,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f96,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f38,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f91,plain,
    ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_3
    | ~ spl3_10 ),
    inference(trivial_inequality_removal,[],[f86])).

fof(f86,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK0)),sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f43,f76])).

fof(f76,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = k1_xboole_0
        | ~ r1_xboole_0(k1_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f75])).

fof(f43,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f41])).

fof(f97,plain,
    ( spl3_12
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f66,f51,f31,f95])).

fof(f51,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f66,plain,
    ( ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)
    | ~ spl3_1
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f33,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f51])).

fof(f81,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f26,f79])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1)))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).

fof(f77,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f28,f75])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k7_relat_1(X1,X0) = k1_xboole_0
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k7_relat_1(X1,X0) != k1_xboole_0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k7_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f65,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f61,plain,
    ( spl3_7
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f49,f46,f31,f59])).

fof(f46,plain,
    ( spl3_4
  <=> ! [X1,X0] :
        ( v1_relat_1(k4_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f49,plain,
    ( ! [X0] : v1_relat_1(k4_xboole_0(sK2,X0))
    | ~ spl3_1
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f33,f47])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k4_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f46])).

fof(f57,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f23,f55])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f53,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f25,f51])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

fof(f48,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f24,f46])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f44,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f22,f41])).

fof(f22,plain,(
    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
    & r1_xboole_0(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
        & r1_xboole_0(X0,X1)
        & v1_relat_1(X2) )
   => ( k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)
      & r1_xboole_0(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1)
      & r1_xboole_0(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_xboole_0(X0,X1)
         => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f39,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f36])).

fof(f21,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f34,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f20,f31])).

fof(f20,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:31:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (7846)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (7848)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (7844)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (7846)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f155,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f34,f39,f44,f48,f53,f57,f61,f65,f77,f81,f97,f112,f117,f121,f154])).
% 0.22/0.47  fof(f154,plain,(
% 0.22/0.47    spl3_14 | ~spl3_15 | ~spl3_16),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f153])).
% 0.22/0.47  fof(f153,plain,(
% 0.22/0.47    $false | (spl3_14 | ~spl3_15 | ~spl3_16)),
% 0.22/0.47    inference(subsumption_resolution,[],[f111,f151])).
% 0.22/0.47  fof(f151,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k7_relat_1(sK2,X0))) ) | (~spl3_15 | ~spl3_16)),
% 0.22/0.47    inference(superposition,[],[f116,f120])).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    ( ! [X0] : (k7_relat_1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2)))) ) | ~spl3_16),
% 0.22/0.47    inference(avatar_component_clause,[],[f119])).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    spl3_16 <=> ! [X0] : k7_relat_1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK2,X0))) ) | ~spl3_15),
% 0.22/0.47    inference(avatar_component_clause,[],[f115])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    spl3_15 <=> ! [X0] : v1_relat_1(k3_xboole_0(sK2,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    ~v1_relat_1(k7_relat_1(sK2,sK0)) | spl3_14),
% 0.22/0.47    inference(avatar_component_clause,[],[f109])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    spl3_14 <=> v1_relat_1(k7_relat_1(sK2,sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.47  fof(f121,plain,(
% 0.22/0.47    spl3_16 | ~spl3_1 | ~spl3_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f92,f79,f31,f119])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    spl3_1 <=> v1_relat_1(sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    spl3_11 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    ( ! [X0] : (k7_relat_1(sK2,X0) = k3_xboole_0(sK2,k2_zfmisc_1(X0,k2_relat_1(sK2)))) ) | (~spl3_1 | ~spl3_11)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f33,f80])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1)) ) | ~spl3_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f79])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    v1_relat_1(sK2) | ~spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f31])).
% 0.22/0.47  fof(f117,plain,(
% 0.22/0.47    spl3_15 | ~spl3_6 | ~spl3_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f84,f59,f55,f115])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    spl3_6 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    spl3_7 <=> ! [X0] : v1_relat_1(k4_xboole_0(sK2,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k3_xboole_0(sK2,X0))) ) | (~spl3_6 | ~spl3_7)),
% 0.22/0.47    inference(superposition,[],[f60,f56])).
% 0.22/0.47  fof(f56,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) ) | ~spl3_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f55])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK2,X0))) ) | ~spl3_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f59])).
% 0.22/0.47  fof(f112,plain,(
% 0.22/0.47    ~spl3_14 | ~spl3_2 | spl3_3 | ~spl3_8 | ~spl3_10 | ~spl3_12),
% 0.22/0.47    inference(avatar_split_clause,[],[f100,f95,f75,f63,f41,f36,f109])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    spl3_2 <=> r1_xboole_0(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    spl3_3 <=> k1_xboole_0 = k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    spl3_8 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    spl3_10 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.47  fof(f95,plain,(
% 0.22/0.47    spl3_12 <=> ! [X0] : r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    ~v1_relat_1(k7_relat_1(sK2,sK0)) | (~spl3_2 | spl3_3 | ~spl3_8 | ~spl3_10 | ~spl3_12)),
% 0.22/0.47    inference(subsumption_resolution,[],[f91,f98])).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) | (~spl3_2 | ~spl3_8 | ~spl3_12)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f38,f96,f64])).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f63])).
% 0.22/0.47  fof(f96,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)) ) | ~spl3_12),
% 0.22/0.47    inference(avatar_component_clause,[],[f95])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    r1_xboole_0(sK0,sK1) | ~spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f36])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    ~r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | (spl3_3 | ~spl3_10)),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f86])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_relat_1(k7_relat_1(sK2,sK0)),sK1) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | (spl3_3 | ~spl3_10)),
% 0.22/0.47    inference(superposition,[],[f43,f76])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl3_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f75])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) | spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f41])).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    spl3_12 | ~spl3_1 | ~spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f66,f51,f31,f95])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    spl3_5 <=> ! [X1,X0] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f66,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(k1_relat_1(k7_relat_1(sK2,X0)),X0)) ) | (~spl3_1 | ~spl3_5)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f33,f52])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) ) | ~spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f51])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    spl3_11),
% 0.22/0.47    inference(avatar_split_clause,[],[f26,f79])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k3_xboole_0(X1,k2_zfmisc_1(X0,k2_relat_1(X1))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_relat_1)).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    spl3_10),
% 0.22/0.47    inference(avatar_split_clause,[],[f28,f75])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0,X1] : (((k7_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k7_relat_1(X1,X0) != k1_xboole_0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(nnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : ((k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k7_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.22/0.47  fof(f65,plain,(
% 0.22/0.47    spl3_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f29,f63])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(flattening,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    spl3_7 | ~spl3_1 | ~spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f49,f46,f31,f59])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    spl3_4 <=> ! [X1,X0] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X0] : (v1_relat_1(k4_xboole_0(sK2,X0))) ) | (~spl3_1 | ~spl3_4)),
% 0.22/0.47    inference(unit_resulting_resolution,[],[f33,f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl3_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f46])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    spl3_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f55])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    spl3_5),
% 0.22/0.47    inference(avatar_split_clause,[],[f25,f51])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f24,f46])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ~spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f22,f41])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2)) => (k1_xboole_0 != k7_relat_1(k7_relat_1(sK2,sK0),sK1) & r1_xboole_0(sK0,sK1) & v1_relat_1(sK2))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1) & v1_relat_1(X2))),
% 0.22/0.47    inference(flattening,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0,X1,X2] : ((k1_xboole_0 != k7_relat_1(k7_relat_1(X2,X0),X1) & r1_xboole_0(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f21,f36])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    r1_xboole_0(sK0,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f20,f31])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    v1_relat_1(sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (7846)------------------------------
% 0.22/0.47  % (7846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (7846)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (7846)Memory used [KB]: 6140
% 0.22/0.47  % (7846)Time elapsed: 0.054 s
% 0.22/0.47  % (7846)------------------------------
% 0.22/0.47  % (7846)------------------------------
% 0.22/0.47  % (7856)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.47  % (7851)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.47  % (7839)Success in time 0.113 s
%------------------------------------------------------------------------------
