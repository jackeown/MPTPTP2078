%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 115 expanded)
%              Number of leaves         :   20 (  54 expanded)
%              Depth                    :    6
%              Number of atoms          :  196 ( 322 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f108,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f43,f47,f51,f55,f59,f73,f89,f98,f101,f107])).

fof(f107,plain,
    ( ~ spl2_3
    | ~ spl2_7
    | spl2_13 ),
    inference(avatar_contradiction_clause,[],[f106])).

fof(f106,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_7
    | spl2_13 ),
    inference(subsumption_resolution,[],[f103,f38])).

fof(f38,plain,
    ( v1_relat_1(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl2_3
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f103,plain,
    ( ~ v1_relat_1(sK0)
    | ~ spl2_7
    | spl2_13 ),
    inference(resolution,[],[f97,f54])).

fof(f54,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( v1_relat_1(k3_xboole_0(X0,X1))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f97,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_13
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f101,plain,
    ( ~ spl2_13
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_10
    | spl2_12 ),
    inference(avatar_split_clause,[],[f100,f86,f69,f41,f31,f95])).

fof(f31,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f41,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f69,plain,
    ( spl2_10
  <=> ! [X3,X2] : r1_tarski(k3_xboole_0(X3,X2),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f86,plain,
    ( spl2_12
  <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f100,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_2
    | ~ spl2_4
    | ~ spl2_10
    | spl2_12 ),
    inference(subsumption_resolution,[],[f99,f33])).

fof(f33,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f99,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_10
    | spl2_12 ),
    inference(subsumption_resolution,[],[f91,f70])).

fof(f70,plain,
    ( ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f69])).

fof(f91,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_4
    | spl2_12 ),
    inference(resolution,[],[f42,f88])).

fof(f88,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))
    | spl2_12 ),
    inference(avatar_component_clause,[],[f86])).

fof(f42,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
        | ~ r1_tarski(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f98,plain,
    ( ~ spl2_13
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_11 ),
    inference(avatar_split_clause,[],[f93,f82,f45,f41,f36,f95])).

fof(f45,plain,
    ( spl2_5
  <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f82,plain,
    ( spl2_11
  <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f93,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_11 ),
    inference(subsumption_resolution,[],[f92,f38])).

fof(f92,plain,
    ( ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_5
    | spl2_11 ),
    inference(subsumption_resolution,[],[f90,f46])).

fof(f46,plain,
    ( ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f90,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ v1_relat_1(sK0)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_4
    | spl2_11 ),
    inference(resolution,[],[f42,f84])).

fof(f84,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f82])).

fof(f89,plain,
    ( ~ spl2_11
    | ~ spl2_12
    | spl2_1
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f78,f57,f26,f86,f82])).

fof(f26,plain,
    ( spl2_1
  <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f57,plain,
    ( spl2_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f78,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))
    | spl2_1
    | ~ spl2_8 ),
    inference(resolution,[],[f58,f28])).

fof(f28,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f58,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f73,plain,
    ( spl2_10
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f63,f49,f45,f69])).

fof(f49,plain,
    ( spl2_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f63,plain,
    ( ! [X2,X3] : r1_tarski(k3_xboole_0(X3,X2),X2)
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(superposition,[],[f46,f50])).

fof(f50,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f49])).

fof(f59,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f24,f57])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f55,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f23,f53])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f51,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f22,f49])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f47,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f21,f45])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f43,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f20,f41])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f39,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f36])).

fof(f17,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
    & v1_relat_1(sK1)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1)))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

fof(f34,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f18,f31])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f29,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f19,f26])).

fof(f19,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:53:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.41  % (8188)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.41  % (8186)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (8191)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.41  % (8191)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f108,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f29,f34,f39,f43,f47,f51,f55,f59,f73,f89,f98,f101,f107])).
% 0.21/0.41  fof(f107,plain,(
% 0.21/0.41    ~spl2_3 | ~spl2_7 | spl2_13),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f106])).
% 0.21/0.41  fof(f106,plain,(
% 0.21/0.41    $false | (~spl2_3 | ~spl2_7 | spl2_13)),
% 0.21/0.41    inference(subsumption_resolution,[],[f103,f38])).
% 0.21/0.41  fof(f38,plain,(
% 0.21/0.41    v1_relat_1(sK0) | ~spl2_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f36])).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    spl2_3 <=> v1_relat_1(sK0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.41  fof(f103,plain,(
% 0.21/0.41    ~v1_relat_1(sK0) | (~spl2_7 | spl2_13)),
% 0.21/0.41    inference(resolution,[],[f97,f54])).
% 0.21/0.41  fof(f54,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) ) | ~spl2_7),
% 0.21/0.41    inference(avatar_component_clause,[],[f53])).
% 0.21/0.41  fof(f53,plain,(
% 0.21/0.41    spl2_7 <=> ! [X1,X0] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.41  fof(f97,plain,(
% 0.21/0.41    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_13),
% 0.21/0.41    inference(avatar_component_clause,[],[f95])).
% 0.21/0.41  fof(f95,plain,(
% 0.21/0.41    spl2_13 <=> v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.41  fof(f101,plain,(
% 0.21/0.41    ~spl2_13 | ~spl2_2 | ~spl2_4 | ~spl2_10 | spl2_12),
% 0.21/0.41    inference(avatar_split_clause,[],[f100,f86,f69,f41,f31,f95])).
% 0.21/0.41  fof(f31,plain,(
% 0.21/0.41    spl2_2 <=> v1_relat_1(sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.41  fof(f41,plain,(
% 0.21/0.41    spl2_4 <=> ! [X1,X0] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.41  fof(f69,plain,(
% 0.21/0.41    spl2_10 <=> ! [X3,X2] : r1_tarski(k3_xboole_0(X3,X2),X2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.41  fof(f86,plain,(
% 0.21/0.41    spl2_12 <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.41  fof(f100,plain,(
% 0.21/0.41    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_2 | ~spl2_4 | ~spl2_10 | spl2_12)),
% 0.21/0.41    inference(subsumption_resolution,[],[f99,f33])).
% 0.21/0.41  fof(f33,plain,(
% 0.21/0.41    v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f31])).
% 0.21/0.41  fof(f99,plain,(
% 0.21/0.41    ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_4 | ~spl2_10 | spl2_12)),
% 0.21/0.41    inference(subsumption_resolution,[],[f91,f70])).
% 0.21/0.41  fof(f70,plain,(
% 0.21/0.41    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X3,X2),X2)) ) | ~spl2_10),
% 0.21/0.41    inference(avatar_component_clause,[],[f69])).
% 0.21/0.41  fof(f91,plain,(
% 0.21/0.41    ~r1_tarski(k3_xboole_0(sK0,sK1),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_4 | spl2_12)),
% 0.21/0.41    inference(resolution,[],[f42,f88])).
% 0.21/0.41  fof(f88,plain,(
% 0.21/0.41    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) | spl2_12),
% 0.21/0.41    inference(avatar_component_clause,[],[f86])).
% 0.21/0.41  fof(f42,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl2_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f41])).
% 0.21/0.41  fof(f98,plain,(
% 0.21/0.41    ~spl2_13 | ~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_11),
% 0.21/0.41    inference(avatar_split_clause,[],[f93,f82,f45,f41,f36,f95])).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    spl2_5 <=> ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.41  fof(f82,plain,(
% 0.21/0.41    spl2_11 <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.41  fof(f93,plain,(
% 0.21/0.41    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_3 | ~spl2_4 | ~spl2_5 | spl2_11)),
% 0.21/0.41    inference(subsumption_resolution,[],[f92,f38])).
% 0.21/0.41  fof(f92,plain,(
% 0.21/0.41    ~v1_relat_1(sK0) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_4 | ~spl2_5 | spl2_11)),
% 0.21/0.41    inference(subsumption_resolution,[],[f90,f46])).
% 0.21/0.41  fof(f46,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) ) | ~spl2_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f45])).
% 0.21/0.41  fof(f90,plain,(
% 0.21/0.41    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | ~v1_relat_1(sK0) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | (~spl2_4 | spl2_11)),
% 0.21/0.41    inference(resolution,[],[f42,f84])).
% 0.21/0.41  fof(f84,plain,(
% 0.21/0.41    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) | spl2_11),
% 0.21/0.41    inference(avatar_component_clause,[],[f82])).
% 0.21/0.41  fof(f89,plain,(
% 0.21/0.41    ~spl2_11 | ~spl2_12 | spl2_1 | ~spl2_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f78,f57,f26,f86,f82])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    spl2_1 <=> r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.41  fof(f57,plain,(
% 0.21/0.41    spl2_8 <=> ! [X1,X0,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.41  fof(f78,plain,(
% 0.21/0.41    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK1)) | ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_relat_1(sK0)) | (spl2_1 | ~spl2_8)),
% 0.21/0.41    inference(resolution,[],[f58,f28])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) | spl2_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f26])).
% 0.21/0.41  fof(f58,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl2_8),
% 0.21/0.41    inference(avatar_component_clause,[],[f57])).
% 0.21/0.41  fof(f73,plain,(
% 0.21/0.41    spl2_10 | ~spl2_5 | ~spl2_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f63,f49,f45,f69])).
% 0.21/0.41  fof(f49,plain,(
% 0.21/0.41    spl2_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.41  fof(f63,plain,(
% 0.21/0.41    ( ! [X2,X3] : (r1_tarski(k3_xboole_0(X3,X2),X2)) ) | (~spl2_5 | ~spl2_6)),
% 0.21/0.41    inference(superposition,[],[f46,f50])).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_6),
% 0.21/0.41    inference(avatar_component_clause,[],[f49])).
% 0.21/0.41  fof(f59,plain,(
% 0.21/0.41    spl2_8),
% 0.21/0.41    inference(avatar_split_clause,[],[f24,f57])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.41    inference(flattening,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.41  fof(f55,plain,(
% 0.21/0.41    spl2_7),
% 0.21/0.41    inference(avatar_split_clause,[],[f23,f53])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.21/0.41  fof(f51,plain,(
% 0.21/0.41    spl2_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f22,f49])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.41  fof(f47,plain,(
% 0.21/0.41    spl2_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f21,f45])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.41  fof(f43,plain,(
% 0.21/0.41    spl2_4),
% 0.21/0.41    inference(avatar_split_clause,[],[f20,f41])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(flattening,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : ((r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 0.21/0.41  fof(f39,plain,(
% 0.21/0.41    spl2_3),
% 0.21/0.41    inference(avatar_split_clause,[],[f17,f36])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    v1_relat_1(sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1)) & v1_relat_1(sK0)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f15,f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(sK0))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,X1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(X1))) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.41    inference(ennf_transformation,[],[f7])).
% 0.21/0.41  fof(f7,negated_conjecture,(
% 0.21/0.41    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.41    inference(negated_conjecture,[],[f6])).
% 0.21/0.41  fof(f6,conjecture,(
% 0.21/0.41    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k3_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).
% 0.21/0.41  fof(f34,plain,(
% 0.21/0.41    spl2_2),
% 0.21/0.41    inference(avatar_split_clause,[],[f18,f31])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    v1_relat_1(sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f16])).
% 0.21/0.41  fof(f29,plain,(
% 0.21/0.41    ~spl2_1),
% 0.21/0.41    inference(avatar_split_clause,[],[f19,f26])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ~r1_tarski(k3_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k3_relat_1(sK0),k3_relat_1(sK1)))),
% 0.21/0.41    inference(cnf_transformation,[],[f16])).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (8191)------------------------------
% 0.21/0.41  % (8191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (8191)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (8191)Memory used [KB]: 6140
% 0.21/0.41  % (8191)Time elapsed: 0.005 s
% 0.21/0.41  % (8191)------------------------------
% 0.21/0.41  % (8191)------------------------------
% 0.21/0.42  % (8180)Success in time 0.062 s
%------------------------------------------------------------------------------
