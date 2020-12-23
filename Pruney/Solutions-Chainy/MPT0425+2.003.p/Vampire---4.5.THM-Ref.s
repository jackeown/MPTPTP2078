%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 112 expanded)
%              Number of leaves         :   20 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :  198 ( 332 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f38,f42,f46,f50,f54,f58,f63,f71,f81,f88,f93,f96])).

fof(f96,plain,
    ( spl4_1
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | spl4_1
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f94,f28])).

fof(f28,plain,
    ( ~ r1_tarski(sK2,k3_tarski(sK0))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl4_1
  <=> r1_tarski(sK2,k3_tarski(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f94,plain,
    ( r1_tarski(sK2,k3_tarski(sK0))
    | ~ spl4_3
    | ~ spl4_14 ),
    inference(resolution,[],[f92,f37])).

fof(f37,plain,
    ( r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_3
  <=> r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f92,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k3_tarski(k2_xboole_0(X0,sK1)))
        | r1_tarski(sK2,k3_tarski(X0)) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_14
  <=> ! [X0] :
        ( ~ r1_tarski(sK2,k3_tarski(k2_xboole_0(X0,sK1)))
        | r1_tarski(sK2,k3_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f93,plain,
    ( spl4_14
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f89,f86,f78,f91])).

fof(f78,plain,
    ( spl4_12
  <=> r1_xboole_0(sK2,k3_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f86,plain,
    ( spl4_13
  <=> ! [X1,X0,X2] :
        ( ~ r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))
        | ~ r1_xboole_0(X2,k3_tarski(X1))
        | r1_tarski(X2,k3_tarski(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK2,k3_tarski(k2_xboole_0(X0,sK1)))
        | r1_tarski(sK2,k3_tarski(X0)) )
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(resolution,[],[f87,f80])).

fof(f80,plain,
    ( r1_xboole_0(sK2,k3_tarski(sK1))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f78])).

fof(f87,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X2,k3_tarski(X1))
        | ~ r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))
        | r1_tarski(X2,k3_tarski(X0)) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f86])).

fof(f88,plain,
    ( spl4_13
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f84,f56,f40,f86])).

fof(f40,plain,
    ( spl4_4
  <=> ! [X1,X0] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f56,plain,
    ( spl4_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X1)
        | ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f84,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))
        | ~ r1_xboole_0(X2,k3_tarski(X1))
        | r1_tarski(X2,k3_tarski(X0)) )
    | ~ spl4_4
    | ~ spl4_8 ),
    inference(superposition,[],[f57,f41])).

fof(f41,plain,
    ( ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f57,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,X2)
        | r1_tarski(X0,X1) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f81,plain,
    ( spl4_12
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f76,f68,f44,f78])).

fof(f44,plain,
    ( spl4_5
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f68,plain,
    ( spl4_10
  <=> r1_xboole_0(k3_tarski(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f76,plain,
    ( r1_xboole_0(sK2,k3_tarski(sK1))
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(resolution,[],[f70,f45])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f70,plain,
    ( r1_xboole_0(k3_tarski(sK1),sK2)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f68])).

fof(f71,plain,
    ( spl4_10
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f66,f61,f48,f68])).

fof(f48,plain,
    ( spl4_6
  <=> ! [X1,X0] :
        ( r1_xboole_0(k3_tarski(X0),X1)
        | ~ r1_xboole_0(sK3(X0,X1),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f61,plain,
    ( spl4_9
  <=> ! [X0] :
        ( r1_xboole_0(k3_tarski(sK1),X0)
        | r1_xboole_0(sK3(sK1,X0),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f66,plain,
    ( r1_xboole_0(k3_tarski(sK1),sK2)
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,
    ( r1_xboole_0(k3_tarski(sK1),sK2)
    | r1_xboole_0(k3_tarski(sK1),sK2)
    | ~ spl4_6
    | ~ spl4_9 ),
    inference(resolution,[],[f62,f49])).

fof(f49,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(sK3(X0,X1),X1)
        | r1_xboole_0(k3_tarski(X0),X1) )
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f48])).

fof(f62,plain,
    ( ! [X0] :
        ( r1_xboole_0(sK3(sK1,X0),sK2)
        | r1_xboole_0(k3_tarski(sK1),X0) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f63,plain,
    ( spl4_9
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f59,f52,f31,f61])).

fof(f31,plain,
    ( spl4_2
  <=> ! [X3] :
        ( r1_xboole_0(X3,sK2)
        | ~ r2_hidden(X3,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f52,plain,
    ( spl4_7
  <=> ! [X1,X0] :
        ( r1_xboole_0(k3_tarski(X0),X1)
        | r2_hidden(sK3(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f59,plain,
    ( ! [X0] :
        ( r1_xboole_0(k3_tarski(sK1),X0)
        | r1_xboole_0(sK3(sK1,X0),sK2) )
    | ~ spl4_2
    | ~ spl4_7 ),
    inference(resolution,[],[f53,f32])).

fof(f32,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK1)
        | r1_xboole_0(X3,sK2) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f53,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X0)
        | r1_xboole_0(k3_tarski(X0),X1) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f52])).

fof(f58,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f54,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f22,f52])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ( ~ r1_xboole_0(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r1_xboole_0(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_xboole_0(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_xboole_0(X2,X1) )
     => r1_xboole_0(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).

fof(f50,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k3_tarski(X0),X1)
      | ~ r1_xboole_0(sK3(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f46,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f42,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f20,f40])).

fof(f20,plain,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).

fof(f38,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(sK2,k3_tarski(sK0))
    & ! [X3] :
        ( r1_xboole_0(X3,sK2)
        | ~ r2_hidden(X3,sK1) )
    & r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X2,k3_tarski(X0))
        & ! [X3] :
            ( r1_xboole_0(X3,X2)
            | ~ r2_hidden(X3,X1) )
        & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
   => ( ~ r1_tarski(sK2,k3_tarski(sK0))
      & ! [X3] :
          ( r1_xboole_0(X3,sK2)
          | ~ r2_hidden(X3,sK1) )
      & r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,k3_tarski(X0))
      & ! [X3] :
          ( r1_xboole_0(X3,X2)
          | ~ r2_hidden(X3,X1) )
      & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X2,k3_tarski(X0))
      & ! [X3] :
          ( r1_xboole_0(X3,X2)
          | ~ r2_hidden(X3,X1) )
      & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( ! [X3] :
              ( r2_hidden(X3,X1)
             => r1_xboole_0(X3,X2) )
          & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
       => r1_tarski(X2,k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( r2_hidden(X3,X1)
           => r1_xboole_0(X3,X2) )
        & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) )
     => r1_tarski(X2,k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_setfam_1)).

fof(f33,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f18,f31])).

fof(f18,plain,(
    ! [X3] :
      ( r1_xboole_0(X3,sK2)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f29,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f19,f26])).

fof(f19,plain,(
    ~ r1_tarski(sK2,k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (8681)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.41  % (8680)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.41  % (8681)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f97,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f29,f33,f38,f42,f46,f50,f54,f58,f63,f71,f81,f88,f93,f96])).
% 0.21/0.41  fof(f96,plain,(
% 0.21/0.41    spl4_1 | ~spl4_3 | ~spl4_14),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f95])).
% 0.21/0.41  fof(f95,plain,(
% 0.21/0.41    $false | (spl4_1 | ~spl4_3 | ~spl4_14)),
% 0.21/0.41    inference(subsumption_resolution,[],[f94,f28])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ~r1_tarski(sK2,k3_tarski(sK0)) | spl4_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    spl4_1 <=> r1_tarski(sK2,k3_tarski(sK0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    r1_tarski(sK2,k3_tarski(sK0)) | (~spl4_3 | ~spl4_14)),
% 0.21/0.42    inference(resolution,[],[f92,f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))) | ~spl4_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl4_3 <=> r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.42  fof(f92,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(sK2,k3_tarski(k2_xboole_0(X0,sK1))) | r1_tarski(sK2,k3_tarski(X0))) ) | ~spl4_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f91])).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    spl4_14 <=> ! [X0] : (~r1_tarski(sK2,k3_tarski(k2_xboole_0(X0,sK1))) | r1_tarski(sK2,k3_tarski(X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    spl4_14 | ~spl4_12 | ~spl4_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f89,f86,f78,f91])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl4_12 <=> r1_xboole_0(sK2,k3_tarski(sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    spl4_13 <=> ! [X1,X0,X2] : (~r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) | ~r1_xboole_0(X2,k3_tarski(X1)) | r1_tarski(X2,k3_tarski(X0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    ( ! [X0] : (~r1_tarski(sK2,k3_tarski(k2_xboole_0(X0,sK1))) | r1_tarski(sK2,k3_tarski(X0))) ) | (~spl4_12 | ~spl4_13)),
% 0.21/0.42    inference(resolution,[],[f87,f80])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    r1_xboole_0(sK2,k3_tarski(sK1)) | ~spl4_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f78])).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X2,k3_tarski(X1)) | ~r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) | r1_tarski(X2,k3_tarski(X0))) ) | ~spl4_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f86])).
% 0.21/0.42  fof(f88,plain,(
% 0.21/0.42    spl4_13 | ~spl4_4 | ~spl4_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f84,f56,f40,f86])).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl4_4 <=> ! [X1,X0] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl4_8 <=> ! [X1,X0,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))) | ~r1_xboole_0(X2,k3_tarski(X1)) | r1_tarski(X2,k3_tarski(X0))) ) | (~spl4_4 | ~spl4_8)),
% 0.21/0.42    inference(superposition,[],[f57,f41])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) ) | ~spl4_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f40])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,X1)) ) | ~spl4_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f56])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    spl4_12 | ~spl4_5 | ~spl4_10),
% 0.21/0.42    inference(avatar_split_clause,[],[f76,f68,f44,f78])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    spl4_5 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl4_10 <=> r1_xboole_0(k3_tarski(sK1),sK2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    r1_xboole_0(sK2,k3_tarski(sK1)) | (~spl4_5 | ~spl4_10)),
% 0.21/0.42    inference(resolution,[],[f70,f45])).
% 0.21/0.42  fof(f45,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl4_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f44])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    r1_xboole_0(k3_tarski(sK1),sK2) | ~spl4_10),
% 0.21/0.42    inference(avatar_component_clause,[],[f68])).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    spl4_10 | ~spl4_6 | ~spl4_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f66,f61,f48,f68])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl4_6 <=> ! [X1,X0] : (r1_xboole_0(k3_tarski(X0),X1) | ~r1_xboole_0(sK3(X0,X1),X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    spl4_9 <=> ! [X0] : (r1_xboole_0(k3_tarski(sK1),X0) | r1_xboole_0(sK3(sK1,X0),sK2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    r1_xboole_0(k3_tarski(sK1),sK2) | (~spl4_6 | ~spl4_9)),
% 0.21/0.42    inference(duplicate_literal_removal,[],[f64])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    r1_xboole_0(k3_tarski(sK1),sK2) | r1_xboole_0(k3_tarski(sK1),sK2) | (~spl4_6 | ~spl4_9)),
% 0.21/0.42    inference(resolution,[],[f62,f49])).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(sK3(X0,X1),X1) | r1_xboole_0(k3_tarski(X0),X1)) ) | ~spl4_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f48])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(sK3(sK1,X0),sK2) | r1_xboole_0(k3_tarski(sK1),X0)) ) | ~spl4_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f61])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl4_9 | ~spl4_2 | ~spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f59,f52,f31,f61])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    spl4_2 <=> ! [X3] : (r1_xboole_0(X3,sK2) | ~r2_hidden(X3,sK1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.42  fof(f52,plain,(
% 0.21/0.42    spl4_7 <=> ! [X1,X0] : (r1_xboole_0(k3_tarski(X0),X1) | r2_hidden(sK3(X0,X1),X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(k3_tarski(sK1),X0) | r1_xboole_0(sK3(sK1,X0),sK2)) ) | (~spl4_2 | ~spl4_7)),
% 0.21/0.42    inference(resolution,[],[f53,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ( ! [X3] : (~r2_hidden(X3,sK1) | r1_xboole_0(X3,sK2)) ) | ~spl4_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f31])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_xboole_0(k3_tarski(X0),X1)) ) | ~spl4_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f52])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl4_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f56])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.42    inference(flattening,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.42    inference(ennf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    spl4_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f22,f52])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | (~r1_xboole_0(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f15])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X1,X0] : (? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)) => (~r1_xboole_0(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ? [X2] : (~r1_xboole_0(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_xboole_0(X2,X1)) => r1_xboole_0(k3_tarski(X0),X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_zfmisc_1)).
% 0.21/0.42  fof(f50,plain,(
% 0.21/0.42    spl4_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f23,f48])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(k3_tarski(X0),X1) | ~r1_xboole_0(sK3(X0,X1),X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl4_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f44])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl4_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f40])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : k3_tarski(k2_xboole_0(X0,X1)) = k2_xboole_0(k3_tarski(X0),k3_tarski(X1))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_zfmisc_1)).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f35])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1)))),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ~r1_tarski(sK2,k3_tarski(sK0)) & ! [X3] : (r1_xboole_0(X3,sK2) | ~r2_hidden(X3,sK1)) & r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1)))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (~r1_tarski(X2,k3_tarski(X0)) & ! [X3] : (r1_xboole_0(X3,X2) | ~r2_hidden(X3,X1)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))) => (~r1_tarski(sK2,k3_tarski(sK0)) & ! [X3] : (r1_xboole_0(X3,sK2) | ~r2_hidden(X3,sK1)) & r1_tarski(sK2,k3_tarski(k2_xboole_0(sK0,sK1))))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (~r1_tarski(X2,k3_tarski(X0)) & ! [X3] : (r1_xboole_0(X3,X2) | ~r2_hidden(X3,X1)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1))))),
% 0.21/0.42    inference(flattening,[],[f7])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0,X1,X2] : (~r1_tarski(X2,k3_tarski(X0)) & (! [X3] : (r1_xboole_0(X3,X2) | ~r2_hidden(X3,X1)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,negated_conjecture,(
% 0.21/0.42    ~! [X0,X1,X2] : ((! [X3] : (r2_hidden(X3,X1) => r1_xboole_0(X3,X2)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))) => r1_tarski(X2,k3_tarski(X0)))),
% 0.21/0.42    inference(negated_conjecture,[],[f5])).
% 0.21/0.42  fof(f5,conjecture,(
% 0.21/0.42    ! [X0,X1,X2] : ((! [X3] : (r2_hidden(X3,X1) => r1_xboole_0(X3,X2)) & r1_tarski(X2,k3_tarski(k2_xboole_0(X0,X1)))) => r1_tarski(X2,k3_tarski(X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_setfam_1)).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f31])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X3] : (r1_xboole_0(X3,sK2) | ~r2_hidden(X3,sK1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    ~spl4_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f26])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ~r1_tarski(sK2,k3_tarski(sK0))),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (8681)------------------------------
% 0.21/0.42  % (8681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (8681)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (8681)Memory used [KB]: 10618
% 0.21/0.42  % (8681)Time elapsed: 0.006 s
% 0.21/0.42  % (8681)------------------------------
% 0.21/0.42  % (8681)------------------------------
% 0.21/0.42  % (8674)Success in time 0.063 s
%------------------------------------------------------------------------------
