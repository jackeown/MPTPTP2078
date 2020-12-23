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
% DateTime   : Thu Dec  3 12:50:46 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  78 expanded)
%              Number of leaves         :   14 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :  113 ( 189 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f81,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f22,f27,f32,f36,f40,f44,f51,f64,f74,f80])).

fof(f80,plain,
    ( spl3_1
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_contradiction_clause,[],[f79])).

fof(f79,plain,
    ( $false
    | spl3_1
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f76,f21])).

fof(f21,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f19])).

fof(f19,plain,
    ( spl3_1
  <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f76,plain,
    ( r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(superposition,[],[f73,f50])).

fof(f50,plain,
    ( sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl3_7
  <=> sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f73,plain,
    ( ! [X2,X3] : r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK2,k2_xboole_0(X2,X3)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl3_11
  <=> ! [X3,X2] : r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK2,k2_xboole_0(X2,X3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f74,plain,
    ( spl3_11
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f66,f62,f34,f72])).

fof(f34,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f62,plain,
    ( spl3_9
  <=> ! [X1,X0] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f66,plain,
    ( ! [X2,X3] : r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK2,k2_xboole_0(X2,X3)))
    | ~ spl3_4
    | ~ spl3_9 ),
    inference(superposition,[],[f35,f63])).

fof(f63,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f62])).

fof(f35,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f34])).

fof(f64,plain,
    ( spl3_9
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f60,f42,f29,f62])).

fof(f29,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f42,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f60,plain,
    ( ! [X0,X1] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f43,f31])).

fof(f31,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f29])).

fof(f43,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_relat_1(X2)
        | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f42])).

fof(f51,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f45,f38,f24,f48])).

fof(f24,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f38,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f45,plain,
    ( sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f39,f26])).

fof(f26,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f24])).

fof(f39,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f44,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f17,f42])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

fof(f40,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f36,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f15,f34])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f32,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f12,f29])).

fof(f12,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
    & r1_tarski(sK0,sK1)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
        & r1_tarski(X0,X1)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))
      & r1_tarski(sK0,sK1)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).

fof(f27,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f13,f24])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f22,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f14,f19])).

fof(f14,plain,(
    ~ r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:17:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.41  % (17559)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.41  % (17554)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.41  % (17561)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (17559)Refutation found. Thanks to Tanya!
% 0.20/0.41  % SZS status Theorem for theBenchmark
% 0.20/0.41  % SZS output start Proof for theBenchmark
% 0.20/0.41  fof(f81,plain,(
% 0.20/0.41    $false),
% 0.20/0.41    inference(avatar_sat_refutation,[],[f22,f27,f32,f36,f40,f44,f51,f64,f74,f80])).
% 0.20/0.41  fof(f80,plain,(
% 0.20/0.41    spl3_1 | ~spl3_7 | ~spl3_11),
% 0.20/0.41    inference(avatar_contradiction_clause,[],[f79])).
% 0.20/0.41  fof(f79,plain,(
% 0.20/0.41    $false | (spl3_1 | ~spl3_7 | ~spl3_11)),
% 0.20/0.41    inference(subsumption_resolution,[],[f76,f21])).
% 0.20/0.41  fof(f21,plain,(
% 0.20/0.41    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | spl3_1),
% 0.20/0.41    inference(avatar_component_clause,[],[f19])).
% 0.20/0.41  fof(f19,plain,(
% 0.20/0.41    spl3_1 <=> r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.41  fof(f76,plain,(
% 0.20/0.41    r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) | (~spl3_7 | ~spl3_11)),
% 0.20/0.41    inference(superposition,[],[f73,f50])).
% 0.20/0.41  fof(f50,plain,(
% 0.20/0.41    sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | ~spl3_7),
% 0.20/0.41    inference(avatar_component_clause,[],[f48])).
% 0.20/0.41  fof(f48,plain,(
% 0.20/0.41    spl3_7 <=> sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.41  fof(f73,plain,(
% 0.20/0.41    ( ! [X2,X3] : (r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK2,k2_xboole_0(X2,X3)))) ) | ~spl3_11),
% 0.20/0.41    inference(avatar_component_clause,[],[f72])).
% 0.20/0.41  fof(f72,plain,(
% 0.20/0.41    spl3_11 <=> ! [X3,X2] : r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK2,k2_xboole_0(X2,X3)))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.41  fof(f74,plain,(
% 0.20/0.41    spl3_11 | ~spl3_4 | ~spl3_9),
% 0.20/0.41    inference(avatar_split_clause,[],[f66,f62,f34,f72])).
% 0.20/0.41  fof(f34,plain,(
% 0.20/0.41    spl3_4 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.41  fof(f62,plain,(
% 0.20/0.41    spl3_9 <=> ! [X1,X0] : k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))),
% 0.20/0.41    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.41  fof(f66,plain,(
% 0.20/0.41    ( ! [X2,X3] : (r1_tarski(k10_relat_1(sK2,X2),k10_relat_1(sK2,k2_xboole_0(X2,X3)))) ) | (~spl3_4 | ~spl3_9)),
% 0.20/0.41    inference(superposition,[],[f35,f63])).
% 0.20/0.41  fof(f63,plain,(
% 0.20/0.41    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | ~spl3_9),
% 0.20/0.41    inference(avatar_component_clause,[],[f62])).
% 0.20/0.42  fof(f35,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_4),
% 0.20/0.42    inference(avatar_component_clause,[],[f34])).
% 0.20/0.42  fof(f64,plain,(
% 0.20/0.42    spl3_9 | ~spl3_3 | ~spl3_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f60,f42,f29,f62])).
% 0.20/0.42  fof(f29,plain,(
% 0.20/0.42    spl3_3 <=> v1_relat_1(sK2)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.42  fof(f42,plain,(
% 0.20/0.42    spl3_6 <=> ! [X1,X0,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.42  fof(f60,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k10_relat_1(sK2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(sK2,X0),k10_relat_1(sK2,X1))) ) | (~spl3_3 | ~spl3_6)),
% 0.20/0.42    inference(resolution,[],[f43,f31])).
% 0.20/0.42  fof(f31,plain,(
% 0.20/0.42    v1_relat_1(sK2) | ~spl3_3),
% 0.20/0.42    inference(avatar_component_clause,[],[f29])).
% 0.20/0.42  fof(f43,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1))) ) | ~spl3_6),
% 0.20/0.42    inference(avatar_component_clause,[],[f42])).
% 0.20/0.42  fof(f51,plain,(
% 0.20/0.42    spl3_7 | ~spl3_2 | ~spl3_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f45,f38,f24,f48])).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.42  fof(f38,plain,(
% 0.20/0.42    spl3_5 <=> ! [X1,X0] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.42  fof(f45,plain,(
% 0.20/0.42    sK1 = k2_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | (~spl3_2 | ~spl3_5)),
% 0.20/0.42    inference(resolution,[],[f39,f26])).
% 0.20/0.42  fof(f26,plain,(
% 0.20/0.42    r1_tarski(sK0,sK1) | ~spl3_2),
% 0.20/0.42    inference(avatar_component_clause,[],[f24])).
% 0.20/0.42  fof(f39,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) ) | ~spl3_5),
% 0.20/0.42    inference(avatar_component_clause,[],[f38])).
% 0.20/0.42  fof(f44,plain,(
% 0.20/0.42    spl3_6),
% 0.20/0.42    inference(avatar_split_clause,[],[f17,f42])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f9])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.20/0.42    inference(ennf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => k10_relat_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k10_relat_1(X2,X0),k10_relat_1(X2,X1)))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).
% 0.20/0.42  fof(f40,plain,(
% 0.20/0.42    spl3_5),
% 0.20/0.42    inference(avatar_split_clause,[],[f16,f38])).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(ennf_transformation,[],[f1])).
% 0.20/0.42  fof(f1,axiom,(
% 0.20/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 0.20/0.42  fof(f36,plain,(
% 0.20/0.42    spl3_4),
% 0.20/0.42    inference(avatar_split_clause,[],[f15,f34])).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.42  fof(f32,plain,(
% 0.20/0.42    spl3_3),
% 0.20/0.42    inference(avatar_split_clause,[],[f12,f29])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    v1_relat_1(sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2)),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2)) => (~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1)) & r1_tarski(sK0,sK1) & v1_relat_1(sK2))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f7,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.20/0.42    inference(flattening,[],[f6])).
% 0.20/0.42  fof(f6,plain,(
% 0.20/0.42    ? [X0,X1,X2] : ((~r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.20/0.42    inference(negated_conjecture,[],[f4])).
% 0.20/0.42  fof(f4,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k10_relat_1(X2,X0),k10_relat_1(X2,X1))))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_relat_1)).
% 0.20/0.42  fof(f27,plain,(
% 0.20/0.42    spl3_2),
% 0.20/0.42    inference(avatar_split_clause,[],[f13,f24])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    r1_tarski(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ~spl3_1),
% 0.20/0.42    inference(avatar_split_clause,[],[f14,f19])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ~r1_tarski(k10_relat_1(sK2,sK0),k10_relat_1(sK2,sK1))),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (17559)------------------------------
% 0.20/0.42  % (17559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (17559)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (17559)Memory used [KB]: 10490
% 0.20/0.42  % (17559)Time elapsed: 0.006 s
% 0.20/0.42  % (17559)------------------------------
% 0.20/0.42  % (17559)------------------------------
% 0.20/0.42  % (17553)Success in time 0.063 s
%------------------------------------------------------------------------------
