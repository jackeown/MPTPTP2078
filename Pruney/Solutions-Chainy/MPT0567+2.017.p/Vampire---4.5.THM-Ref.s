%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   55 (  70 expanded)
%              Number of leaves         :   15 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :  134 ( 173 expanded)
%              Number of equality atoms :   24 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f43,f49,f57,f82,f108,f130])).

fof(f130,plain,
    ( spl4_1
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl4_1
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f128,f51])).

fof(f51,plain,(
    ! [X1] : ~ r2_hidden(X1,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f50,f18])).

fof(f18,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_xboole_0)
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f22,f19])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f128,plain,
    ( r2_hidden(sK3(sK1(k10_relat_1(sK0,k1_xboole_0)),k1_xboole_0,sK0),k1_xboole_0)
    | spl4_1
    | ~ spl4_12 ),
    inference(trivial_inequality_removal,[],[f124])).

fof(f124,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r2_hidden(sK3(sK1(k10_relat_1(sK0,k1_xboole_0)),k1_xboole_0,sK0),k1_xboole_0)
    | spl4_1
    | ~ spl4_12 ),
    inference(superposition,[],[f32,f107])).

fof(f107,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k10_relat_1(sK0,X0)
        | r2_hidden(sK3(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl4_12
  <=> ! [X0] :
        ( r2_hidden(sK3(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0)
        | k1_xboole_0 = k10_relat_1(sK0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f32,plain,
    ( k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f30,plain,
    ( spl4_1
  <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f108,plain,
    ( spl4_12
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f104,f80,f35,f106])).

fof(f35,plain,
    ( spl4_2
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f80,plain,
    ( spl4_9
  <=> ! [X7,X8] :
        ( k1_xboole_0 = k10_relat_1(X7,X8)
        | r2_hidden(sK3(sK1(k10_relat_1(X7,X8)),X8,X7),X8)
        | ~ v1_relat_1(X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f104,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0)
        | k1_xboole_0 = k10_relat_1(sK0,X0) )
    | ~ spl4_2
    | ~ spl4_9 ),
    inference(resolution,[],[f81,f37])).

fof(f37,plain,
    ( v1_relat_1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f81,plain,
    ( ! [X8,X7] :
        ( ~ v1_relat_1(X7)
        | r2_hidden(sK3(sK1(k10_relat_1(X7,X8)),X8,X7),X8)
        | k1_xboole_0 = k10_relat_1(X7,X8) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f82,plain,
    ( spl4_9
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f65,f55,f80])).

fof(f55,plain,
    ( spl4_5
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f65,plain,
    ( ! [X8,X7] :
        ( k1_xboole_0 = k10_relat_1(X7,X8)
        | r2_hidden(sK3(sK1(k10_relat_1(X7,X8)),X8,X7),X8)
        | ~ v1_relat_1(X7) )
    | ~ spl4_5 ),
    inference(resolution,[],[f56,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k10_relat_1(X2,X1))
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f56,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f57,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f53,f47,f55])).

fof(f47,plain,
    ( spl4_4
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f53,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK1(X0),X0) )
    | ~ spl4_4 ),
    inference(resolution,[],[f48,f20])).

fof(f20,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f48,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f49,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f44,f40,f47])).

fof(f40,plain,
    ( spl4_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f44,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f24,f42])).

fof(f42,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f40])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | X0 = X1
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f43,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f17,f40])).

fof(f17,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f38,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( k1_xboole_0 != k10_relat_1(X0,k1_xboole_0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f33,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:46:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.42  % (10533)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.43  % (10528)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.43  % (10534)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.43  % (10528)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f131,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f33,f38,f43,f49,f57,f82,f108,f130])).
% 0.20/0.43  fof(f130,plain,(
% 0.20/0.43    spl4_1 | ~spl4_12),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f129])).
% 0.20/0.43  fof(f129,plain,(
% 0.20/0.43    $false | (spl4_1 | ~spl4_12)),
% 0.20/0.43    inference(subsumption_resolution,[],[f128,f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X1] : (~r2_hidden(X1,k1_xboole_0)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f50,f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r2_hidden(X1,k1_xboole_0) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(superposition,[],[f22,f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.43    inference(rectify,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.43  fof(f128,plain,(
% 0.20/0.43    r2_hidden(sK3(sK1(k10_relat_1(sK0,k1_xboole_0)),k1_xboole_0,sK0),k1_xboole_0) | (spl4_1 | ~spl4_12)),
% 0.20/0.43    inference(trivial_inequality_removal,[],[f124])).
% 0.20/0.43  fof(f124,plain,(
% 0.20/0.43    k1_xboole_0 != k1_xboole_0 | r2_hidden(sK3(sK1(k10_relat_1(sK0,k1_xboole_0)),k1_xboole_0,sK0),k1_xboole_0) | (spl4_1 | ~spl4_12)),
% 0.20/0.43    inference(superposition,[],[f32,f107])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k10_relat_1(sK0,X0) | r2_hidden(sK3(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0)) ) | ~spl4_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f106])).
% 0.20/0.43  fof(f106,plain,(
% 0.20/0.43    spl4_12 <=> ! [X0] : (r2_hidden(sK3(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0) | k1_xboole_0 = k10_relat_1(sK0,X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0) | spl4_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    spl4_1 <=> k1_xboole_0 = k10_relat_1(sK0,k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.43  fof(f108,plain,(
% 0.20/0.43    spl4_12 | ~spl4_2 | ~spl4_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f104,f80,f35,f106])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    spl4_2 <=> v1_relat_1(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    spl4_9 <=> ! [X7,X8] : (k1_xboole_0 = k10_relat_1(X7,X8) | r2_hidden(sK3(sK1(k10_relat_1(X7,X8)),X8,X7),X8) | ~v1_relat_1(X7))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.43  fof(f104,plain,(
% 0.20/0.43    ( ! [X0] : (r2_hidden(sK3(sK1(k10_relat_1(sK0,X0)),X0,sK0),X0) | k1_xboole_0 = k10_relat_1(sK0,X0)) ) | (~spl4_2 | ~spl4_9)),
% 0.20/0.43    inference(resolution,[],[f81,f37])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    v1_relat_1(sK0) | ~spl4_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f35])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    ( ! [X8,X7] : (~v1_relat_1(X7) | r2_hidden(sK3(sK1(k10_relat_1(X7,X8)),X8,X7),X8) | k1_xboole_0 = k10_relat_1(X7,X8)) ) | ~spl4_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f80])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    spl4_9 | ~spl4_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f65,f55,f80])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    spl4_5 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    ( ! [X8,X7] : (k1_xboole_0 = k10_relat_1(X7,X8) | r2_hidden(sK3(sK1(k10_relat_1(X7,X8)),X8,X7),X8) | ~v1_relat_1(X7)) ) | ~spl4_5),
% 0.20/0.43    inference(resolution,[],[f56,f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k10_relat_1(X2,X1)) | r2_hidden(sK3(X0,X1,X2),X1) | ~v1_relat_1(X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) ) | ~spl4_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f55])).
% 0.20/0.43  fof(f57,plain,(
% 0.20/0.43    spl4_5 | ~spl4_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f53,f47,f55])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    spl4_4 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK1(X0),X0)) ) | ~spl4_4),
% 0.20/0.43    inference(resolution,[],[f48,f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl4_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f47])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    spl4_4 | ~spl4_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f44,f40,f47])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    spl4_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | ~spl4_3),
% 0.20/0.43    inference(resolution,[],[f24,f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0) | ~spl4_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f40])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v1_xboole_0(X0) | X0 = X1 | ~v1_xboole_0(X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    spl4_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f17,f40])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f15,f35])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    v1_relat_1(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ? [X0] : (k1_xboole_0 != k10_relat_1(X0,k1_xboole_0) & v1_relat_1(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,negated_conjecture,(
% 0.20/0.43    ~! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.20/0.43    inference(negated_conjecture,[],[f8])).
% 0.20/0.43  fof(f8,conjecture,(
% 0.20/0.43    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ~spl4_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f16,f30])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    k1_xboole_0 != k10_relat_1(sK0,k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (10528)------------------------------
% 0.20/0.43  % (10528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (10528)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (10528)Memory used [KB]: 10618
% 0.20/0.43  % (10528)Time elapsed: 0.027 s
% 0.20/0.43  % (10528)------------------------------
% 0.20/0.43  % (10528)------------------------------
% 0.20/0.44  % (10526)Success in time 0.076 s
%------------------------------------------------------------------------------
