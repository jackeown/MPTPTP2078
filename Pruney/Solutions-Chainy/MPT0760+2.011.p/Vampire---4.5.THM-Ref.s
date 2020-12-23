%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  79 expanded)
%              Number of leaves         :   13 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :  150 ( 225 expanded)
%              Number of equality atoms :   25 (  39 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f105,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f36,f40,f44,f56,f60,f65,f78,f92,f104])).

fof(f104,plain,
    ( spl4_2
    | spl4_3
    | ~ spl4_14 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl4_2
    | spl4_3
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f98,f39])).

fof(f39,plain,
    ( k1_xboole_0 != k1_wellord1(sK1,sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl4_3
  <=> k1_xboole_0 = k1_wellord1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f98,plain,
    ( k1_xboole_0 = k1_wellord1(sK1,sK0)
    | spl4_2
    | ~ spl4_14 ),
    inference(resolution,[],[f91,f35])).

fof(f35,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(sK1))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl4_2
  <=> r2_hidden(sK0,k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f91,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k3_relat_1(sK1))
        | k1_xboole_0 = k1_wellord1(sK1,X1) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl4_14
  <=> ! [X1] :
        ( k1_xboole_0 = k1_wellord1(sK1,X1)
        | r2_hidden(X1,k3_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f92,plain,
    ( spl4_14
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f82,f76,f54,f30,f90])).

fof(f30,plain,
    ( spl4_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f54,plain,
    ( spl4_7
  <=> ! [X1,X0,X2] :
        ( ~ v1_relat_1(X2)
        | ~ r2_hidden(k4_tarski(X0,X1),X2)
        | r2_hidden(X1,k3_relat_1(X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f76,plain,
    ( spl4_12
  <=> ! [X0] :
        ( r2_hidden(k4_tarski(sK3(k1_wellord1(sK1,X0)),X0),sK1)
        | k1_xboole_0 = k1_wellord1(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f82,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_wellord1(sK1,X1)
        | r2_hidden(X1,k3_relat_1(sK1)) )
    | ~ spl4_1
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f80,f31])).

fof(f31,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f80,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_wellord1(sK1,X1)
        | ~ v1_relat_1(sK1)
        | r2_hidden(X1,k3_relat_1(sK1)) )
    | ~ spl4_7
    | ~ spl4_12 ),
    inference(resolution,[],[f77,f55])).

fof(f55,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(k4_tarski(X0,X1),X2)
        | ~ v1_relat_1(X2)
        | r2_hidden(X1,k3_relat_1(X2)) )
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f54])).

fof(f77,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(k1_wellord1(sK1,X0)),X0),sK1)
        | k1_xboole_0 = k1_wellord1(sK1,X0) )
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f76])).

fof(f78,plain,
    ( spl4_12
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f70,f63,f42,f76])).

fof(f42,plain,
    ( spl4_4
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | r2_hidden(sK3(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f63,plain,
    ( spl4_9
  <=> ! [X1,X0] :
        ( r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X0,k1_wellord1(sK1,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f70,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK3(k1_wellord1(sK1,X0)),X0),sK1)
        | k1_xboole_0 = k1_wellord1(sK1,X0) )
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(resolution,[],[f64,f43])).

fof(f43,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(X0),X0)
        | k1_xboole_0 = X0 )
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_wellord1(sK1,X1))
        | r2_hidden(k4_tarski(X0,X1),sK1) )
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f65,plain,
    ( spl4_9
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f61,f58,f30,f63])).

fof(f58,plain,
    ( spl4_8
  <=> ! [X1,X3,X0] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(X3,X1),X0)
        | ~ r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k4_tarski(X0,X1),sK1)
        | ~ r2_hidden(X0,k1_wellord1(sK1,X1)) )
    | ~ spl4_1
    | ~ spl4_8 ),
    inference(resolution,[],[f59,f31])).

fof(f59,plain,
    ( ! [X0,X3,X1] :
        ( ~ v1_relat_1(X0)
        | r2_hidden(k4_tarski(X3,X1),X0)
        | ~ r2_hidden(X3,k1_wellord1(X0,X1)) )
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f58])).

fof(f60,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f25,f58])).

fof(f25,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,k1_wellord1(X0,X1)) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X3,X1),X0)
      | ~ r2_hidden(X3,X2)
      | k1_wellord1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).

fof(f56,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f23,f54])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k3_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k3_relat_1(X2))
        & r2_hidden(X0,k3_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k3_relat_1(X2))
          & r2_hidden(X0,k3_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).

fof(f44,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f21,f42])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK3(X0),X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f40,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f14,f38])).

fof(f14,plain,(
    k1_xboole_0 != k1_wellord1(sK1,sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 != k1_wellord1(X1,X0)
      & ~ r2_hidden(X0,k3_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k1_wellord1(X1,X0)
          | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k1_wellord1(X1,X0)
        | r2_hidden(X0,k3_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).

fof(f36,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f13,f34])).

fof(f13,plain,(
    ~ r2_hidden(sK0,k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f32,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f12,f30])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:05:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (11000)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (10992)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (10998)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.46  % (10988)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (10992)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f105,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f32,f36,f40,f44,f56,f60,f65,f78,f92,f104])).
% 0.21/0.46  fof(f104,plain,(
% 0.21/0.46    spl4_2 | spl4_3 | ~spl4_14),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f103])).
% 0.21/0.46  fof(f103,plain,(
% 0.21/0.46    $false | (spl4_2 | spl4_3 | ~spl4_14)),
% 0.21/0.46    inference(subsumption_resolution,[],[f98,f39])).
% 0.21/0.46  fof(f39,plain,(
% 0.21/0.46    k1_xboole_0 != k1_wellord1(sK1,sK0) | spl4_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    spl4_3 <=> k1_xboole_0 = k1_wellord1(sK1,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.46  fof(f98,plain,(
% 0.21/0.46    k1_xboole_0 = k1_wellord1(sK1,sK0) | (spl4_2 | ~spl4_14)),
% 0.21/0.46    inference(resolution,[],[f91,f35])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ~r2_hidden(sK0,k3_relat_1(sK1)) | spl4_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f34])).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    spl4_2 <=> r2_hidden(sK0,k3_relat_1(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    ( ! [X1] : (r2_hidden(X1,k3_relat_1(sK1)) | k1_xboole_0 = k1_wellord1(sK1,X1)) ) | ~spl4_14),
% 0.21/0.46    inference(avatar_component_clause,[],[f90])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    spl4_14 <=> ! [X1] : (k1_xboole_0 = k1_wellord1(sK1,X1) | r2_hidden(X1,k3_relat_1(sK1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.46  fof(f92,plain,(
% 0.21/0.46    spl4_14 | ~spl4_1 | ~spl4_7 | ~spl4_12),
% 0.21/0.46    inference(avatar_split_clause,[],[f82,f76,f54,f30,f90])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    spl4_1 <=> v1_relat_1(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    spl4_7 <=> ! [X1,X0,X2] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    spl4_12 <=> ! [X0] : (r2_hidden(k4_tarski(sK3(k1_wellord1(sK1,X0)),X0),sK1) | k1_xboole_0 = k1_wellord1(sK1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    ( ! [X1] : (k1_xboole_0 = k1_wellord1(sK1,X1) | r2_hidden(X1,k3_relat_1(sK1))) ) | (~spl4_1 | ~spl4_7 | ~spl4_12)),
% 0.21/0.46    inference(subsumption_resolution,[],[f80,f31])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    v1_relat_1(sK1) | ~spl4_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f30])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    ( ! [X1] : (k1_xboole_0 = k1_wellord1(sK1,X1) | ~v1_relat_1(sK1) | r2_hidden(X1,k3_relat_1(sK1))) ) | (~spl4_7 | ~spl4_12)),
% 0.21/0.46    inference(resolution,[],[f77,f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k3_relat_1(X2))) ) | ~spl4_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f54])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(k4_tarski(sK3(k1_wellord1(sK1,X0)),X0),sK1) | k1_xboole_0 = k1_wellord1(sK1,X0)) ) | ~spl4_12),
% 0.21/0.46    inference(avatar_component_clause,[],[f76])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    spl4_12 | ~spl4_4 | ~spl4_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f70,f63,f42,f76])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl4_4 <=> ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    spl4_9 <=> ! [X1,X0] : (r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X0,k1_wellord1(sK1,X1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(k4_tarski(sK3(k1_wellord1(sK1,X0)),X0),sK1) | k1_xboole_0 = k1_wellord1(sK1,X0)) ) | (~spl4_4 | ~spl4_9)),
% 0.21/0.46    inference(resolution,[],[f64,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) ) | ~spl4_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f42])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_hidden(X0,k1_wellord1(sK1,X1)) | r2_hidden(k4_tarski(X0,X1),sK1)) ) | ~spl4_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f63])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    spl4_9 | ~spl4_1 | ~spl4_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f61,f58,f30,f63])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl4_8 <=> ! [X1,X3,X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k1_wellord1(X0,X1)))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.46  fof(f61,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r2_hidden(k4_tarski(X0,X1),sK1) | ~r2_hidden(X0,k1_wellord1(sK1,X1))) ) | (~spl4_1 | ~spl4_8)),
% 0.21/0.46    inference(resolution,[],[f59,f31])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k1_wellord1(X0,X1))) ) | ~spl4_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f58])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    spl4_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f58])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,k1_wellord1(X0,X1))) )),
% 0.21/0.46    inference(equality_resolution,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(X3,X1),X0) | ~r2_hidden(X3,X2) | k1_wellord1(X0,X1) != X2) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord1)).
% 0.21/0.46  fof(f56,plain,(
% 0.21/0.46    spl4_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f23,f54])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k3_relat_1(X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1,X2] : ((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(flattening,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (((r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k3_relat_1(X2)) & r2_hidden(X0,k3_relat_1(X2)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_relat_1)).
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    spl4_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f42])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK3(X0),X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    ~spl4_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f14,f38])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    k1_xboole_0 != k1_wellord1(sK1,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1] : (k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1)) & v1_relat_1(X1))),
% 0.21/0.46    inference(flattening,[],[f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0,X1] : ((k1_xboole_0 != k1_wellord1(X1,X0) & ~r2_hidden(X0,k3_relat_1(X1))) & v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 0.21/0.46    inference(negated_conjecture,[],[f4])).
% 0.21/0.46  fof(f4,conjecture,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k1_wellord1(X1,X0) | r2_hidden(X0,k3_relat_1(X1))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_wellord1)).
% 0.21/0.46  fof(f36,plain,(
% 0.21/0.46    ~spl4_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f13,f34])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ~r2_hidden(sK0,k3_relat_1(sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    spl4_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f12,f30])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    v1_relat_1(sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (10992)------------------------------
% 0.21/0.46  % (10992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (10992)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (10992)Memory used [KB]: 10618
% 0.21/0.46  % (10992)Time elapsed: 0.056 s
% 0.21/0.46  % (10992)------------------------------
% 0.21/0.46  % (10992)------------------------------
% 0.21/0.47  % (10989)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (10982)Success in time 0.111 s
%------------------------------------------------------------------------------
