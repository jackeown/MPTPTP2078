%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  83 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :  135 ( 207 expanded)
%              Number of equality atoms :   29 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f72,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f39,f44,f48,f57,f64,f68,f71])).

fof(f71,plain,
    ( spl4_2
    | ~ spl4_7 ),
    inference(avatar_contradiction_clause,[],[f70])).

fof(f70,plain,
    ( $false
    | spl4_2
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f69,f34])).

fof(f34,plain,
    ( k1_xboole_0 != sK0
    | spl4_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f69,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_7 ),
    inference(resolution,[],[f56,f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f56,plain,
    ( ! [X0] : ~ r2_hidden(X0,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_7
  <=> ! [X0] : ~ r2_hidden(X0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f68,plain,
    ( spl4_6
    | ~ spl4_8 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | spl4_6
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f66,f53])).

fof(f53,plain,
    ( ~ r1_xboole_0(sK0,k1_relat_1(sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl4_6
  <=> r1_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f66,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl4_8 ),
    inference(resolution,[],[f63,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
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

fof(f63,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl4_8
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f64,plain,
    ( spl4_8
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f60,f42,f28,f62])).

fof(f28,plain,
    ( spl4_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f42,plain,
    ( spl4_4
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f60,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(trivial_inequality_removal,[],[f59])).

fof(f59,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(superposition,[],[f31,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f31,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k9_relat_1(sK1,X0)
        | r1_xboole_0(k1_relat_1(sK1),X0) )
    | ~ spl4_1 ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f29,plain,
    ( v1_relat_1(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f57,plain,
    ( ~ spl4_6
    | spl4_7
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f49,f46,f55,f52])).

fof(f46,plain,
    ( spl4_5
  <=> sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f49,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ r1_xboole_0(sK0,k1_relat_1(sK1)) )
    | ~ spl4_5 ),
    inference(superposition,[],[f25,f47])).

fof(f47,plain,
    ( sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f48,plain,
    ( spl4_5
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f40,f37,f46])).

fof(f37,plain,
    ( spl4_3
  <=> r1_tarski(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f40,plain,
    ( sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl4_3 ),
    inference(resolution,[],[f38,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f38,plain,
    ( r1_tarski(sK0,k1_relat_1(sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f44,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f19,f42])).

fof(f19,plain,(
    k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k9_relat_1(X1,X0)
      & r1_tarski(X0,k1_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
            & r1_tarski(X0,k1_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(f39,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    r1_tarski(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f30,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f16,f28])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:43:24 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.47  % (25877)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (25892)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  % (25877)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f30,f35,f39,f44,f48,f57,f64,f68,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    spl4_2 | ~spl4_7),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    $false | (spl4_2 | ~spl4_7)),
% 0.20/0.47    inference(subsumption_resolution,[],[f69,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    k1_xboole_0 != sK0 | spl4_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    spl4_2 <=> k1_xboole_0 = sK0),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    k1_xboole_0 = sK0 | ~spl4_7),
% 0.20/0.47    inference(resolution,[],[f56,f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,sK0)) ) | ~spl4_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    spl4_7 <=> ! [X0] : ~r2_hidden(X0,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl4_6 | ~spl4_8),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    $false | (spl4_6 | ~spl4_8)),
% 0.20/0.47    inference(subsumption_resolution,[],[f66,f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ~r1_xboole_0(sK0,k1_relat_1(sK1)) | spl4_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    spl4_6 <=> r1_xboole_0(sK0,k1_relat_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    r1_xboole_0(sK0,k1_relat_1(sK1)) | ~spl4_8),
% 0.20/0.47    inference(resolution,[],[f63,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl4_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl4_8 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl4_8 | ~spl4_1 | ~spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f60,f42,f28,f62])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    spl4_1 <=> v1_relat_1(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    spl4_4 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl4_1 | ~spl4_4)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),sK0) | (~spl4_1 | ~spl4_4)),
% 0.20/0.47    inference(superposition,[],[f31,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl4_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f42])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | r1_xboole_0(k1_relat_1(sK1),X0)) ) | ~spl4_1),
% 0.20/0.47    inference(resolution,[],[f29,f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    v1_relat_1(sK1) | ~spl4_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f28])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ~spl4_6 | spl4_7 | ~spl4_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f49,f46,f55,f52])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    spl4_5 <=> sK0 = k3_xboole_0(sK0,k1_relat_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(X0,sK0) | ~r1_xboole_0(sK0,k1_relat_1(sK1))) ) | ~spl4_5),
% 0.20/0.47    inference(superposition,[],[f25,f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) | ~spl4_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f46])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,plain,(
% 0.20/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    inference(rectify,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    spl4_5 | ~spl4_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f40,f37,f46])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    spl4_3 <=> r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    sK0 = k3_xboole_0(sK0,k1_relat_1(sK1)) | ~spl4_3),
% 0.20/0.47    inference(resolution,[],[f38,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    r1_tarski(sK0,k1_relat_1(sK1)) | ~spl4_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f37])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    spl4_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f19,f42])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1] : (k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f9])).
% 0.20/0.47  fof(f9,plain,(
% 0.20/0.47    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.47    inference(negated_conjecture,[],[f6])).
% 0.20/0.47  fof(f6,conjecture,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    spl4_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f18,f37])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    r1_tarski(sK0,k1_relat_1(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ~spl4_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f17,f33])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    k1_xboole_0 != sK0),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    spl4_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f16,f28])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (25877)------------------------------
% 0.20/0.47  % (25877)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (25877)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (25877)Memory used [KB]: 6140
% 0.20/0.47  % (25877)Time elapsed: 0.054 s
% 0.20/0.47  % (25877)------------------------------
% 0.20/0.47  % (25877)------------------------------
% 0.20/0.47  % (25880)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.48  % (25874)Success in time 0.114 s
%------------------------------------------------------------------------------
