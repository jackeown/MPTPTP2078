%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:53:18 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   53 (  87 expanded)
%              Number of leaves         :   11 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :  168 ( 284 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f93,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f41,f49,f53,f60,f64,f69,f92])).

fof(f92,plain,
    ( ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_7 ),
    inference(subsumption_resolution,[],[f88,f68])).

fof(f68,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_7
  <=> r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f88,plain,
    ( r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(resolution,[],[f75,f48])).

fof(f48,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl4_3
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f75,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,X0)) )
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f74,f36])).

fof(f36,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl4_1
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(sK2)
        | ~ r2_hidden(sK0,X0)
        | r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,X0)) )
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f70,f52])).

fof(f52,plain,
    ( r2_hidden(sK0,k1_relat_1(sK2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl4_4
  <=> r2_hidden(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,k1_relat_1(sK2))
        | ~ v1_relat_1(sK2)
        | ~ r2_hidden(sK0,X0)
        | r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,X0)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f59,f30])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k9_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

fof(f59,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f58])).

% (21038)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
fof(f58,plain,
    ( spl4_5
  <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f69,plain,
    ( ~ spl4_7
    | ~ spl4_1
    | spl4_6 ),
    inference(avatar_split_clause,[],[f65,f62,f35,f67])).

fof(f62,plain,
    ( spl4_6
  <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f65,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1))
    | ~ spl4_1
    | spl4_6 ),
    inference(forward_demodulation,[],[f63,f42])).

fof(f42,plain,
    ( ! [X0] : k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)
    | ~ spl4_1 ),
    inference(resolution,[],[f36,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f63,plain,
    ( ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f19,f62])).

fof(f19,plain,(
    ~ r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))
      & r2_hidden(X0,X1)
      & r2_hidden(X0,k1_relat_1(X2))
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( v1_funct_1(X2)
          & v1_relat_1(X2) )
       => ( ( r2_hidden(X0,X1)
            & r2_hidden(X0,k1_relat_1(X2)) )
         => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( r2_hidden(X0,X1)
          & r2_hidden(X0,k1_relat_1(X2)) )
       => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).

fof(f60,plain,
    ( spl4_5
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f56,f51,f39,f35,f58])).

fof(f39,plain,
    ( spl4_2
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f56,plain,
    ( r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f55,f36])).

fof(f55,plain,
    ( ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f54,f40])).

fof(f40,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f54,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)
    | ~ spl4_4 ),
    inference(resolution,[],[f52,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).

fof(f53,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f17,f51])).

fof(f17,plain,(
    r2_hidden(sK0,k1_relat_1(sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f49,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f18,f47])).

fof(f18,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f41,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f16,f39])).

fof(f16,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f37,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 17:39:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (21028)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.46  % (21036)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.47  % (21033)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.47  % (21027)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.47  % (21029)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.47  % (21046)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.47  % (21032)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.47  % (21043)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.47  % (21027)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f37,f41,f49,f53,f60,f64,f69,f92])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    ~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_7),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f91])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    $false | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_7)),
% 0.22/0.47    inference(subsumption_resolution,[],[f88,f68])).
% 0.22/0.47  fof(f68,plain,(
% 0.22/0.47    ~r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1)) | spl4_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f67])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    spl4_7 <=> r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1)) | (~spl4_1 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.22/0.47    inference(resolution,[],[f75,f48])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    r2_hidden(sK0,sK1) | ~spl4_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    spl4_3 <=> r2_hidden(sK0,sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(sK0,X0) | r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,X0))) ) | (~spl4_1 | ~spl4_4 | ~spl4_5)),
% 0.22/0.47    inference(subsumption_resolution,[],[f74,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    v1_relat_1(sK2) | ~spl4_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    spl4_1 <=> v1_relat_1(sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.47  fof(f74,plain,(
% 0.22/0.47    ( ! [X0] : (~v1_relat_1(sK2) | ~r2_hidden(sK0,X0) | r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,X0))) ) | (~spl4_4 | ~spl4_5)),
% 0.22/0.47    inference(subsumption_resolution,[],[f70,f52])).
% 0.22/0.47  fof(f52,plain,(
% 0.22/0.47    r2_hidden(sK0,k1_relat_1(sK2)) | ~spl4_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f51])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    spl4_4 <=> r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(sK0,k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~r2_hidden(sK0,X0) | r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,X0))) ) | ~spl4_5),
% 0.22/0.47    inference(resolution,[],[f59,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k9_relat_1(X2,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~spl4_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f58])).
% 0.22/0.48  % (21038)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    spl4_5 <=> r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    ~spl4_7 | ~spl4_1 | spl4_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f65,f62,f35,f67])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl4_6 <=> r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    ~r2_hidden(k1_funct_1(sK2,sK0),k9_relat_1(sK2,sK1)) | (~spl4_1 | spl4_6)),
% 0.22/0.48    inference(forward_demodulation,[],[f63,f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0] : (k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0)) ) | ~spl4_1),
% 0.22/0.48    inference(resolution,[],[f36,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1))) | spl4_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f62])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    ~spl4_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f19,f62])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ~r2_hidden(k1_funct_1(sK2,sK0),k2_relat_1(k7_relat_1(sK2,sK1)))),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)) & v1_funct_1(X2) & v1_relat_1(X2))),
% 0.22/0.48    inference(flattening,[],[f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0,X1,X2] : ((~r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1))) & (r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2)))) & (v1_funct_1(X2) & v1_relat_1(X2)))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((r2_hidden(X0,X1) & r2_hidden(X0,k1_relat_1(X2))) => r2_hidden(k1_funct_1(X2,X0),k2_relat_1(k7_relat_1(X2,X1)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_funct_1)).
% 0.22/0.48  fof(f60,plain,(
% 0.22/0.48    spl4_5 | ~spl4_1 | ~spl4_2 | ~spl4_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f56,f51,f39,f35,f58])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    spl4_2 <=> v1_funct_1(sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | (~spl4_1 | ~spl4_2 | ~spl4_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f55,f36])).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | (~spl4_2 | ~spl4_4)),
% 0.22/0.48    inference(subsumption_resolution,[],[f54,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    v1_funct_1(sK2) | ~spl4_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f39])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | r2_hidden(k4_tarski(sK0,k1_funct_1(sK2,sK0)),sK2) | ~spl4_4),
% 0.22/0.48    inference(resolution,[],[f52,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)) )),
% 0.22/0.48    inference(equality_resolution,[],[f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_funct_1)).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    spl4_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f17,f51])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    r2_hidden(sK0,k1_relat_1(sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    spl4_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f18,f47])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    r2_hidden(sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    spl4_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f16,f39])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    v1_funct_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    spl4_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f15,f35])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    v1_relat_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (21027)------------------------------
% 0.22/0.48  % (21027)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (21027)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (21027)Memory used [KB]: 6140
% 0.22/0.48  % (21027)Time elapsed: 0.068 s
% 0.22/0.48  % (21027)------------------------------
% 0.22/0.48  % (21027)------------------------------
% 0.22/0.48  % (21045)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.48  % (21030)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (21026)Success in time 0.112 s
%------------------------------------------------------------------------------
