%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 (  86 expanded)
%              Number of leaves         :   12 (  28 expanded)
%              Depth                    :    9
%              Number of atoms          :  142 ( 206 expanded)
%              Number of equality atoms :   33 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f51,f119,f142,f144,f156])).

fof(f156,plain,
    ( ~ spl4_1
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f44,f40,f141,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f141,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl4_4
  <=> r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f40,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_tarski(X3,X1)) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f44,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl4_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f144,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f17,f137])).

fof(f137,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl4_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f142,plain,
    ( ~ spl4_3
    | spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f131,f47,f139,f135])).

fof(f47,plain,
    ( spl4_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f131,plain,
    ( r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(trivial_inequality_removal,[],[f130])).

fof(f130,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl4_2 ),
    inference(superposition,[],[f70,f49])).

fof(f49,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) != k1_xboole_0
      | r1_xboole_0(k1_relat_1(X0),k2_tarski(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) != k1_xboole_0
      | r1_xboole_0(k1_relat_1(X0),k2_tarski(X1,X1))
      | ~ v1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f25,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) != k1_xboole_0
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k9_relat_1(X1,X0) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f119,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f17,f45,f48,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k11_relat_1(X0,X1) = k1_xboole_0
      | ~ v1_relat_1(X0)
      | r2_hidden(X1,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f69,f61])).

fof(f61,plain,(
    ! [X6,X7] :
      ( r1_xboole_0(X6,k2_tarski(X7,X7))
      | r2_hidden(X7,X6) ) ),
    inference(superposition,[],[f20,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k2_tarski(X1,X1)) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f26,f18])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f20,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f69,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(k1_relat_1(X2),k2_tarski(X3,X3))
      | k1_xboole_0 = k11_relat_1(X2,X3)
      | ~ v1_relat_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f68])).

fof(f68,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = k11_relat_1(X2,X3)
      | ~ r1_xboole_0(k1_relat_1(X2),k2_tarski(X3,X3))
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(superposition,[],[f24,f34])).

% (6147)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f48,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f45,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f43])).

% (6145)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f51,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f15,f47,f43])).

fof(f15,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f50,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f16,f47,f43])).

fof(f16,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:25:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (6139)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (6126)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.50  % (6155)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (6130)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (6134)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.51  % (6131)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (6150)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.51  % (6139)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (6129)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f157,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f50,f51,f119,f142,f144,f156])).
% 0.20/0.51  fof(f156,plain,(
% 0.20/0.51    ~spl4_1 | ~spl4_4),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f148])).
% 0.20/0.51  fof(f148,plain,(
% 0.20/0.51    $false | (~spl4_1 | ~spl4_4)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f44,f40,f141,f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    inference(rectify,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.51  fof(f141,plain,(
% 0.20/0.51    r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0)) | ~spl4_4),
% 0.20/0.51    inference(avatar_component_clause,[],[f139])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    spl4_4 <=> r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X3,X1] : (r2_hidden(X3,k2_tarski(X3,X1))) )),
% 0.20/0.51    inference(equality_resolution,[],[f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_tarski(X3,X1) != X2) )),
% 0.20/0.51    inference(equality_resolution,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl4_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f43])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    spl4_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    spl4_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f143])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    $false | spl4_3),
% 0.20/0.52    inference(subsumption_resolution,[],[f17,f137])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    ~v1_relat_1(sK1) | spl4_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f135])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    spl4_3 <=> v1_relat_1(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    v1_relat_1(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.52    inference(negated_conjecture,[],[f8])).
% 0.20/0.52  fof(f8,conjecture,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    ~spl4_3 | spl4_4 | ~spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f131,f47,f139,f135])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    spl4_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  fof(f131,plain,(
% 0.20/0.52    r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0)) | ~v1_relat_1(sK1) | ~spl4_2),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f130])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK1),k2_tarski(sK0,sK0)) | ~v1_relat_1(sK1) | ~spl4_2),
% 0.20/0.52    inference(superposition,[],[f70,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f47])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) != k1_xboole_0 | r1_xboole_0(k1_relat_1(X0),k2_tarski(X1,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) != k1_xboole_0 | r1_xboole_0(k1_relat_1(X0),k2_tarski(X1,X1)) | ~v1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(superposition,[],[f25,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k9_relat_1(X0,k2_tarski(X1,X1)) | ~v1_relat_1(X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f19,f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k9_relat_1(X1,X0) != k1_xboole_0 | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0,X1] : ((k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k9_relat_1(X1,X0) = k1_xboole_0 <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    spl4_1 | spl4_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f116])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    $false | (spl4_1 | spl4_2)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f17,f45,f48,f115])).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k11_relat_1(X0,X1) = k1_xboole_0 | ~v1_relat_1(X0) | r2_hidden(X1,k1_relat_1(X0))) )),
% 0.20/0.52    inference(resolution,[],[f69,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X6,X7] : (r1_xboole_0(X6,k2_tarski(X7,X7)) | r2_hidden(X7,X6)) )),
% 0.20/0.52    inference(superposition,[],[f20,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,k2_tarski(X1,X1)) = X0 | r2_hidden(X1,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f26,f18])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r1_xboole_0(k1_relat_1(X2),k2_tarski(X3,X3)) | k1_xboole_0 = k11_relat_1(X2,X3) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    ( ! [X2,X3] : (k1_xboole_0 = k11_relat_1(X2,X3) | ~r1_xboole_0(k1_relat_1(X2),k2_tarski(X3,X3)) | ~v1_relat_1(X2) | ~v1_relat_1(X2)) )),
% 0.20/0.52    inference(superposition,[],[f24,f34])).
% 0.20/0.52  % (6147)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k1_xboole_0 | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    k1_xboole_0 != k11_relat_1(sK1,sK0) | spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f47])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl4_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f43])).
% 0.20/0.52  % (6145)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    spl4_1 | ~spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f15,f47,f43])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ~spl4_1 | spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f16,f47,f43])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f11])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (6139)------------------------------
% 0.20/0.52  % (6139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (6139)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (6139)Memory used [KB]: 6268
% 0.20/0.52  % (6139)Time elapsed: 0.101 s
% 0.20/0.52  % (6139)------------------------------
% 0.20/0.52  % (6139)------------------------------
% 0.20/0.52  % (6125)Success in time 0.163 s
%------------------------------------------------------------------------------
