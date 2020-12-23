%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:16 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :   40 (  57 expanded)
%              Number of leaves         :    9 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   90 ( 118 expanded)
%              Number of equality atoms :   23 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f49,f67,f105,f136])).

fof(f136,plain,
    ( ~ spl5_3
    | spl5_6 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl5_3
    | spl5_6 ),
    inference(subsumption_resolution,[],[f128,f24])).

fof(f24,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f128,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0))))
    | ~ spl5_3
    | spl5_6 ),
    inference(resolution,[],[f111,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0 ) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f111,plain,
    ( r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl5_3
    | spl5_6 ),
    inference(subsumption_resolution,[],[f110,f86])).

fof(f86,plain,
    ( ~ r2_hidden(sK1(k1_xboole_0,sK0,k1_xboole_0),k1_xboole_0)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_6
  <=> r2_hidden(sK1(k1_xboole_0,sK0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f110,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK0,k1_xboole_0),k1_xboole_0)
    | r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0)
    | ~ spl5_3 ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,
    ( ! [X2] :
        ( k1_xboole_0 != X2
        | r2_hidden(sK1(k1_xboole_0,sK0,X2),X2)
        | r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,X2),sK3(k1_xboole_0,sK0,X2)),k1_xboole_0) )
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl5_3
  <=> ! [X2] :
        ( k1_xboole_0 != X2
        | r2_hidden(sK1(k1_xboole_0,sK0,X2),X2)
        | r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,X2),sK3(k1_xboole_0,sK0,X2)),k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f105,plain,(
    ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f98,f24])).

fof(f98,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK1(k1_xboole_0,sK0,k1_xboole_0)))
    | ~ spl5_6 ),
    inference(resolution,[],[f87,f30])).

fof(f87,plain,
    ( r2_hidden(sK1(k1_xboole_0,sK0,k1_xboole_0),k1_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f67,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f60,f24])).

fof(f60,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK4(k1_xboole_0),sK4(k1_xboole_0)))
    | spl5_1 ),
    inference(resolution,[],[f54,f30])).

fof(f54,plain,
    ( r2_hidden(sK4(k1_xboole_0),k1_xboole_0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f41,f25])).

fof(f25,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f41,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl5_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f49,plain,
    ( ~ spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f36,f47,f39])).

fof(f36,plain,(
    ! [X2] :
      ( k1_xboole_0 != X2
      | ~ v1_relat_1(k1_xboole_0)
      | r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,X2),sK3(k1_xboole_0,sK0,X2)),k1_xboole_0)
      | r2_hidden(sK1(k1_xboole_0,sK0,X2),X2) ) ),
    inference(superposition,[],[f17,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0)
      | r2_hidden(sK1(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

fof(f17,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:42:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (26508)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (26516)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (26524)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.56  % (26516)Refutation not found, incomplete strategy% (26516)------------------------------
% 0.21/0.56  % (26516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (26510)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.56  % (26518)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (26518)Refutation not found, incomplete strategy% (26518)------------------------------
% 0.21/0.56  % (26518)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (26516)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (26516)Memory used [KB]: 10618
% 0.21/0.56  % (26502)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.56  % (26516)Time elapsed: 0.126 s
% 0.21/0.56  % (26516)------------------------------
% 0.21/0.56  % (26516)------------------------------
% 0.21/0.56  % (26518)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (26518)Memory used [KB]: 10618
% 0.21/0.56  % (26518)Time elapsed: 0.071 s
% 0.21/0.56  % (26518)------------------------------
% 0.21/0.56  % (26518)------------------------------
% 0.21/0.56  % (26500)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.57  % (26500)Refutation not found, incomplete strategy% (26500)------------------------------
% 0.21/0.57  % (26500)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (26500)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (26500)Memory used [KB]: 6140
% 0.21/0.57  % (26500)Time elapsed: 0.122 s
% 0.21/0.57  % (26500)------------------------------
% 0.21/0.57  % (26500)------------------------------
% 0.21/0.57  % (26505)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.52/0.57  % (26505)Refutation found. Thanks to Tanya!
% 1.52/0.57  % SZS status Theorem for theBenchmark
% 1.52/0.57  % SZS output start Proof for theBenchmark
% 1.52/0.57  fof(f137,plain,(
% 1.52/0.57    $false),
% 1.52/0.57    inference(avatar_sat_refutation,[],[f49,f67,f105,f136])).
% 1.52/0.57  fof(f136,plain,(
% 1.52/0.57    ~spl5_3 | spl5_6),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f135])).
% 1.52/0.57  fof(f135,plain,(
% 1.52/0.57    $false | (~spl5_3 | spl5_6)),
% 1.52/0.57    inference(subsumption_resolution,[],[f128,f24])).
% 1.52/0.57  fof(f24,plain,(
% 1.52/0.57    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f1])).
% 1.52/0.57  fof(f1,axiom,(
% 1.52/0.57    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.52/0.57  fof(f128,plain,(
% 1.52/0.57    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)))) | (~spl5_3 | spl5_6)),
% 1.52/0.57    inference(resolution,[],[f111,f30])).
% 1.52/0.57  fof(f30,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k2_tarski(X1,X1)) != X0) )),
% 1.52/0.57    inference(definition_unfolding,[],[f28,f29])).
% 1.52/0.57  fof(f29,plain,(
% 1.52/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f2])).
% 1.52/0.57  fof(f2,axiom,(
% 1.52/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.52/0.57  fof(f28,plain,(
% 1.52/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 1.52/0.57    inference(cnf_transformation,[],[f8])).
% 1.52/0.57  fof(f8,axiom,(
% 1.52/0.57    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.52/0.57  fof(f111,plain,(
% 1.52/0.57    r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0) | (~spl5_3 | spl5_6)),
% 1.52/0.57    inference(subsumption_resolution,[],[f110,f86])).
% 1.52/0.57  fof(f86,plain,(
% 1.52/0.57    ~r2_hidden(sK1(k1_xboole_0,sK0,k1_xboole_0),k1_xboole_0) | spl5_6),
% 1.52/0.57    inference(avatar_component_clause,[],[f85])).
% 1.52/0.57  fof(f85,plain,(
% 1.52/0.57    spl5_6 <=> r2_hidden(sK1(k1_xboole_0,sK0,k1_xboole_0),k1_xboole_0)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.52/0.57  fof(f110,plain,(
% 1.52/0.57    r2_hidden(sK1(k1_xboole_0,sK0,k1_xboole_0),k1_xboole_0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK3(k1_xboole_0,sK0,k1_xboole_0)),k1_xboole_0) | ~spl5_3),
% 1.52/0.57    inference(equality_resolution,[],[f48])).
% 1.52/0.57  fof(f48,plain,(
% 1.52/0.57    ( ! [X2] : (k1_xboole_0 != X2 | r2_hidden(sK1(k1_xboole_0,sK0,X2),X2) | r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,X2),sK3(k1_xboole_0,sK0,X2)),k1_xboole_0)) ) | ~spl5_3),
% 1.52/0.57    inference(avatar_component_clause,[],[f47])).
% 1.52/0.57  fof(f47,plain,(
% 1.52/0.57    spl5_3 <=> ! [X2] : (k1_xboole_0 != X2 | r2_hidden(sK1(k1_xboole_0,sK0,X2),X2) | r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,X2),sK3(k1_xboole_0,sK0,X2)),k1_xboole_0))),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.52/0.57  fof(f105,plain,(
% 1.52/0.57    ~spl5_6),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f104])).
% 1.52/0.57  fof(f104,plain,(
% 1.52/0.57    $false | ~spl5_6),
% 1.52/0.57    inference(subsumption_resolution,[],[f98,f24])).
% 1.52/0.57  fof(f98,plain,(
% 1.52/0.57    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK1(k1_xboole_0,sK0,k1_xboole_0),sK1(k1_xboole_0,sK0,k1_xboole_0))) | ~spl5_6),
% 1.52/0.57    inference(resolution,[],[f87,f30])).
% 1.52/0.57  fof(f87,plain,(
% 1.52/0.57    r2_hidden(sK1(k1_xboole_0,sK0,k1_xboole_0),k1_xboole_0) | ~spl5_6),
% 1.52/0.57    inference(avatar_component_clause,[],[f85])).
% 1.52/0.57  fof(f67,plain,(
% 1.52/0.57    spl5_1),
% 1.52/0.57    inference(avatar_contradiction_clause,[],[f66])).
% 1.52/0.57  fof(f66,plain,(
% 1.52/0.57    $false | spl5_1),
% 1.52/0.57    inference(subsumption_resolution,[],[f60,f24])).
% 1.52/0.57  fof(f60,plain,(
% 1.52/0.57    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_tarski(sK4(k1_xboole_0),sK4(k1_xboole_0))) | spl5_1),
% 1.52/0.57    inference(resolution,[],[f54,f30])).
% 1.52/0.57  fof(f54,plain,(
% 1.52/0.57    r2_hidden(sK4(k1_xboole_0),k1_xboole_0) | spl5_1),
% 1.52/0.57    inference(unit_resulting_resolution,[],[f41,f25])).
% 1.52/0.57  fof(f25,plain,(
% 1.52/0.57    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_relat_1(X0)) )),
% 1.52/0.57    inference(cnf_transformation,[],[f16])).
% 1.52/0.57  fof(f16,plain,(
% 1.52/0.57    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.52/0.57    inference(ennf_transformation,[],[f13])).
% 1.52/0.57  fof(f13,plain,(
% 1.52/0.57    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 1.52/0.57    inference(unused_predicate_definition_removal,[],[f10])).
% 1.52/0.57  fof(f10,axiom,(
% 1.52/0.57    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 1.52/0.57  fof(f41,plain,(
% 1.52/0.57    ~v1_relat_1(k1_xboole_0) | spl5_1),
% 1.52/0.57    inference(avatar_component_clause,[],[f39])).
% 1.52/0.57  fof(f39,plain,(
% 1.52/0.57    spl5_1 <=> v1_relat_1(k1_xboole_0)),
% 1.52/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.52/0.57  fof(f49,plain,(
% 1.52/0.57    ~spl5_1 | spl5_3),
% 1.52/0.57    inference(avatar_split_clause,[],[f36,f47,f39])).
% 1.52/0.57  fof(f36,plain,(
% 1.52/0.57    ( ! [X2] : (k1_xboole_0 != X2 | ~v1_relat_1(k1_xboole_0) | r2_hidden(k4_tarski(sK1(k1_xboole_0,sK0,X2),sK3(k1_xboole_0,sK0,X2)),k1_xboole_0) | r2_hidden(sK1(k1_xboole_0,sK0,X2),X2)) )),
% 1.52/0.57    inference(superposition,[],[f17,f19])).
% 1.52/0.57  fof(f19,plain,(
% 1.52/0.57    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK1(X0,X1,X2),sK3(X0,X1,X2)),X0) | r2_hidden(sK1(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 1.52/0.57    inference(cnf_transformation,[],[f15])).
% 1.52/0.57  fof(f15,plain,(
% 1.52/0.57    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.52/0.57    inference(ennf_transformation,[],[f9])).
% 1.52/0.57  fof(f9,axiom,(
% 1.52/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 1.52/0.57  fof(f17,plain,(
% 1.52/0.57    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.52/0.57    inference(cnf_transformation,[],[f14])).
% 1.52/0.57  fof(f14,plain,(
% 1.52/0.57    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 1.52/0.57    inference(ennf_transformation,[],[f12])).
% 1.52/0.57  fof(f12,negated_conjecture,(
% 1.52/0.57    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.52/0.57    inference(negated_conjecture,[],[f11])).
% 1.52/0.57  fof(f11,conjecture,(
% 1.52/0.57    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.52/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 1.52/0.57  % SZS output end Proof for theBenchmark
% 1.52/0.57  % (26505)------------------------------
% 1.52/0.57  % (26505)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.57  % (26505)Termination reason: Refutation
% 1.52/0.57  
% 1.52/0.57  % (26505)Memory used [KB]: 10746
% 1.52/0.57  % (26505)Time elapsed: 0.145 s
% 1.52/0.57  % (26505)------------------------------
% 1.52/0.57  % (26505)------------------------------
% 1.52/0.57  % (26495)Success in time 0.204 s
%------------------------------------------------------------------------------
