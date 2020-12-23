%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:16 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   38 (  52 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :   14
%              Number of atoms          :   63 (  87 expanded)
%              Number of equality atoms :   41 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f203])).

fof(f203,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f199])).

fof(f199,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f77,f186])).

fof(f186,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(forward_demodulation,[],[f185,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

fof(f185,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(forward_demodulation,[],[f184,f166])).

fof(f166,plain,(
    ! [X6,X7] : k1_tarski(X7) = k2_relat_1(k1_tarski(k4_tarski(X6,X7))) ),
    inference(forward_demodulation,[],[f165,f48])).

fof(f48,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f165,plain,(
    ! [X6,X7] : k2_tarski(X7,X7) = k2_relat_1(k1_tarski(k4_tarski(X6,X7))) ),
    inference(subsumption_resolution,[],[f159,f58])).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_relat_1)).

fof(f159,plain,(
    ! [X6,X7] :
      ( k2_tarski(X7,X7) = k2_relat_1(k1_tarski(k4_tarski(X6,X7)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(X6,X7))) ) ),
    inference(superposition,[],[f72,f48])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relat_1(X4) = k2_tarski(X1,X3)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3,X4] :
      ( ( k2_relat_1(X4) = k2_tarski(X1,X3)
        & k1_relat_1(X4) = k2_tarski(X0,X2) )
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] :
      ( v1_relat_1(X4)
     => ( k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4
       => ( k2_relat_1(X4) = k2_tarski(X1,X3)
          & k1_relat_1(X4) = k2_tarski(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).

fof(f184,plain,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_xboole_0(k1_tarski(X0),k2_relat_1(k1_tarski(k4_tarski(X0,X1)))) ),
    inference(subsumption_resolution,[],[f183,f58])).

fof(f183,plain,(
    ! [X0,X1] :
      ( k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_xboole_0(k1_tarski(X0),k2_relat_1(k1_tarski(k4_tarski(X0,X1))))
      | ~ v1_relat_1(k1_tarski(k4_tarski(X0,X1))) ) ),
    inference(superposition,[],[f49,f177])).

fof(f177,plain,(
    ! [X6,X7] : k1_tarski(X6) = k1_relat_1(k1_tarski(k4_tarski(X6,X7))) ),
    inference(forward_demodulation,[],[f176,f48])).

fof(f176,plain,(
    ! [X6,X7] : k2_tarski(X6,X6) = k1_relat_1(k1_tarski(k4_tarski(X6,X7))) ),
    inference(subsumption_resolution,[],[f170,f58])).

fof(f170,plain,(
    ! [X6,X7] :
      ( k2_tarski(X6,X6) = k1_relat_1(k1_tarski(k4_tarski(X6,X7)))
      | ~ v1_relat_1(k1_tarski(k4_tarski(X6,X7))) ) ),
    inference(superposition,[],[f73,f48])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))
      | ~ v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k1_relat_1(X4) = k2_tarski(X0,X2)
      | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4
      | ~ v1_relat_1(X4) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f49,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f77,plain,
    ( k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_1
  <=> k2_tarski(sK0,sK1) = k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f78,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f35,f75])).

fof(f35,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f21])).

fof(f21,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))
   => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:04:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.51  % (29030)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (29033)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (29054)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (29054)Refutation not found, incomplete strategy% (29054)------------------------------
% 0.21/0.52  % (29054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (29054)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (29054)Memory used [KB]: 10618
% 0.21/0.52  % (29054)Time elapsed: 0.115 s
% 0.21/0.52  % (29054)------------------------------
% 0.21/0.52  % (29054)------------------------------
% 1.23/0.52  % (29059)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.23/0.52  % (29057)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.23/0.53  % (29046)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.23/0.53  % (29038)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.23/0.53  % (29056)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.23/0.53  % (29056)Refutation not found, incomplete strategy% (29056)------------------------------
% 1.23/0.53  % (29056)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (29056)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (29056)Memory used [KB]: 6140
% 1.23/0.53  % (29056)Time elapsed: 0.116 s
% 1.23/0.53  % (29056)------------------------------
% 1.23/0.53  % (29056)------------------------------
% 1.23/0.53  % (29044)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.23/0.53  % (29040)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.23/0.53  % (29043)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.23/0.54  % (29042)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.23/0.54  % (29032)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.23/0.54  % (29041)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.23/0.54  % (29046)Refutation not found, incomplete strategy% (29046)------------------------------
% 1.23/0.54  % (29046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (29046)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (29046)Memory used [KB]: 10618
% 1.23/0.54  % (29046)Time elapsed: 0.136 s
% 1.23/0.54  % (29046)------------------------------
% 1.23/0.54  % (29046)------------------------------
% 1.23/0.54  % (29051)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.23/0.54  % (29042)Refutation not found, incomplete strategy% (29042)------------------------------
% 1.23/0.54  % (29042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.54  % (29042)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.54  
% 1.23/0.54  % (29042)Memory used [KB]: 10618
% 1.23/0.54  % (29042)Time elapsed: 0.131 s
% 1.23/0.54  % (29042)------------------------------
% 1.23/0.54  % (29042)------------------------------
% 1.23/0.54  % (29034)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.36/0.54  % (29035)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.36/0.54  % (29051)Refutation found. Thanks to Tanya!
% 1.36/0.54  % SZS status Theorem for theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f204,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(avatar_sat_refutation,[],[f78,f203])).
% 1.36/0.54  fof(f203,plain,(
% 1.36/0.54    spl4_1),
% 1.36/0.54    inference(avatar_contradiction_clause,[],[f199])).
% 1.36/0.54  fof(f199,plain,(
% 1.36/0.54    $false | spl4_1),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f77,f186])).
% 1.36/0.54  fof(f186,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 1.36/0.54    inference(forward_demodulation,[],[f185,f46])).
% 1.36/0.54  fof(f46,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).
% 1.36/0.54  fof(f185,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),k1_tarski(X1)) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 1.36/0.54    inference(forward_demodulation,[],[f184,f166])).
% 1.36/0.54  fof(f166,plain,(
% 1.36/0.54    ( ! [X6,X7] : (k1_tarski(X7) = k2_relat_1(k1_tarski(k4_tarski(X6,X7)))) )),
% 1.36/0.54    inference(forward_demodulation,[],[f165,f48])).
% 1.36/0.54  fof(f48,plain,(
% 1.36/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.36/0.54  fof(f165,plain,(
% 1.36/0.54    ( ! [X6,X7] : (k2_tarski(X7,X7) = k2_relat_1(k1_tarski(k4_tarski(X6,X7)))) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f159,f58])).
% 1.36/0.54  fof(f58,plain,(
% 1.36/0.54    ( ! [X0,X1] : (v1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f13])).
% 1.36/0.54  fof(f13,axiom,(
% 1.36/0.54    ! [X0,X1] : v1_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_relat_1)).
% 1.36/0.54  fof(f159,plain,(
% 1.36/0.54    ( ! [X6,X7] : (k2_tarski(X7,X7) = k2_relat_1(k1_tarski(k4_tarski(X6,X7))) | ~v1_relat_1(k1_tarski(k4_tarski(X6,X7)))) )),
% 1.36/0.54    inference(superposition,[],[f72,f48])).
% 1.36/0.54  fof(f72,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (k2_tarski(X1,X3) = k2_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.36/0.54    inference(equality_resolution,[],[f60])).
% 1.36/0.54  fof(f60,plain,(
% 1.36/0.54    ( ! [X4,X2,X0,X3,X1] : (k2_relat_1(X4) = k2_tarski(X1,X3) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f20])).
% 1.36/0.54  fof(f20,plain,(
% 1.36/0.54    ! [X0,X1,X2,X3,X4] : ((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4))),
% 1.36/0.54    inference(flattening,[],[f19])).
% 1.36/0.54  fof(f19,plain,(
% 1.36/0.54    ! [X0,X1,X2,X3,X4] : (((k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2)) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4) | ~v1_relat_1(X4))),
% 1.36/0.54    inference(ennf_transformation,[],[f14])).
% 1.36/0.54  fof(f14,axiom,(
% 1.36/0.54    ! [X0,X1,X2,X3,X4] : (v1_relat_1(X4) => (k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) = X4 => (k2_relat_1(X4) = k2_tarski(X1,X3) & k1_relat_1(X4) = k2_tarski(X0,X2))))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relat_1)).
% 1.36/0.54  fof(f184,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_xboole_0(k1_tarski(X0),k2_relat_1(k1_tarski(k4_tarski(X0,X1))))) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f183,f58])).
% 1.36/0.54  fof(f183,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_xboole_0(k1_tarski(X0),k2_relat_1(k1_tarski(k4_tarski(X0,X1)))) | ~v1_relat_1(k1_tarski(k4_tarski(X0,X1)))) )),
% 1.36/0.54    inference(superposition,[],[f49,f177])).
% 1.36/0.54  fof(f177,plain,(
% 1.36/0.54    ( ! [X6,X7] : (k1_tarski(X6) = k1_relat_1(k1_tarski(k4_tarski(X6,X7)))) )),
% 1.36/0.54    inference(forward_demodulation,[],[f176,f48])).
% 1.36/0.54  fof(f176,plain,(
% 1.36/0.54    ( ! [X6,X7] : (k2_tarski(X6,X6) = k1_relat_1(k1_tarski(k4_tarski(X6,X7)))) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f170,f58])).
% 1.36/0.54  fof(f170,plain,(
% 1.36/0.54    ( ! [X6,X7] : (k2_tarski(X6,X6) = k1_relat_1(k1_tarski(k4_tarski(X6,X7))) | ~v1_relat_1(k1_tarski(k4_tarski(X6,X7)))) )),
% 1.36/0.54    inference(superposition,[],[f73,f48])).
% 1.36/0.54  fof(f73,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (k2_tarski(X0,X2) = k1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3))) | ~v1_relat_1(k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)))) )),
% 1.36/0.54    inference(equality_resolution,[],[f59])).
% 1.36/0.54  fof(f59,plain,(
% 1.36/0.54    ( ! [X4,X2,X0,X3,X1] : (k1_relat_1(X4) = k2_tarski(X0,X2) | k2_tarski(k4_tarski(X0,X1),k4_tarski(X2,X3)) != X4 | ~v1_relat_1(X4)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f20])).
% 1.36/0.54  fof(f49,plain,(
% 1.36/0.54    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f18])).
% 1.36/0.54  fof(f18,plain,(
% 1.36/0.54    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.36/0.54    inference(ennf_transformation,[],[f12])).
% 1.36/0.54  fof(f12,axiom,(
% 1.36/0.54    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.36/0.54  fof(f77,plain,(
% 1.36/0.54    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1))) | spl4_1),
% 1.36/0.54    inference(avatar_component_clause,[],[f75])).
% 1.36/0.54  fof(f75,plain,(
% 1.36/0.54    spl4_1 <=> k2_tarski(sK0,sK1) = k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 1.36/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.36/0.54  fof(f78,plain,(
% 1.36/0.54    ~spl4_1),
% 1.36/0.54    inference(avatar_split_clause,[],[f35,f75])).
% 1.36/0.54  fof(f35,plain,(
% 1.36/0.54    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 1.36/0.54    inference(cnf_transformation,[],[f22])).
% 1.36/0.54  fof(f22,plain,(
% 1.36/0.54    k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 1.36/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f21])).
% 1.36/0.54  fof(f21,plain,(
% 1.36/0.54    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1))) => k2_tarski(sK0,sK1) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK1)))),
% 1.36/0.54    introduced(choice_axiom,[])).
% 1.36/0.54  fof(f17,plain,(
% 1.36/0.54    ? [X0,X1] : k2_tarski(X0,X1) != k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 1.36/0.54    inference(ennf_transformation,[],[f16])).
% 1.36/0.54  fof(f16,negated_conjecture,(
% 1.36/0.54    ~! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 1.36/0.54    inference(negated_conjecture,[],[f15])).
% 1.36/0.54  fof(f15,conjecture,(
% 1.36/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k3_relat_1(k1_tarski(k4_tarski(X0,X1)))),
% 1.36/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relat_1)).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (29051)------------------------------
% 1.36/0.54  % (29051)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (29051)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (29051)Memory used [KB]: 6268
% 1.36/0.54  % (29051)Time elapsed: 0.135 s
% 1.36/0.54  % (29051)------------------------------
% 1.36/0.54  % (29051)------------------------------
% 1.36/0.54  % (29029)Success in time 0.176 s
%------------------------------------------------------------------------------
