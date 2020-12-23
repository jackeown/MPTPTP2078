%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:27 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   66 (  97 expanded)
%              Number of leaves         :   18 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :  153 ( 227 expanded)
%              Number of equality atoms :   41 (  71 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f70,f75,f88,f97,f101,f106,f114,f117,f118])).

fof(f118,plain,
    ( sK0 != sK2
    | k2_tarski(sK0,sK2) = k2_tarski(sK0,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f117,plain,
    ( ~ spl5_1
    | spl5_9 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl5_1
    | spl5_9 ),
    inference(unit_resulting_resolution,[],[f60,f113,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f18])).

fof(f18,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f113,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK0),sK1)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl5_9
  <=> r1_tarski(k2_tarski(sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f60,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f114,plain,
    ( ~ spl5_9
    | ~ spl5_2
    | spl5_5 ),
    inference(avatar_split_clause,[],[f107,f81,f63,f111])).

fof(f63,plain,
    ( spl5_2
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f81,plain,
    ( spl5_5
  <=> r1_tarski(k2_tarski(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f107,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK0),sK1)
    | ~ spl5_2
    | spl5_5 ),
    inference(backward_demodulation,[],[f83,f65])).

fof(f65,plain,
    ( sK0 = sK2
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f83,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK2),sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f106,plain,
    ( ~ spl5_1
    | ~ spl5_7 ),
    inference(avatar_contradiction_clause,[],[f102])).

fof(f102,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(unit_resulting_resolution,[],[f60,f92,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f92,plain,
    ( r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_7
  <=> r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f101,plain,
    ( spl5_3
    | spl5_8 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl5_3
    | spl5_8 ),
    inference(unit_resulting_resolution,[],[f69,f49,f96,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k4_xboole_0(X0,X1))
      | r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f96,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl5_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_8
  <=> r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f49,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_tarski(X0,X3)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f69,plain,
    ( ~ r2_hidden(sK2,sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl5_3
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f97,plain,
    ( spl5_7
    | ~ spl5_8
    | spl5_4 ),
    inference(avatar_split_clause,[],[f79,f72,f94,f90])).

fof(f72,plain,
    ( spl5_4
  <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f79,plain,
    ( ~ r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl5_4 ),
    inference(trivial_inequality_removal,[],[f77])).

fof(f77,plain,
    ( k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0)
    | ~ r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl5_4 ),
    inference(superposition,[],[f74,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f36,f18])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f74,plain,
    ( k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))
    | spl5_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f88,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | spl5_4 ),
    inference(avatar_split_clause,[],[f78,f72,f85,f81])).

fof(f85,plain,
    ( spl5_6
  <=> k2_tarski(sK0,sK2) = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f78,plain,
    ( k2_tarski(sK0,sK2) != k2_tarski(sK0,sK0)
    | ~ r1_tarski(k2_tarski(sK0,sK2),sK1)
    | spl5_4 ),
    inference(superposition,[],[f74,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f75,plain,(
    ~ spl5_4 ),
    inference(avatar_split_clause,[],[f40,f72])).

fof(f40,plain,(
    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) ),
    inference(definition_unfolding,[],[f17,f18,f19])).

fof(f17,plain,(
    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & ( X0 = X2
        | ~ r2_hidden(X2,X1) )
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,X1)
       => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
          | ( X0 != X2
            & r2_hidden(X2,X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,X1)
     => ( k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1)
        | ( X0 != X2
          & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).

fof(f70,plain,
    ( spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f15,f67,f63])).

fof(f15,plain,
    ( ~ r2_hidden(sK2,sK1)
    | sK0 = sK2 ),
    inference(cnf_transformation,[],[f12])).

fof(f61,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f16,f58])).

fof(f16,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:11:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (858)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (874)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (866)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.28/0.53  % (854)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.28/0.54  % (855)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.28/0.54  % (856)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.28/0.54  % (857)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.28/0.54  % (878)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.41/0.55  % (860)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.41/0.55  % (880)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.41/0.55  % (870)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.41/0.55  % (851)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.41/0.55  % (861)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.41/0.55  % (881)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.41/0.55  % (880)Refutation found. Thanks to Tanya!
% 1.41/0.55  % SZS status Theorem for theBenchmark
% 1.41/0.55  % SZS output start Proof for theBenchmark
% 1.41/0.55  fof(f119,plain,(
% 1.41/0.55    $false),
% 1.41/0.55    inference(avatar_sat_refutation,[],[f61,f70,f75,f88,f97,f101,f106,f114,f117,f118])).
% 1.41/0.55  fof(f118,plain,(
% 1.41/0.55    sK0 != sK2 | k2_tarski(sK0,sK2) = k2_tarski(sK0,sK0)),
% 1.41/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.41/0.55  fof(f117,plain,(
% 1.41/0.55    ~spl5_1 | spl5_9),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f115])).
% 1.41/0.55  fof(f115,plain,(
% 1.41/0.55    $false | (~spl5_1 | spl5_9)),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f60,f113,f43])).
% 1.41/0.55  fof(f43,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.41/0.55    inference(definition_unfolding,[],[f22,f18])).
% 1.41/0.55  fof(f18,plain,(
% 1.41/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f6])).
% 1.41/0.55  fof(f6,axiom,(
% 1.41/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.41/0.55  fof(f22,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f7])).
% 1.41/0.55  fof(f7,axiom,(
% 1.41/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.41/0.55  fof(f113,plain,(
% 1.41/0.55    ~r1_tarski(k2_tarski(sK0,sK0),sK1) | spl5_9),
% 1.41/0.55    inference(avatar_component_clause,[],[f111])).
% 1.41/0.55  fof(f111,plain,(
% 1.41/0.55    spl5_9 <=> r1_tarski(k2_tarski(sK0,sK0),sK1)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.41/0.55  fof(f60,plain,(
% 1.41/0.55    r2_hidden(sK0,sK1) | ~spl5_1),
% 1.41/0.55    inference(avatar_component_clause,[],[f58])).
% 1.41/0.55  fof(f58,plain,(
% 1.41/0.55    spl5_1 <=> r2_hidden(sK0,sK1)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.41/0.55  fof(f114,plain,(
% 1.41/0.55    ~spl5_9 | ~spl5_2 | spl5_5),
% 1.41/0.55    inference(avatar_split_clause,[],[f107,f81,f63,f111])).
% 1.41/0.55  fof(f63,plain,(
% 1.41/0.55    spl5_2 <=> sK0 = sK2),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.41/0.55  fof(f81,plain,(
% 1.41/0.55    spl5_5 <=> r1_tarski(k2_tarski(sK0,sK2),sK1)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.41/0.55  fof(f107,plain,(
% 1.41/0.55    ~r1_tarski(k2_tarski(sK0,sK0),sK1) | (~spl5_2 | spl5_5)),
% 1.41/0.55    inference(backward_demodulation,[],[f83,f65])).
% 1.41/0.55  fof(f65,plain,(
% 1.41/0.55    sK0 = sK2 | ~spl5_2),
% 1.41/0.55    inference(avatar_component_clause,[],[f63])).
% 1.41/0.55  fof(f83,plain,(
% 1.41/0.55    ~r1_tarski(k2_tarski(sK0,sK2),sK1) | spl5_5),
% 1.41/0.55    inference(avatar_component_clause,[],[f81])).
% 1.41/0.55  fof(f106,plain,(
% 1.41/0.55    ~spl5_1 | ~spl5_7),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f102])).
% 1.41/0.55  fof(f102,plain,(
% 1.41/0.55    $false | (~spl5_1 | ~spl5_7)),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f60,f92,f54])).
% 1.41/0.55  fof(f54,plain,(
% 1.41/0.55    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) )),
% 1.41/0.55    inference(equality_resolution,[],[f34])).
% 1.41/0.55  fof(f34,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.55    inference(cnf_transformation,[],[f1])).
% 1.41/0.55  fof(f1,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 1.41/0.55  fof(f92,plain,(
% 1.41/0.55    r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | ~spl5_7),
% 1.41/0.55    inference(avatar_component_clause,[],[f90])).
% 1.41/0.55  fof(f90,plain,(
% 1.41/0.55    spl5_7 <=> r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.41/0.55  fof(f101,plain,(
% 1.41/0.55    spl5_3 | spl5_8),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f98])).
% 1.41/0.55  fof(f98,plain,(
% 1.41/0.55    $false | (spl5_3 | spl5_8)),
% 1.41/0.55    inference(unit_resulting_resolution,[],[f69,f49,f96,f53])).
% 1.41/0.55  fof(f53,plain,(
% 1.41/0.55    ( ! [X0,X3,X1] : (r2_hidden(X3,k4_xboole_0(X0,X1)) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.41/0.55    inference(equality_resolution,[],[f35])).
% 1.41/0.55  fof(f35,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 1.41/0.55    inference(cnf_transformation,[],[f1])).
% 1.41/0.55  fof(f96,plain,(
% 1.41/0.55    ~r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl5_8),
% 1.41/0.55    inference(avatar_component_clause,[],[f94])).
% 1.41/0.55  fof(f94,plain,(
% 1.41/0.55    spl5_8 <=> r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.41/0.55  fof(f49,plain,(
% 1.41/0.55    ( ! [X0,X3] : (r2_hidden(X3,k2_tarski(X0,X3))) )),
% 1.41/0.55    inference(equality_resolution,[],[f48])).
% 1.41/0.55  fof(f48,plain,(
% 1.41/0.55    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k2_tarski(X0,X3) != X2) )),
% 1.41/0.55    inference(equality_resolution,[],[f29])).
% 1.41/0.55  fof(f29,plain,(
% 1.41/0.55    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.41/0.55    inference(cnf_transformation,[],[f5])).
% 1.41/0.55  fof(f5,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.41/0.55  fof(f69,plain,(
% 1.41/0.55    ~r2_hidden(sK2,sK1) | spl5_3),
% 1.41/0.55    inference(avatar_component_clause,[],[f67])).
% 1.41/0.55  fof(f67,plain,(
% 1.41/0.55    spl5_3 <=> r2_hidden(sK2,sK1)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.41/0.55  fof(f97,plain,(
% 1.41/0.55    spl5_7 | ~spl5_8 | spl5_4),
% 1.41/0.55    inference(avatar_split_clause,[],[f79,f72,f94,f90])).
% 1.41/0.55  fof(f72,plain,(
% 1.41/0.55    spl5_4 <=> k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.41/0.55  fof(f79,plain,(
% 1.41/0.55    ~r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl5_4),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f77])).
% 1.41/0.55  fof(f77,plain,(
% 1.41/0.55    k2_tarski(sK0,sK0) != k2_tarski(sK0,sK0) | ~r2_hidden(sK2,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl5_4),
% 1.41/0.55    inference(superposition,[],[f74,f47])).
% 1.41/0.55  fof(f47,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.41/0.55    inference(definition_unfolding,[],[f36,f18])).
% 1.41/0.55  fof(f36,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f8])).
% 1.41/0.55  fof(f8,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 1.41/0.55  fof(f74,plain,(
% 1.41/0.55    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1)) | spl5_4),
% 1.41/0.55    inference(avatar_component_clause,[],[f72])).
% 1.41/0.55  fof(f88,plain,(
% 1.41/0.55    ~spl5_5 | ~spl5_6 | spl5_4),
% 1.41/0.55    inference(avatar_split_clause,[],[f78,f72,f85,f81])).
% 1.41/0.55  fof(f85,plain,(
% 1.41/0.55    spl5_6 <=> k2_tarski(sK0,sK2) = k2_tarski(sK0,sK0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.41/0.55  fof(f78,plain,(
% 1.41/0.55    k2_tarski(sK0,sK2) != k2_tarski(sK0,sK0) | ~r1_tarski(k2_tarski(sK0,sK2),sK1) | spl5_4),
% 1.41/0.55    inference(superposition,[],[f74,f41])).
% 1.41/0.55  fof(f41,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.41/0.55    inference(definition_unfolding,[],[f20,f19])).
% 1.41/0.55  fof(f19,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f4])).
% 1.41/0.55  fof(f4,axiom,(
% 1.41/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.41/0.55  fof(f20,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.41/0.55    inference(cnf_transformation,[],[f13])).
% 1.41/0.55  fof(f13,plain,(
% 1.41/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f2])).
% 1.41/0.55  fof(f2,axiom,(
% 1.41/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.41/0.55  fof(f75,plain,(
% 1.41/0.55    ~spl5_4),
% 1.41/0.55    inference(avatar_split_clause,[],[f40,f72])).
% 1.41/0.55  fof(f40,plain,(
% 1.41/0.55    k2_tarski(sK0,sK0) != k4_xboole_0(k2_tarski(sK0,sK2),k4_xboole_0(k2_tarski(sK0,sK2),sK1))),
% 1.41/0.55    inference(definition_unfolding,[],[f17,f18,f19])).
% 1.41/0.55  fof(f17,plain,(
% 1.41/0.55    k1_tarski(sK0) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f12])).
% 1.41/0.55  fof(f12,plain,(
% 1.41/0.55    ? [X0,X1,X2] : (k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 1.41/0.55    inference(flattening,[],[f11])).
% 1.41/0.55  fof(f11,plain,(
% 1.41/0.55    ? [X0,X1,X2] : ((k1_tarski(X0) != k3_xboole_0(k2_tarski(X0,X2),X1) & (X0 = X2 | ~r2_hidden(X2,X1))) & r2_hidden(X0,X1))),
% 1.41/0.55    inference(ennf_transformation,[],[f10])).
% 1.41/0.55  fof(f10,negated_conjecture,(
% 1.41/0.55    ~! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 1.41/0.55    inference(negated_conjecture,[],[f9])).
% 1.41/0.55  fof(f9,conjecture,(
% 1.41/0.55    ! [X0,X1,X2] : (r2_hidden(X0,X1) => (k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X2),X1) | (X0 != X2 & r2_hidden(X2,X1))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_zfmisc_1)).
% 1.41/0.55  fof(f70,plain,(
% 1.41/0.55    spl5_2 | ~spl5_3),
% 1.41/0.55    inference(avatar_split_clause,[],[f15,f67,f63])).
% 1.41/0.55  fof(f15,plain,(
% 1.41/0.55    ~r2_hidden(sK2,sK1) | sK0 = sK2),
% 1.41/0.55    inference(cnf_transformation,[],[f12])).
% 1.41/0.55  fof(f61,plain,(
% 1.41/0.55    spl5_1),
% 1.41/0.55    inference(avatar_split_clause,[],[f16,f58])).
% 1.41/0.55  fof(f16,plain,(
% 1.41/0.55    r2_hidden(sK0,sK1)),
% 1.41/0.55    inference(cnf_transformation,[],[f12])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (880)------------------------------
% 1.41/0.55  % (880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (880)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (880)Memory used [KB]: 10746
% 1.41/0.55  % (880)Time elapsed: 0.139 s
% 1.41/0.55  % (880)------------------------------
% 1.41/0.55  % (880)------------------------------
% 1.41/0.55  % (879)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.41/0.55  % (881)Refutation not found, incomplete strategy% (881)------------------------------
% 1.41/0.55  % (881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (881)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (881)Memory used [KB]: 1663
% 1.41/0.55  % (881)Time elapsed: 0.138 s
% 1.41/0.55  % (881)------------------------------
% 1.41/0.55  % (881)------------------------------
% 1.41/0.56  % (872)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.41/0.56  % (864)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.41/0.56  % (876)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.41/0.56  % (871)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.41/0.56  % (865)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.41/0.56  % (873)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.41/0.56  % (862)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.41/0.56  % (863)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.41/0.57  % (852)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.41/0.57  % (868)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.41/0.57  % (850)Success in time 0.209 s
%------------------------------------------------------------------------------
