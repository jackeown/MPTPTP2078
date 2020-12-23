%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 114 expanded)
%              Number of leaves         :    9 (  34 expanded)
%              Depth                    :   10
%              Number of atoms          :  128 ( 293 expanded)
%              Number of equality atoms :   24 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (32613)Time elapsed: 0.130 s
% (32613)------------------------------
% (32613)------------------------------
fof(f146,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f53,f100,f145])).

fof(f145,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f26,f39,f128,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f128,plain,
    ( r2_hidden(sK3(sK1,sK0),k1_xboole_0)
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(forward_demodulation,[],[f121,f48])).

fof(f48,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl7_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f121,plain,
    ( r2_hidden(sK3(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f15,f101,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f101,plain,
    ( r2_hidden(k4_tarski(sK0,sK3(sK1,sK0)),sK1)
    | ~ spl7_1 ),
    inference(unit_resulting_resolution,[],[f45,f35])).

fof(f35,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f45,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl7_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f39,plain,(
    ! [X2] : r2_hidden(X2,k2_tarski(X2,X2)) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k2_tarski(X2,X2) != X1 ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f20,f27])).

fof(f27,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f26,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f100,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f96])).

fof(f96,plain,
    ( $false
    | spl7_1
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f26,f39,f81,f28])).

fof(f81,plain,
    ( r2_hidden(sK2(k11_relat_1(sK1,sK0),k1_xboole_0),k1_xboole_0)
    | spl7_1
    | spl7_2 ),
    inference(unit_resulting_resolution,[],[f49,f69])).

fof(f69,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k11_relat_1(sK1,sK0),X0),X0)
        | k11_relat_1(sK1,sK0) = X0 )
    | spl7_1 ),
    inference(forward_demodulation,[],[f65,f62])).

fof(f62,plain,
    ( k11_relat_1(sK1,sK0) = k1_relat_1(k11_relat_1(sK1,sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f57,f57,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f57,plain,
    ( ! [X0] : ~ r2_hidden(X0,k11_relat_1(sK1,sK0))
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f15,f54,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f54,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),sK1)
    | spl7_1 ),
    inference(unit_resulting_resolution,[],[f44,f36])).

fof(f36,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X2,X3),X0) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f44,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f65,plain,
    ( ! [X0] :
        ( r2_hidden(sK2(k11_relat_1(sK1,sK0),X0),X0)
        | k1_relat_1(k11_relat_1(sK1,sK0)) = X0 )
    | spl7_1 ),
    inference(resolution,[],[f57,f18])).

fof(f49,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f47])).

fof(f53,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f14,f47,f43])).

fof(f14,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f50,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f13,f47,f43])).

fof(f13,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:36:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (32587)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.47  % (32611)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.48  % (32610)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.48  % (32586)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (32596)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.50  % (32601)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (32589)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (32615)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (32591)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (32588)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (32596)Refutation not found, incomplete strategy% (32596)------------------------------
% 0.21/0.52  % (32596)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32596)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32596)Memory used [KB]: 10618
% 0.21/0.52  % (32596)Time elapsed: 0.133 s
% 0.21/0.52  % (32596)------------------------------
% 0.21/0.52  % (32596)------------------------------
% 0.21/0.53  % (32593)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (32598)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (32605)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (32590)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (32609)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (32612)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (32603)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (32613)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (32613)Refutation not found, incomplete strategy% (32613)------------------------------
% 0.21/0.54  % (32613)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32613)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (32612)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (32613)Memory used [KB]: 6140
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  % (32613)Time elapsed: 0.130 s
% 0.21/0.54  % (32613)------------------------------
% 0.21/0.54  % (32613)------------------------------
% 0.21/0.54  fof(f146,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f50,f53,f100,f145])).
% 0.21/0.54  fof(f145,plain,(
% 0.21/0.54    ~spl7_1 | ~spl7_2),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f142])).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    $false | (~spl7_1 | ~spl7_2)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f26,f39,f128,f28])).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,plain,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    inference(rectify,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.54  fof(f128,plain,(
% 0.21/0.54    r2_hidden(sK3(sK1,sK0),k1_xboole_0) | (~spl7_1 | ~spl7_2)),
% 0.21/0.54    inference(forward_demodulation,[],[f121,f48])).
% 0.21/0.54  fof(f48,plain,(
% 0.21/0.54    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl7_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f47])).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    spl7_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    r2_hidden(sK3(sK1,sK0),k11_relat_1(sK1,sK0)) | ~spl7_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f15,f101,f25])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,plain,(
% 0.21/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 0.21/0.54  fof(f101,plain,(
% 0.21/0.54    r2_hidden(k4_tarski(sK0,sK3(sK1,sK0)),sK1) | ~spl7_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f45,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.21/0.54    inference(equality_resolution,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK3(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl7_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f43])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    spl7_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    v1_relat_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,plain,(
% 0.21/0.54    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.54    inference(negated_conjecture,[],[f7])).
% 0.21/0.54  fof(f7,conjecture,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X2] : (r2_hidden(X2,k2_tarski(X2,X2))) )),
% 0.21/0.54    inference(equality_resolution,[],[f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X2,X1] : (r2_hidden(X2,X1) | k2_tarski(X2,X2) != X1) )),
% 0.21/0.54    inference(equality_resolution,[],[f34])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k2_tarski(X0,X0) != X1) )),
% 0.21/0.54    inference(definition_unfolding,[],[f20,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.54  fof(f100,plain,(
% 0.21/0.54    spl7_1 | spl7_2),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f96])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    $false | (spl7_1 | spl7_2)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f26,f39,f81,f28])).
% 0.21/0.54  fof(f81,plain,(
% 0.21/0.54    r2_hidden(sK2(k11_relat_1(sK1,sK0),k1_xboole_0),k1_xboole_0) | (spl7_1 | spl7_2)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f49,f69])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK2(k11_relat_1(sK1,sK0),X0),X0) | k11_relat_1(sK1,sK0) = X0) ) | spl7_1),
% 0.21/0.54    inference(forward_demodulation,[],[f65,f62])).
% 0.21/0.54  fof(f62,plain,(
% 0.21/0.54    k11_relat_1(sK1,sK0) = k1_relat_1(k11_relat_1(sK1,sK0)) | spl7_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f57,f57,f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK2(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(X0,k11_relat_1(sK1,sK0))) ) | spl7_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f15,f54,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,X0),sK1)) ) | spl7_1),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f44,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X2,X0,X3] : (r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X3),X0)) )),
% 0.21/0.54    inference(equality_resolution,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl7_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f43])).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    ( ! [X0] : (r2_hidden(sK2(k11_relat_1(sK1,sK0),X0),X0) | k1_relat_1(k11_relat_1(sK1,sK0)) = X0) ) | spl7_1),
% 0.21/0.54    inference(resolution,[],[f57,f18])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    k1_xboole_0 != k11_relat_1(sK1,sK0) | spl7_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f47])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ~spl7_1 | spl7_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f14,f47,f43])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    spl7_1 | ~spl7_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f13,f47,f43])).
% 0.21/0.54  fof(f13,plain,(
% 0.21/0.54    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (32612)------------------------------
% 0.21/0.54  % (32612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (32612)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (32612)Memory used [KB]: 6268
% 0.21/0.54  % (32612)Time elapsed: 0.132 s
% 0.21/0.54  % (32612)------------------------------
% 0.21/0.54  % (32612)------------------------------
% 0.21/0.54  % (32585)Success in time 0.18 s
%------------------------------------------------------------------------------
