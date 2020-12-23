%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:43 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 128 expanded)
%              Number of leaves         :   15 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :  137 ( 224 expanded)
%              Number of equality atoms :   36 ( 101 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f61,f70,f74,f85,f105])).

fof(f105,plain,
    ( spl2_2
    | spl2_4
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | spl2_2
    | spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f94,f92,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f30,f35])).

fof(f35,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f34])).

fof(f34,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f92,plain,
    ( ~ r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl2_4
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f84,f80])).

fof(f80,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,sK0)
        | ~ r1_tarski(sK0,X0) )
    | spl2_4 ),
    inference(resolution,[],[f75,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f75,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | spl2_4 ),
    inference(unit_resulting_resolution,[],[f69,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f69,plain,
    ( k1_xboole_0 != sK0
    | spl2_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl2_4
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f84,plain,
    ( r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl2_5
  <=> r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f94,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl2_2
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f91,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_enumset1(X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f35])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f91,plain,
    ( ~ r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0)
    | spl2_2
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f54,f84,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f54,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl2_2
  <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f85,plain,
    ( spl2_5
    | spl2_2
    | spl2_4 ),
    inference(avatar_split_clause,[],[f36,f67,f52,f82])).

fof(f36,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k2_enumset1(sK1,sK1,sK1,sK1)
    | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f20,f35,f35])).

fof(f20,plain,
    ( k1_xboole_0 = sK0
    | sK0 = k1_tarski(sK1)
    | r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <~> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,k1_tarski(X1))
      <=> ( k1_tarski(X1) = X0
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).

fof(f74,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f26,f65])).

fof(f65,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))
    | spl2_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_3
  <=> r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f26,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f70,plain,
    ( ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f46,f67,f63])).

fof(f46,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(inner_rewriting,[],[f38])).

fof(f38,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f18,f35])).

fof(f18,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f56])).

fof(f56,plain,
    ( $false
    | spl2_1 ),
    inference(unit_resulting_resolution,[],[f43,f50])).

fof(f50,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl2_1
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f55,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f45,f52,f48])).

fof(f45,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r1_tarski(sK0,sK0) ),
    inference(inner_rewriting,[],[f37])).

fof(f37,plain,
    ( sK0 != k2_enumset1(sK1,sK1,sK1,sK1)
    | ~ r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(definition_unfolding,[],[f19,f35,f35])).

fof(f19,plain,
    ( sK0 != k1_tarski(sK1)
    | ~ r1_tarski(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:01:45 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (31401)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.24/0.52  % (31396)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.24/0.52  % (31413)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.24/0.53  % (31402)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.24/0.53  % (31397)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.24/0.53  % (31421)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.24/0.53  % (31413)Refutation not found, incomplete strategy% (31413)------------------------------
% 1.24/0.53  % (31413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (31405)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.24/0.53  % (31413)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (31413)Memory used [KB]: 1663
% 1.24/0.53  % (31413)Time elapsed: 0.118 s
% 1.24/0.53  % (31413)------------------------------
% 1.24/0.53  % (31413)------------------------------
% 1.24/0.53  % (31397)Refutation not found, incomplete strategy% (31397)------------------------------
% 1.24/0.53  % (31397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.53  % (31397)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.53  
% 1.24/0.53  % (31397)Memory used [KB]: 1663
% 1.24/0.53  % (31397)Time elapsed: 0.088 s
% 1.24/0.53  % (31397)------------------------------
% 1.24/0.53  % (31397)------------------------------
% 1.32/0.53  % (31403)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.32/0.53  % (31409)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.32/0.53  % (31421)Refutation found. Thanks to Tanya!
% 1.32/0.53  % SZS status Theorem for theBenchmark
% 1.32/0.53  % SZS output start Proof for theBenchmark
% 1.32/0.53  fof(f106,plain,(
% 1.32/0.53    $false),
% 1.32/0.53    inference(avatar_sat_refutation,[],[f55,f61,f70,f74,f85,f105])).
% 1.32/0.53  fof(f105,plain,(
% 1.32/0.53    spl2_2 | spl2_4 | ~spl2_5),
% 1.32/0.53    inference(avatar_contradiction_clause,[],[f101])).
% 1.32/0.53  fof(f101,plain,(
% 1.32/0.53    $false | (spl2_2 | spl2_4 | ~spl2_5)),
% 1.32/0.53    inference(unit_resulting_resolution,[],[f94,f92,f41])).
% 1.32/0.53  fof(f41,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k2_enumset1(X0,X0,X0,X0),X1)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f30,f35])).
% 1.32/0.53  fof(f35,plain,(
% 1.32/0.53    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f31,f34])).
% 1.32/0.53  fof(f34,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.32/0.53    inference(definition_unfolding,[],[f32,f33])).
% 1.32/0.53  fof(f33,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f7])).
% 1.32/0.53  fof(f7,axiom,(
% 1.32/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.53  fof(f32,plain,(
% 1.32/0.53    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f6])).
% 1.32/0.53  fof(f6,axiom,(
% 1.32/0.53    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.53  fof(f31,plain,(
% 1.32/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f5])).
% 1.32/0.53  fof(f5,axiom,(
% 1.32/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.53  fof(f30,plain,(
% 1.32/0.53    ( ! [X0,X1] : (r2_hidden(X0,X1) | r1_xboole_0(k1_tarski(X0),X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f17])).
% 1.32/0.53  fof(f17,plain,(
% 1.32/0.53    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.32/0.53    inference(ennf_transformation,[],[f10])).
% 1.32/0.53  fof(f10,axiom,(
% 1.32/0.53    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.32/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.32/0.53  fof(f92,plain,(
% 1.32/0.53    ~r1_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | (spl2_4 | ~spl2_5)),
% 1.32/0.53    inference(unit_resulting_resolution,[],[f84,f80])).
% 1.32/0.53  fof(f80,plain,(
% 1.32/0.53    ( ! [X0] : (~r1_xboole_0(X0,sK0) | ~r1_tarski(sK0,X0)) ) | spl2_4),
% 1.32/0.53    inference(resolution,[],[f75,f27])).
% 1.32/0.53  fof(f27,plain,(
% 1.32/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 1.32/0.53    inference(cnf_transformation,[],[f16])).
% 1.32/0.53  fof(f16,plain,(
% 1.32/0.53    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.32/0.53    inference(flattening,[],[f15])).
% 1.32/0.54  fof(f15,plain,(
% 1.32/0.54    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.32/0.54    inference(ennf_transformation,[],[f3])).
% 1.32/0.54  fof(f3,axiom,(
% 1.32/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.32/0.54  fof(f75,plain,(
% 1.32/0.54    ~r1_xboole_0(sK0,sK0) | spl2_4),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f69,f24])).
% 1.32/0.54  fof(f24,plain,(
% 1.32/0.54    ( ! [X0] : (~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) )),
% 1.32/0.54    inference(cnf_transformation,[],[f14])).
% 1.32/0.54  fof(f14,plain,(
% 1.32/0.54    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 1.32/0.54    inference(ennf_transformation,[],[f4])).
% 1.32/0.54  fof(f4,axiom,(
% 1.32/0.54    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.32/0.54  fof(f69,plain,(
% 1.32/0.54    k1_xboole_0 != sK0 | spl2_4),
% 1.32/0.54    inference(avatar_component_clause,[],[f67])).
% 1.32/0.54  fof(f67,plain,(
% 1.32/0.54    spl2_4 <=> k1_xboole_0 = sK0),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.32/0.54  fof(f84,plain,(
% 1.32/0.54    r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1)) | ~spl2_5),
% 1.32/0.54    inference(avatar_component_clause,[],[f82])).
% 1.32/0.54  fof(f82,plain,(
% 1.32/0.54    spl2_5 <=> r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.32/0.54  fof(f94,plain,(
% 1.32/0.54    ~r2_hidden(sK1,sK0) | (spl2_2 | ~spl2_5)),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f91,f40])).
% 1.32/0.54  fof(f40,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r1_tarski(k2_enumset1(X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.32/0.54    inference(definition_unfolding,[],[f28,f35])).
% 1.32/0.54  fof(f28,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f9])).
% 1.32/0.54  fof(f9,axiom,(
% 1.32/0.54    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.32/0.54  fof(f91,plain,(
% 1.32/0.54    ~r1_tarski(k2_enumset1(sK1,sK1,sK1,sK1),sK0) | (spl2_2 | ~spl2_5)),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f54,f84,f23])).
% 1.32/0.54  fof(f23,plain,(
% 1.32/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.32/0.54    inference(cnf_transformation,[],[f1])).
% 1.32/0.54  fof(f1,axiom,(
% 1.32/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.32/0.54  fof(f54,plain,(
% 1.32/0.54    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | spl2_2),
% 1.32/0.54    inference(avatar_component_clause,[],[f52])).
% 1.32/0.54  fof(f52,plain,(
% 1.32/0.54    spl2_2 <=> sK0 = k2_enumset1(sK1,sK1,sK1,sK1)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.32/0.54  fof(f85,plain,(
% 1.32/0.54    spl2_5 | spl2_2 | spl2_4),
% 1.32/0.54    inference(avatar_split_clause,[],[f36,f67,f52,f82])).
% 1.32/0.54  fof(f36,plain,(
% 1.32/0.54    k1_xboole_0 = sK0 | sK0 = k2_enumset1(sK1,sK1,sK1,sK1) | r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.32/0.54    inference(definition_unfolding,[],[f20,f35,f35])).
% 1.32/0.54  fof(f20,plain,(
% 1.32/0.54    k1_xboole_0 = sK0 | sK0 = k1_tarski(sK1) | r1_tarski(sK0,k1_tarski(sK1))),
% 1.32/0.54    inference(cnf_transformation,[],[f13])).
% 1.32/0.54  fof(f13,plain,(
% 1.32/0.54    ? [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <~> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.32/0.54    inference(ennf_transformation,[],[f12])).
% 1.32/0.54  fof(f12,negated_conjecture,(
% 1.32/0.54    ~! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.32/0.54    inference(negated_conjecture,[],[f11])).
% 1.32/0.54  fof(f11,conjecture,(
% 1.32/0.54    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_zfmisc_1)).
% 1.32/0.54  fof(f74,plain,(
% 1.32/0.54    spl2_3),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f71])).
% 1.32/0.54  fof(f71,plain,(
% 1.32/0.54    $false | spl2_3),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f26,f65])).
% 1.32/0.54  fof(f65,plain,(
% 1.32/0.54    ~r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1)) | spl2_3),
% 1.32/0.54    inference(avatar_component_clause,[],[f63])).
% 1.32/0.54  fof(f63,plain,(
% 1.32/0.54    spl2_3 <=> r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.32/0.54  fof(f26,plain,(
% 1.32/0.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.32/0.54    inference(cnf_transformation,[],[f2])).
% 1.32/0.54  fof(f2,axiom,(
% 1.32/0.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.32/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.32/0.54  fof(f70,plain,(
% 1.32/0.54    ~spl2_3 | ~spl2_4),
% 1.32/0.54    inference(avatar_split_clause,[],[f46,f67,f63])).
% 1.32/0.54  fof(f46,plain,(
% 1.32/0.54    k1_xboole_0 != sK0 | ~r1_tarski(k1_xboole_0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.32/0.54    inference(inner_rewriting,[],[f38])).
% 1.32/0.54  fof(f38,plain,(
% 1.32/0.54    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.32/0.54    inference(definition_unfolding,[],[f18,f35])).
% 1.32/0.54  fof(f18,plain,(
% 1.32/0.54    k1_xboole_0 != sK0 | ~r1_tarski(sK0,k1_tarski(sK1))),
% 1.32/0.54    inference(cnf_transformation,[],[f13])).
% 1.32/0.54  fof(f61,plain,(
% 1.32/0.54    spl2_1),
% 1.32/0.54    inference(avatar_contradiction_clause,[],[f56])).
% 1.32/0.54  fof(f56,plain,(
% 1.32/0.54    $false | spl2_1),
% 1.32/0.54    inference(unit_resulting_resolution,[],[f43,f50])).
% 1.32/0.54  fof(f50,plain,(
% 1.32/0.54    ~r1_tarski(sK0,sK0) | spl2_1),
% 1.32/0.54    inference(avatar_component_clause,[],[f48])).
% 1.32/0.54  fof(f48,plain,(
% 1.32/0.54    spl2_1 <=> r1_tarski(sK0,sK0)),
% 1.32/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.32/0.54  fof(f43,plain,(
% 1.32/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.32/0.54    inference(equality_resolution,[],[f21])).
% 1.32/0.54  fof(f21,plain,(
% 1.32/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 1.32/0.54    inference(cnf_transformation,[],[f1])).
% 1.32/0.54  fof(f55,plain,(
% 1.32/0.54    ~spl2_1 | ~spl2_2),
% 1.32/0.54    inference(avatar_split_clause,[],[f45,f52,f48])).
% 1.32/0.54  fof(f45,plain,(
% 1.32/0.54    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_tarski(sK0,sK0)),
% 1.32/0.54    inference(inner_rewriting,[],[f37])).
% 1.32/0.54  fof(f37,plain,(
% 1.32/0.54    sK0 != k2_enumset1(sK1,sK1,sK1,sK1) | ~r1_tarski(sK0,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.32/0.54    inference(definition_unfolding,[],[f19,f35,f35])).
% 1.32/0.54  fof(f19,plain,(
% 1.32/0.54    sK0 != k1_tarski(sK1) | ~r1_tarski(sK0,k1_tarski(sK1))),
% 1.32/0.54    inference(cnf_transformation,[],[f13])).
% 1.32/0.54  % SZS output end Proof for theBenchmark
% 1.32/0.54  % (31421)------------------------------
% 1.32/0.54  % (31421)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (31421)Termination reason: Refutation
% 1.32/0.54  
% 1.32/0.54  % (31421)Memory used [KB]: 6268
% 1.32/0.54  % (31421)Time elapsed: 0.118 s
% 1.32/0.54  % (31421)------------------------------
% 1.32/0.54  % (31421)------------------------------
% 1.32/0.54  % (31411)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.32/0.54  % (31395)Success in time 0.172 s
%------------------------------------------------------------------------------
