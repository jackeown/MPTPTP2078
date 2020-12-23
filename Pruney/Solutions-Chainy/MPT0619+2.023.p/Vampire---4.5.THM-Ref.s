%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:49 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 444 expanded)
%              Number of leaves         :   13 ( 113 expanded)
%              Depth                    :   14
%              Number of atoms          :  174 ( 966 expanded)
%              Number of equality atoms :   72 ( 534 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f223,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f157,f173,f222])).

fof(f222,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f219])).

fof(f219,plain,
    ( $false
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f123,f214])).

fof(f214,plain,
    ( ~ r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))
    | ~ spl4_3 ),
    inference(forward_demodulation,[],[f201,f193])).

fof(f193,plain,
    ( k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f130,f187])).

fof(f187,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k2_relat_1(sK1))
        | k1_funct_1(sK1,sK0) = X2 )
    | ~ spl4_3 ),
    inference(superposition,[],[f184,f122])).

fof(f122,plain,(
    k2_relat_1(sK1) = k11_relat_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f121,f65])).

fof(f65,plain,(
    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1] :
      ( k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0))
      & k1_tarski(X0) = k1_relat_1(X1)
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v1_funct_1(X1)
          & v1_relat_1(X1) )
       => ( k1_tarski(X0) = k1_relat_1(X1)
         => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( k1_tarski(X0) = k1_relat_1(X1)
       => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

fof(f121,plain,(
    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0) ),
    inference(superposition,[],[f66,f49])).

fof(f49,plain,(
    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f24,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f24,plain,(
    k1_tarski(sK0) = k1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f22,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f34,f47])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k11_relat_1(sK1,X0))
        | k1_funct_1(sK1,X0) = X1 )
    | ~ spl4_3 ),
    inference(resolution,[],[f172,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(X1,X0),sK1)
      | ~ r2_hidden(X0,k11_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f22,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).

fof(f172,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(k4_tarski(X2,X3),sK1)
        | k1_funct_1(sK1,X2) = X3 )
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl4_3
  <=> ! [X3,X2] :
        ( k1_funct_1(sK1,X2) = X3
        | ~ r2_hidden(k4_tarski(X2,X3),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f130,plain,(
    r2_hidden(sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f48,f127,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).

fof(f127,plain,(
    k1_xboole_0 != k2_relat_1(sK1) ),
    inference(superposition,[],[f79,f122])).

fof(f79,plain,(
    k1_xboole_0 != k11_relat_1(sK1,sK0) ),
    inference(unit_resulting_resolution,[],[f22,f76,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k11_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).

fof(f76,plain,(
    r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(superposition,[],[f63,f49])).

fof(f63,plain,(
    ! [X3,X1] : r2_hidden(X3,k2_enumset1(X3,X3,X3,X1)) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X3,X1] :
      ( r2_hidden(X3,X2)
      | k2_enumset1(X3,X3,X3,X1) != X2 ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f40,f46])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f48,plain,(
    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0)) ),
    inference(definition_unfolding,[],[f25,f47])).

fof(f25,plain,(
    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f201,plain,
    ( ~ r2_hidden(sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f131,f187])).

fof(f131,plain,(
    k1_funct_1(sK1,sK0) != sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f48,f127,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK2(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f123,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(backward_demodulation,[],[f101,f122])).

fof(f101,plain,(
    r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0)) ),
    inference(unit_resulting_resolution,[],[f22,f80,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f80,plain,(
    r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f22,f23,f76,f59])).

fof(f59,plain,(
    ! [X2,X0] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ v1_funct_1(X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | k1_funct_1(X2,X0) != X1
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f23,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f173,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f73,f150,f171])).

fof(f150,plain,
    ( spl4_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f73,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(sK1)
      | k1_funct_1(sK1,X2) = X3
      | ~ r2_hidden(k4_tarski(X2,X3),sK1) ) ),
    inference(resolution,[],[f23,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2)
      | k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f157,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f154])).

fof(f154,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f22,f152])).

fof(f152,plain,
    ( ~ v1_relat_1(sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f150])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n012.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:44:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.13/0.52  % (8150)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.13/0.52  % (8146)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.13/0.52  % (8153)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.13/0.52  % (8152)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.13/0.52  % (8146)Refutation not found, incomplete strategy% (8146)------------------------------
% 1.13/0.52  % (8146)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.13/0.52  % (8146)Termination reason: Refutation not found, incomplete strategy
% 1.13/0.52  
% 1.13/0.52  % (8146)Memory used [KB]: 1663
% 1.13/0.52  % (8146)Time elapsed: 0.100 s
% 1.13/0.52  % (8146)------------------------------
% 1.13/0.52  % (8146)------------------------------
% 1.13/0.52  % (8149)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.13/0.53  % (8164)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.13/0.53  % (8167)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.13/0.53  % (8168)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.13/0.53  % (8158)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.13/0.53  % (8162)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.13/0.53  % (8166)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.13/0.53  % (8156)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.13/0.53  % (8163)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.34/0.53  % (8160)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.34/0.54  % (8174)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.54  % (8174)Refutation not found, incomplete strategy% (8174)------------------------------
% 1.34/0.54  % (8174)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (8174)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (8174)Memory used [KB]: 1663
% 1.34/0.54  % (8174)Time elapsed: 0.102 s
% 1.34/0.54  % (8174)------------------------------
% 1.34/0.54  % (8174)------------------------------
% 1.34/0.54  % (8154)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.34/0.54  % (8145)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.34/0.54  % (8159)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.34/0.54  % (8171)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.34/0.54  % (8148)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.34/0.54  % (8172)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.34/0.54  % (8151)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (8170)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.54  % (8147)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.34/0.54  % (8173)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.34/0.54  % (8170)Refutation found. Thanks to Tanya!
% 1.34/0.54  % SZS status Theorem for theBenchmark
% 1.34/0.54  % SZS output start Proof for theBenchmark
% 1.34/0.54  fof(f223,plain,(
% 1.34/0.54    $false),
% 1.34/0.54    inference(avatar_sat_refutation,[],[f157,f173,f222])).
% 1.34/0.54  fof(f222,plain,(
% 1.34/0.54    ~spl4_3),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f219])).
% 1.34/0.54  fof(f219,plain,(
% 1.34/0.54    $false | ~spl4_3),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f123,f214])).
% 1.34/0.54  fof(f214,plain,(
% 1.34/0.54    ~r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1)) | ~spl4_3),
% 1.34/0.54    inference(forward_demodulation,[],[f201,f193])).
% 1.34/0.54  fof(f193,plain,(
% 1.34/0.54    k1_funct_1(sK1,sK0) = sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)) | ~spl4_3),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f130,f187])).
% 1.34/0.54  fof(f187,plain,(
% 1.34/0.54    ( ! [X2] : (~r2_hidden(X2,k2_relat_1(sK1)) | k1_funct_1(sK1,sK0) = X2) ) | ~spl4_3),
% 1.34/0.54    inference(superposition,[],[f184,f122])).
% 1.34/0.54  fof(f122,plain,(
% 1.34/0.54    k2_relat_1(sK1) = k11_relat_1(sK1,sK0)),
% 1.34/0.54    inference(forward_demodulation,[],[f121,f65])).
% 1.34/0.54  fof(f65,plain,(
% 1.34/0.54    k2_relat_1(sK1) = k9_relat_1(sK1,k1_relat_1(sK1))),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f22,f29])).
% 1.34/0.54  fof(f29,plain,(
% 1.34/0.54    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f17])).
% 1.34/0.54  fof(f17,plain,(
% 1.34/0.54    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f7])).
% 1.34/0.54  fof(f7,axiom,(
% 1.34/0.54    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 1.34/0.54  fof(f22,plain,(
% 1.34/0.54    v1_relat_1(sK1)),
% 1.34/0.54    inference(cnf_transformation,[],[f14])).
% 1.34/0.54  fof(f14,plain,(
% 1.34/0.54    ? [X0,X1] : (k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1) & v1_funct_1(X1) & v1_relat_1(X1))),
% 1.34/0.54    inference(flattening,[],[f13])).
% 1.34/0.54  fof(f13,plain,(
% 1.34/0.54    ? [X0,X1] : ((k2_relat_1(X1) != k1_tarski(k1_funct_1(X1,X0)) & k1_tarski(X0) = k1_relat_1(X1)) & (v1_funct_1(X1) & v1_relat_1(X1)))),
% 1.34/0.54    inference(ennf_transformation,[],[f12])).
% 1.34/0.54  fof(f12,negated_conjecture,(
% 1.34/0.54    ~! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.34/0.54    inference(negated_conjecture,[],[f11])).
% 1.34/0.54  fof(f11,conjecture,(
% 1.34/0.54    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_tarski(X0) = k1_relat_1(X1) => k2_relat_1(X1) = k1_tarski(k1_funct_1(X1,X0))))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).
% 1.34/0.54  fof(f121,plain,(
% 1.34/0.54    k9_relat_1(sK1,k1_relat_1(sK1)) = k11_relat_1(sK1,sK0)),
% 1.34/0.54    inference(superposition,[],[f66,f49])).
% 1.34/0.54  fof(f49,plain,(
% 1.34/0.54    k1_relat_1(sK1) = k2_enumset1(sK0,sK0,sK0,sK0)),
% 1.34/0.54    inference(definition_unfolding,[],[f24,f47])).
% 1.34/0.54  fof(f47,plain,(
% 1.34/0.54    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f35,f46])).
% 1.34/0.54  fof(f46,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.34/0.54    inference(definition_unfolding,[],[f44,f45])).
% 1.34/0.54  fof(f45,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f4])).
% 1.34/0.54  fof(f4,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.34/0.54  fof(f44,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f3])).
% 1.34/0.54  fof(f3,axiom,(
% 1.34/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.34/0.54  fof(f35,plain,(
% 1.34/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f2])).
% 1.34/0.54  fof(f2,axiom,(
% 1.34/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.34/0.54  fof(f24,plain,(
% 1.34/0.54    k1_tarski(sK0) = k1_relat_1(sK1)),
% 1.34/0.54    inference(cnf_transformation,[],[f14])).
% 1.34/0.54  fof(f66,plain,(
% 1.34/0.54    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k2_enumset1(X0,X0,X0,X0))) )),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f22,f52])).
% 1.34/0.54  fof(f52,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.34/0.54    inference(definition_unfolding,[],[f34,f47])).
% 1.34/0.54  fof(f34,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f20])).
% 1.34/0.54  fof(f20,plain,(
% 1.34/0.54    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.34/0.54    inference(ennf_transformation,[],[f6])).
% 1.34/0.54  fof(f6,axiom,(
% 1.34/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_relat_1)).
% 1.34/0.54  fof(f184,plain,(
% 1.34/0.54    ( ! [X0,X1] : (~r2_hidden(X1,k11_relat_1(sK1,X0)) | k1_funct_1(sK1,X0) = X1) ) | ~spl4_3),
% 1.34/0.54    inference(resolution,[],[f172,f67])).
% 1.34/0.54  fof(f67,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r2_hidden(k4_tarski(X1,X0),sK1) | ~r2_hidden(X0,k11_relat_1(sK1,X1))) )),
% 1.34/0.54    inference(resolution,[],[f22,f42])).
% 1.34/0.54  fof(f42,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f21])).
% 1.34/0.54  fof(f21,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 1.34/0.54    inference(ennf_transformation,[],[f8])).
% 1.34/0.54  fof(f8,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t204_relat_1)).
% 1.34/0.54  fof(f172,plain,(
% 1.34/0.54    ( ! [X2,X3] : (~r2_hidden(k4_tarski(X2,X3),sK1) | k1_funct_1(sK1,X2) = X3) ) | ~spl4_3),
% 1.34/0.54    inference(avatar_component_clause,[],[f171])).
% 1.34/0.54  fof(f171,plain,(
% 1.34/0.54    spl4_3 <=> ! [X3,X2] : (k1_funct_1(sK1,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK1))),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.34/0.54  fof(f130,plain,(
% 1.34/0.54    r2_hidden(sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1))),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f48,f127,f51])).
% 1.34/0.54  fof(f51,plain,(
% 1.34/0.54    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.34/0.54    inference(definition_unfolding,[],[f32,f47])).
% 1.34/0.54  fof(f32,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK2(X0,X1),X0)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f19])).
% 1.34/0.54  fof(f19,plain,(
% 1.34/0.54    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 1.34/0.54    inference(ennf_transformation,[],[f5])).
% 1.34/0.54  fof(f5,axiom,(
% 1.34/0.54    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_zfmisc_1)).
% 1.34/0.54  fof(f127,plain,(
% 1.34/0.54    k1_xboole_0 != k2_relat_1(sK1)),
% 1.34/0.54    inference(superposition,[],[f79,f122])).
% 1.34/0.54  fof(f79,plain,(
% 1.34/0.54    k1_xboole_0 != k11_relat_1(sK1,sK0)),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f22,f76,f31])).
% 1.34/0.54  fof(f31,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_xboole_0 != k11_relat_1(X1,X0) | ~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1))) )),
% 1.34/0.54    inference(cnf_transformation,[],[f18])).
% 1.34/0.54  fof(f18,plain,(
% 1.34/0.54    ! [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 1.34/0.54    inference(ennf_transformation,[],[f9])).
% 1.34/0.54  fof(f9,axiom,(
% 1.34/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t205_relat_1)).
% 1.34/0.54  fof(f76,plain,(
% 1.34/0.54    r2_hidden(sK0,k1_relat_1(sK1))),
% 1.34/0.54    inference(superposition,[],[f63,f49])).
% 1.34/0.54  fof(f63,plain,(
% 1.34/0.54    ( ! [X3,X1] : (r2_hidden(X3,k2_enumset1(X3,X3,X3,X1))) )),
% 1.34/0.54    inference(equality_resolution,[],[f62])).
% 1.34/0.54  fof(f62,plain,(
% 1.34/0.54    ( ! [X2,X3,X1] : (r2_hidden(X3,X2) | k2_enumset1(X3,X3,X3,X1) != X2) )),
% 1.34/0.54    inference(equality_resolution,[],[f54])).
% 1.34/0.54  fof(f54,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 1.34/0.54    inference(definition_unfolding,[],[f40,f46])).
% 1.34/0.54  fof(f40,plain,(
% 1.34/0.54    ( ! [X2,X0,X3,X1] : (X0 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.34/0.54    inference(cnf_transformation,[],[f1])).
% 1.34/0.54  fof(f1,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.34/0.54  fof(f48,plain,(
% 1.34/0.54    k2_relat_1(sK1) != k2_enumset1(k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0),k1_funct_1(sK1,sK0))),
% 1.34/0.54    inference(definition_unfolding,[],[f25,f47])).
% 1.34/0.54  fof(f25,plain,(
% 1.34/0.54    k2_relat_1(sK1) != k1_tarski(k1_funct_1(sK1,sK0))),
% 1.34/0.54    inference(cnf_transformation,[],[f14])).
% 1.34/0.54  fof(f201,plain,(
% 1.34/0.54    ~r2_hidden(sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0)),k2_relat_1(sK1)) | ~spl4_3),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f131,f187])).
% 1.34/0.54  fof(f131,plain,(
% 1.34/0.54    k1_funct_1(sK1,sK0) != sK2(k2_relat_1(sK1),k1_funct_1(sK1,sK0))),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f48,f127,f50])).
% 1.34/0.54  fof(f50,plain,(
% 1.34/0.54    ( ! [X0,X1] : (sK2(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.34/0.54    inference(definition_unfolding,[],[f33,f47])).
% 1.34/0.54  fof(f33,plain,(
% 1.34/0.54    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK2(X0,X1) != X1) )),
% 1.34/0.54    inference(cnf_transformation,[],[f19])).
% 1.34/0.54  fof(f123,plain,(
% 1.34/0.54    r2_hidden(k1_funct_1(sK1,sK0),k2_relat_1(sK1))),
% 1.34/0.54    inference(backward_demodulation,[],[f101,f122])).
% 1.34/0.54  fof(f101,plain,(
% 1.34/0.54    r2_hidden(k1_funct_1(sK1,sK0),k11_relat_1(sK1,sK0))),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f22,f80,f43])).
% 1.34/0.54  fof(f43,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f21])).
% 1.34/0.54  fof(f80,plain,(
% 1.34/0.54    r2_hidden(k4_tarski(sK0,k1_funct_1(sK1,sK0)),sK1)),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f22,f23,f76,f59])).
% 1.34/0.54  fof(f59,plain,(
% 1.34/0.54    ( ! [X2,X0] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)) )),
% 1.34/0.54    inference(equality_resolution,[],[f28])).
% 1.34/0.54  fof(f28,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~v1_funct_1(X2) | ~r2_hidden(X0,k1_relat_1(X2)) | k1_funct_1(X2,X0) != X1 | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f16])).
% 1.34/0.54  fof(f16,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 1.34/0.54    inference(flattening,[],[f15])).
% 1.34/0.54  fof(f15,plain,(
% 1.34/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 1.34/0.54    inference(ennf_transformation,[],[f10])).
% 1.34/0.54  fof(f10,axiom,(
% 1.34/0.54    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.34/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).
% 1.34/0.54  fof(f23,plain,(
% 1.34/0.54    v1_funct_1(sK1)),
% 1.34/0.54    inference(cnf_transformation,[],[f14])).
% 1.34/0.54  fof(f173,plain,(
% 1.34/0.54    spl4_3 | ~spl4_2),
% 1.34/0.54    inference(avatar_split_clause,[],[f73,f150,f171])).
% 1.34/0.54  fof(f150,plain,(
% 1.34/0.54    spl4_2 <=> v1_relat_1(sK1)),
% 1.34/0.54    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.34/0.54  fof(f73,plain,(
% 1.34/0.54    ( ! [X2,X3] : (~v1_relat_1(sK1) | k1_funct_1(sK1,X2) = X3 | ~r2_hidden(k4_tarski(X2,X3),sK1)) )),
% 1.34/0.54    inference(resolution,[],[f23,f27])).
% 1.34/0.54  fof(f27,plain,(
% 1.34/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_relat_1(X2) | k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.34/0.54    inference(cnf_transformation,[],[f16])).
% 1.34/0.54  fof(f157,plain,(
% 1.34/0.54    spl4_2),
% 1.34/0.54    inference(avatar_contradiction_clause,[],[f154])).
% 1.34/0.54  fof(f154,plain,(
% 1.34/0.54    $false | spl4_2),
% 1.34/0.54    inference(unit_resulting_resolution,[],[f22,f152])).
% 1.34/0.54  fof(f152,plain,(
% 1.34/0.54    ~v1_relat_1(sK1) | spl4_2),
% 1.34/0.54    inference(avatar_component_clause,[],[f150])).
% 1.34/0.54  % SZS output end Proof for theBenchmark
% 1.34/0.54  % (8170)------------------------------
% 1.34/0.54  % (8170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (8170)Termination reason: Refutation
% 1.34/0.54  
% 1.34/0.54  % (8170)Memory used [KB]: 6268
% 1.34/0.54  % (8170)Time elapsed: 0.130 s
% 1.34/0.54  % (8170)------------------------------
% 1.34/0.54  % (8170)------------------------------
% 1.34/0.55  % (8155)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.34/0.55  % (8144)Success in time 0.183 s
%------------------------------------------------------------------------------
