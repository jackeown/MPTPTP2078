%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 203 expanded)
%              Number of leaves         :   17 (  69 expanded)
%              Depth                    :   11
%              Number of atoms          :  153 ( 353 expanded)
%              Number of equality atoms :   51 ( 153 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f245,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f96,f126,f159,f198,f223])).

fof(f223,plain,
    ( spl8_2
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f215])).

fof(f215,plain,
    ( $false
    | spl8_2
    | ~ spl8_4 ),
    inference(unit_resulting_resolution,[],[f61,f121,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f121,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl8_4
  <=> ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f61,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl8_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f198,plain,(
    ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f35,f189])).

fof(f189,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl8_5 ),
    inference(backward_demodulation,[],[f185,f188])).

fof(f188,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl8_5 ),
    inference(superposition,[],[f50,f176])).

fof(f176,plain,
    ( k1_xboole_0 = k2_tarski(sK3(k1_xboole_0),sK3(k1_xboole_0))
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f173,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f173,plain,
    ( r1_tarski(k2_tarski(sK3(k1_xboole_0),sK3(k1_xboole_0)),k1_xboole_0)
    | ~ spl8_5 ),
    inference(unit_resulting_resolution,[],[f125,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_tarski(X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f45])).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f125,plain,
    ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl8_5
  <=> r2_hidden(sK3(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X0) = k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f44,f45,f45])).

fof(f44,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f185,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl8_5 ),
    inference(superposition,[],[f53,f176])).

fof(f53,plain,(
    ! [X1] : k2_tarski(X1,X1) != k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1))) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k2_tarski(X0,X0) != k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1))) ) ),
    inference(definition_unfolding,[],[f43,f45,f41,f45,f45])).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f35,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f159,plain,(
    spl8_3 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f35,f150])).

fof(f150,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl8_3 ),
    inference(backward_demodulation,[],[f146,f149])).

fof(f149,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl8_3 ),
    inference(superposition,[],[f50,f135])).

fof(f135,plain,
    ( k1_xboole_0 = k2_tarski(sK5(k1_xboole_0),sK5(k1_xboole_0))
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f130,f34])).

fof(f130,plain,
    ( r1_tarski(k2_tarski(sK5(k1_xboole_0),sK5(k1_xboole_0)),k1_xboole_0)
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f127,f47])).

fof(f127,plain,
    ( r2_hidden(sK5(k1_xboole_0),k1_xboole_0)
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f118,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | r2_hidden(sK5(X0),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f118,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl8_3
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f146,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | spl8_3 ),
    inference(superposition,[],[f53,f135])).

fof(f126,plain,
    ( ~ spl8_3
    | spl8_4
    | spl8_5
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f107,f55,f123,f120,f116])).

fof(f55,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f107,plain,
    ( ! [X0] :
        ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl8_1 ),
    inference(superposition,[],[f32,f56])).

fof(f56,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

fof(f96,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f35,f87])).

fof(f87,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl8_1 ),
    inference(backward_demodulation,[],[f83,f86])).

fof(f86,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl8_1 ),
    inference(superposition,[],[f50,f74])).

fof(f74,plain,
    ( k1_xboole_0 = k2_tarski(k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0))),k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0))))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f71,f34])).

fof(f71,plain,
    ( r1_tarski(k2_tarski(k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0))),k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0)))),k1_xboole_0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f67,f47])).

fof(f67,plain,
    ( r2_hidden(k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0))),k1_xboole_0)
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f64,f51])).

fof(f51,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK1(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f64,plain,
    ( r2_hidden(sK4(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | spl8_1 ),
    inference(unit_resulting_resolution,[],[f57,f33])).

fof(f57,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f83,plain,
    ( k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | spl8_1 ),
    inference(superposition,[],[f53,f74])).

fof(f62,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f27,f59,f55])).

fof(f27,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:38:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (7704)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (7695)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (7720)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.52  % (7696)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (7701)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (7701)Refutation not found, incomplete strategy% (7701)------------------------------
% 0.20/0.52  % (7701)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7701)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (7701)Memory used [KB]: 10618
% 0.20/0.52  % (7701)Time elapsed: 0.112 s
% 0.20/0.52  % (7701)------------------------------
% 0.20/0.52  % (7701)------------------------------
% 0.20/0.52  % (7695)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f245,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f62,f96,f126,f159,f198,f223])).
% 0.20/0.52  fof(f223,plain,(
% 0.20/0.52    spl8_2 | ~spl8_4),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f215])).
% 0.20/0.52  fof(f215,plain,(
% 0.20/0.52    $false | (spl8_2 | ~spl8_4)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f61,f121,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK4(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) ) | ~spl8_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f120])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    spl8_4 <=> ! [X0] : ~r2_hidden(X0,k1_relat_1(k1_xboole_0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl8_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    spl8_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.52  fof(f198,plain,(
% 0.20/0.52    ~spl8_5),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f190])).
% 0.20/0.52  fof(f190,plain,(
% 0.20/0.52    $false | ~spl8_5),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f35,f189])).
% 0.20/0.52  fof(f189,plain,(
% 0.20/0.52    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl8_5),
% 0.20/0.52    inference(backward_demodulation,[],[f185,f188])).
% 0.20/0.52  fof(f188,plain,(
% 0.20/0.52    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl8_5),
% 0.20/0.52    inference(superposition,[],[f50,f176])).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    k1_xboole_0 = k2_tarski(sK3(k1_xboole_0),sK3(k1_xboole_0)) | ~spl8_5),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f173,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    r1_tarski(k2_tarski(sK3(k1_xboole_0),sK3(k1_xboole_0)),k1_xboole_0) | ~spl8_5),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f125,f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f39,f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,axiom,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    r2_hidden(sK3(k1_xboole_0),k1_xboole_0) | ~spl8_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f123])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    spl8_5 <=> r2_hidden(sK3(k1_xboole_0),k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X0) = k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f44,f45,f45])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,axiom,(
% 0.20/0.52    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 0.20/0.52  fof(f185,plain,(
% 0.20/0.52    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) | ~spl8_5),
% 0.20/0.52    inference(superposition,[],[f53,f176])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X1] : (k2_tarski(X1,X1) != k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X1,X1)))) )),
% 0.20/0.52    inference(equality_resolution,[],[f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (X0 != X1 | k2_tarski(X0,X0) != k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X1,X1)))) )),
% 0.20/0.52    inference(definition_unfolding,[],[f43,f45,f41,f45,f45])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f14])).
% 0.20/0.52  fof(f14,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.52  fof(f159,plain,(
% 0.20/0.52    spl8_3),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f151])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    $false | spl8_3),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f35,f150])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | spl8_3),
% 0.20/0.52    inference(backward_demodulation,[],[f146,f149])).
% 0.20/0.52  fof(f149,plain,(
% 0.20/0.52    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | spl8_3),
% 0.20/0.52    inference(superposition,[],[f50,f135])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    k1_xboole_0 = k2_tarski(sK5(k1_xboole_0),sK5(k1_xboole_0)) | spl8_3),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f130,f34])).
% 0.20/0.52  fof(f130,plain,(
% 0.20/0.52    r1_tarski(k2_tarski(sK5(k1_xboole_0),sK5(k1_xboole_0)),k1_xboole_0) | spl8_3),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f127,f47])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    r2_hidden(sK5(k1_xboole_0),k1_xboole_0) | spl8_3),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f118,f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ( ! [X0] : (v1_relat_1(X0) | r2_hidden(sK5(X0),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    ~v1_relat_1(k1_xboole_0) | spl8_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f116])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    spl8_3 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) | spl8_3),
% 0.20/0.52    inference(superposition,[],[f53,f135])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    ~spl8_3 | spl8_4 | spl8_5 | ~spl8_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f107,f55,f123,f120,f116])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    spl8_1 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    ( ! [X0] : (r2_hidden(sK3(k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)) ) | ~spl8_1),
% 0.20/0.52    inference(superposition,[],[f32,f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl8_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f55])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    spl8_1),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    $false | spl8_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f35,f87])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k1_xboole_0) | spl8_1),
% 0.20/0.52    inference(backward_demodulation,[],[f83,f86])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k1_xboole_0) | spl8_1),
% 0.20/0.52    inference(superposition,[],[f50,f74])).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    k1_xboole_0 = k2_tarski(k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0))),k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0)))) | spl8_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f71,f34])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    r1_tarski(k2_tarski(k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0))),k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0)))),k1_xboole_0) | spl8_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f67,f47])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    r2_hidden(k4_tarski(sK1(k1_xboole_0,sK4(k2_relat_1(k1_xboole_0))),sK4(k2_relat_1(k1_xboole_0))),k1_xboole_0) | spl8_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f64,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK1(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 0.20/0.52    inference(equality_resolution,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,axiom,(
% 0.20/0.52    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    r2_hidden(sK4(k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) | spl8_1),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f57,f33])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl8_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f55])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    k1_xboole_0 != k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,k1_xboole_0)) | spl8_1),
% 0.20/0.52    inference(superposition,[],[f53,f74])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ~spl8_1 | ~spl8_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f27,f59,f55])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.52    inference(ennf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,negated_conjecture,(
% 0.20/0.52    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.20/0.52    inference(negated_conjecture,[],[f19])).
% 0.20/0.52  fof(f19,conjecture,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (7695)------------------------------
% 0.20/0.52  % (7695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7695)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (7695)Memory used [KB]: 6268
% 0.20/0.52  % (7695)Time elapsed: 0.112 s
% 0.20/0.52  % (7695)------------------------------
% 0.20/0.52  % (7695)------------------------------
% 0.20/0.53  % (7690)Success in time 0.169 s
%------------------------------------------------------------------------------
