%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:28 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 357 expanded)
%              Number of leaves         :   10 (  96 expanded)
%              Depth                    :   13
%              Number of atoms          :  165 (1035 expanded)
%              Number of equality atoms :   26 ( 138 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f434,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f130,f319,f433])).

fof(f433,plain,
    ( ~ spl11_1
    | spl11_2 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | ~ spl11_1
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f29,f409,f409,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f16])).

% (19770)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (19772)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (19770)Refutation not found, incomplete strategy% (19770)------------------------------
% (19770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19770)Termination reason: Refutation not found, incomplete strategy

% (19770)Memory used [KB]: 10618
% (19770)Time elapsed: 0.117 s
% (19770)------------------------------
% (19770)------------------------------
% (19785)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% (19777)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (19781)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (19771)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (19771)Refutation not found, incomplete strategy% (19771)------------------------------
% (19771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19771)Termination reason: Refutation not found, incomplete strategy

% (19771)Memory used [KB]: 10618
% (19771)Time elapsed: 0.140 s
% (19771)------------------------------
% (19771)------------------------------
% (19777)Refutation not found, incomplete strategy% (19777)------------------------------
% (19777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (19777)Termination reason: Refutation not found, incomplete strategy

% (19777)Memory used [KB]: 10618
% (19777)Time elapsed: 0.140 s
% (19777)------------------------------
% (19777)------------------------------
% (19773)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (19789)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f16,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f409,plain,
    ( r2_hidden(sK6(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0)
    | ~ spl11_1
    | spl11_2 ),
    inference(forward_demodulation,[],[f403,f64])).

fof(f64,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl11_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f403,plain,
    ( r2_hidden(sK6(sK1,sK2(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0))
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f23,f322,f321,f332,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f332,plain,
    ( r2_hidden(k4_tarski(sK6(sK1,sK2(k2_relat_1(sK1),sK0)),sK2(k2_relat_1(sK1),sK0)),sK1)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f321,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK6(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f321,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f67,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl11_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl11_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f322,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0)
    | spl11_2 ),
    inference(unit_resulting_resolution,[],[f67,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f23,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f29,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f319,plain,
    ( spl11_1
    | ~ spl11_2 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl11_1
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f29,f304,f304,f24])).

fof(f304,plain,
    ( r2_hidden(sK5(k10_relat_1(sK1,sK0),k1_xboole_0),k1_xboole_0)
    | spl11_1
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f63,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k10_relat_1(sK1,sK0),X0),X0)
        | k10_relat_1(sK1,sK0) = X0 )
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f100,f92])).

fof(f92,plain,
    ( k10_relat_1(sK1,sK0) = k2_relat_1(k10_relat_1(sK1,sK0))
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f79,f88])).

fof(f88,plain,
    ( k10_relat_1(sK1,sK0) = k3_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f82,f50])).

fof(f50,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0)) ),
    inference(unit_resulting_resolution,[],[f23,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f82,plain,
    ( k3_xboole_0(k2_relat_1(sK1),sK0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),sK0))
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f23,f70,f70,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK10(X0,X1,X2),X1)
      | r2_hidden(sK8(X0,X1,X2),X2)
      | k10_relat_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f70,plain,
    ( ! [X0] : ~ r2_hidden(X0,k3_xboole_0(k2_relat_1(sK1),sK0))
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f68,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f68,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f79,plain,
    ( k3_xboole_0(k2_relat_1(sK1),sK0) = k2_relat_1(k3_xboole_0(k2_relat_1(sK1),sK0))
    | ~ spl11_2 ),
    inference(unit_resulting_resolution,[],[f70,f70,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f100,plain,
    ( ! [X0] :
        ( k2_relat_1(k10_relat_1(sK1,sK0)) = X0
        | r2_hidden(sK5(k10_relat_1(sK1,sK0),X0),X0) )
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f99,f88])).

fof(f99,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k10_relat_1(sK1,sK0),X0),X0)
        | k2_relat_1(k3_xboole_0(k2_relat_1(sK1),sK0)) = X0 )
    | ~ spl11_2 ),
    inference(forward_demodulation,[],[f83,f88])).

fof(f83,plain,
    ( ! [X0] :
        ( r2_hidden(sK5(k3_xboole_0(k2_relat_1(sK1),sK0),X0),X0)
        | k2_relat_1(k3_xboole_0(k2_relat_1(sK1),sK0)) = X0 )
    | ~ spl11_2 ),
    inference(resolution,[],[f70,f36])).

fof(f63,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f130,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f22,f66,f62])).

fof(f22,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f21,f66,f62])).

fof(f21,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:04:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (19783)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.49  % (19775)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (19762)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (19767)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (19766)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.51  % (19768)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (19769)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (19774)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.52  % (19784)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (19782)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (19782)Refutation not found, incomplete strategy% (19782)------------------------------
% 0.20/0.53  % (19782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19780)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (19776)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (19788)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (19760)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (19787)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (19764)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (19760)Refutation not found, incomplete strategy% (19760)------------------------------
% 0.20/0.53  % (19760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19760)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19760)Memory used [KB]: 1663
% 0.20/0.53  % (19760)Time elapsed: 0.120 s
% 0.20/0.53  % (19760)------------------------------
% 0.20/0.53  % (19760)------------------------------
% 0.20/0.53  % (19761)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (19763)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (19765)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (19769)Refutation not found, incomplete strategy% (19769)------------------------------
% 0.20/0.53  % (19769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (19769)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19769)Memory used [KB]: 10618
% 0.20/0.53  % (19769)Time elapsed: 0.126 s
% 0.20/0.53  % (19769)------------------------------
% 0.20/0.53  % (19769)------------------------------
% 0.20/0.53  % (19782)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (19782)Memory used [KB]: 10746
% 0.20/0.53  % (19782)Time elapsed: 0.123 s
% 0.20/0.53  % (19782)------------------------------
% 0.20/0.53  % (19782)------------------------------
% 0.20/0.54  % (19786)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.54  % (19778)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (19764)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  fof(f434,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(avatar_sat_refutation,[],[f69,f130,f319,f433])).
% 0.20/0.54  fof(f433,plain,(
% 0.20/0.54    ~spl11_1 | spl11_2),
% 0.20/0.54    inference(avatar_contradiction_clause,[],[f431])).
% 0.20/0.54  fof(f431,plain,(
% 0.20/0.54    $false | (~spl11_1 | spl11_2)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f29,f409,f409,f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f16])).
% 0.20/0.54  % (19770)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.54  % (19772)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (19770)Refutation not found, incomplete strategy% (19770)------------------------------
% 0.20/0.54  % (19770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (19770)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (19770)Memory used [KB]: 10618
% 0.20/0.54  % (19770)Time elapsed: 0.117 s
% 0.20/0.54  % (19770)------------------------------
% 0.20/0.54  % (19770)------------------------------
% 0.20/0.54  % (19785)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (19777)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.55  % (19781)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.55  % (19771)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.55  % (19771)Refutation not found, incomplete strategy% (19771)------------------------------
% 1.45/0.55  % (19771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (19771)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (19771)Memory used [KB]: 10618
% 1.45/0.55  % (19771)Time elapsed: 0.140 s
% 1.45/0.55  % (19771)------------------------------
% 1.45/0.55  % (19771)------------------------------
% 1.45/0.55  % (19777)Refutation not found, incomplete strategy% (19777)------------------------------
% 1.45/0.55  % (19777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (19777)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (19777)Memory used [KB]: 10618
% 1.45/0.55  % (19777)Time elapsed: 0.140 s
% 1.45/0.55  % (19777)------------------------------
% 1.45/0.55  % (19777)------------------------------
% 1.45/0.55  % (19773)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.56  % (19789)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.45/0.56  fof(f16,plain,(
% 1.45/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.45/0.56    inference(ennf_transformation,[],[f13])).
% 1.45/0.56  fof(f13,plain,(
% 1.45/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.56    inference(rectify,[],[f1])).
% 1.45/0.56  fof(f1,axiom,(
% 1.45/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.45/0.56  fof(f409,plain,(
% 1.45/0.56    r2_hidden(sK6(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0) | (~spl11_1 | spl11_2)),
% 1.45/0.56    inference(forward_demodulation,[],[f403,f64])).
% 1.45/0.56  fof(f64,plain,(
% 1.45/0.56    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl11_1),
% 1.45/0.56    inference(avatar_component_clause,[],[f62])).
% 1.45/0.56  fof(f62,plain,(
% 1.45/0.56    spl11_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.45/0.56  fof(f403,plain,(
% 1.45/0.56    r2_hidden(sK6(sK1,sK2(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0)) | spl11_2),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f23,f322,f321,f332,f33])).
% 1.45/0.56  fof(f33,plain,(
% 1.45/0.56    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f18])).
% 1.45/0.56  fof(f18,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.45/0.56    inference(ennf_transformation,[],[f8])).
% 1.45/0.56  fof(f8,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 1.45/0.56  fof(f332,plain,(
% 1.45/0.56    r2_hidden(k4_tarski(sK6(sK1,sK2(k2_relat_1(sK1),sK0)),sK2(k2_relat_1(sK1),sK0)),sK1) | spl11_2),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f321,f45])).
% 1.45/0.56  fof(f45,plain,(
% 1.45/0.56    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK6(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.45/0.56    inference(equality_resolution,[],[f35])).
% 1.45/0.56  fof(f35,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.45/0.56    inference(cnf_transformation,[],[f7])).
% 1.45/0.56  fof(f7,axiom,(
% 1.45/0.56    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.45/0.56  fof(f321,plain,(
% 1.45/0.56    r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | spl11_2),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f67,f25])).
% 1.45/0.56  fof(f25,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f16])).
% 1.45/0.56  fof(f67,plain,(
% 1.45/0.56    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl11_2),
% 1.45/0.56    inference(avatar_component_clause,[],[f66])).
% 1.45/0.56  fof(f66,plain,(
% 1.45/0.56    spl11_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.45/0.56  fof(f322,plain,(
% 1.45/0.56    r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0) | spl11_2),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f67,f26])).
% 1.45/0.56  fof(f26,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f16])).
% 1.45/0.56  fof(f23,plain,(
% 1.45/0.56    v1_relat_1(sK1)),
% 1.45/0.56    inference(cnf_transformation,[],[f15])).
% 1.45/0.56  fof(f15,plain,(
% 1.45/0.56    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.45/0.56    inference(ennf_transformation,[],[f12])).
% 1.45/0.56  fof(f12,negated_conjecture,(
% 1.45/0.56    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.45/0.56    inference(negated_conjecture,[],[f11])).
% 1.45/0.56  fof(f11,conjecture,(
% 1.45/0.56    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.45/0.56  fof(f29,plain,(
% 1.45/0.56    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f3])).
% 1.45/0.56  fof(f3,axiom,(
% 1.45/0.56    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.45/0.56  fof(f319,plain,(
% 1.45/0.56    spl11_1 | ~spl11_2),
% 1.45/0.56    inference(avatar_contradiction_clause,[],[f316])).
% 1.45/0.56  fof(f316,plain,(
% 1.45/0.56    $false | (spl11_1 | ~spl11_2)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f29,f304,f304,f24])).
% 1.45/0.56  fof(f304,plain,(
% 1.45/0.56    r2_hidden(sK5(k10_relat_1(sK1,sK0),k1_xboole_0),k1_xboole_0) | (spl11_1 | ~spl11_2)),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f63,f101])).
% 1.45/0.56  fof(f101,plain,(
% 1.45/0.56    ( ! [X0] : (r2_hidden(sK5(k10_relat_1(sK1,sK0),X0),X0) | k10_relat_1(sK1,sK0) = X0) ) | ~spl11_2),
% 1.45/0.56    inference(forward_demodulation,[],[f100,f92])).
% 1.45/0.56  fof(f92,plain,(
% 1.45/0.56    k10_relat_1(sK1,sK0) = k2_relat_1(k10_relat_1(sK1,sK0)) | ~spl11_2),
% 1.45/0.56    inference(forward_demodulation,[],[f79,f88])).
% 1.45/0.56  fof(f88,plain,(
% 1.45/0.56    k10_relat_1(sK1,sK0) = k3_xboole_0(k2_relat_1(sK1),sK0) | ~spl11_2),
% 1.45/0.56    inference(forward_demodulation,[],[f82,f50])).
% 1.45/0.56  fof(f50,plain,(
% 1.45/0.56    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))) )),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f23,f38])).
% 1.45/0.56  fof(f38,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f19])).
% 1.45/0.56  fof(f19,plain,(
% 1.45/0.56    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.45/0.56    inference(ennf_transformation,[],[f9])).
% 1.45/0.56  fof(f9,axiom,(
% 1.45/0.56    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.45/0.56  fof(f82,plain,(
% 1.45/0.56    k3_xboole_0(k2_relat_1(sK1),sK0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),sK0)) | ~spl11_2),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f23,f70,f70,f41])).
% 1.45/0.56  fof(f41,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | r2_hidden(sK10(X0,X1,X2),X1) | r2_hidden(sK8(X0,X1,X2),X2) | k10_relat_1(X0,X1) = X2) )),
% 1.45/0.56    inference(cnf_transformation,[],[f20])).
% 1.45/0.56  fof(f20,plain,(
% 1.45/0.56    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.45/0.56    inference(ennf_transformation,[],[f6])).
% 1.45/0.56  fof(f6,axiom,(
% 1.45/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 1.45/0.56  fof(f70,plain,(
% 1.45/0.56    ( ! [X0] : (~r2_hidden(X0,k3_xboole_0(k2_relat_1(sK1),sK0))) ) | ~spl11_2),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f68,f27])).
% 1.45/0.56  fof(f27,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f17])).
% 1.45/0.56  fof(f17,plain,(
% 1.45/0.56    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.45/0.56    inference(ennf_transformation,[],[f14])).
% 1.45/0.56  fof(f14,plain,(
% 1.45/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.56    inference(rectify,[],[f2])).
% 1.45/0.56  fof(f2,axiom,(
% 1.45/0.56    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.45/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.45/0.56  fof(f68,plain,(
% 1.45/0.56    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl11_2),
% 1.45/0.56    inference(avatar_component_clause,[],[f66])).
% 1.45/0.56  fof(f79,plain,(
% 1.45/0.56    k3_xboole_0(k2_relat_1(sK1),sK0) = k2_relat_1(k3_xboole_0(k2_relat_1(sK1),sK0)) | ~spl11_2),
% 1.45/0.56    inference(unit_resulting_resolution,[],[f70,f70,f36])).
% 1.45/0.56  fof(f36,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.45/0.56    inference(cnf_transformation,[],[f7])).
% 1.45/0.56  fof(f100,plain,(
% 1.45/0.56    ( ! [X0] : (k2_relat_1(k10_relat_1(sK1,sK0)) = X0 | r2_hidden(sK5(k10_relat_1(sK1,sK0),X0),X0)) ) | ~spl11_2),
% 1.45/0.56    inference(forward_demodulation,[],[f99,f88])).
% 1.45/0.56  fof(f99,plain,(
% 1.45/0.56    ( ! [X0] : (r2_hidden(sK5(k10_relat_1(sK1,sK0),X0),X0) | k2_relat_1(k3_xboole_0(k2_relat_1(sK1),sK0)) = X0) ) | ~spl11_2),
% 1.45/0.56    inference(forward_demodulation,[],[f83,f88])).
% 1.45/0.56  fof(f83,plain,(
% 1.45/0.56    ( ! [X0] : (r2_hidden(sK5(k3_xboole_0(k2_relat_1(sK1),sK0),X0),X0) | k2_relat_1(k3_xboole_0(k2_relat_1(sK1),sK0)) = X0) ) | ~spl11_2),
% 1.45/0.56    inference(resolution,[],[f70,f36])).
% 1.45/0.56  fof(f63,plain,(
% 1.45/0.56    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl11_1),
% 1.45/0.56    inference(avatar_component_clause,[],[f62])).
% 1.45/0.56  fof(f130,plain,(
% 1.45/0.56    ~spl11_1 | ~spl11_2),
% 1.45/0.56    inference(avatar_split_clause,[],[f22,f66,f62])).
% 1.45/0.56  fof(f22,plain,(
% 1.45/0.56    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f15])).
% 1.45/0.56  fof(f69,plain,(
% 1.45/0.56    spl11_1 | spl11_2),
% 1.45/0.56    inference(avatar_split_clause,[],[f21,f66,f62])).
% 1.45/0.56  fof(f21,plain,(
% 1.45/0.56    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.45/0.56    inference(cnf_transformation,[],[f15])).
% 1.45/0.56  % SZS output end Proof for theBenchmark
% 1.45/0.56  % (19764)------------------------------
% 1.45/0.56  % (19764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (19764)Termination reason: Refutation
% 1.45/0.56  
% 1.45/0.56  % (19764)Memory used [KB]: 6524
% 1.45/0.56  % (19764)Time elapsed: 0.134 s
% 1.45/0.56  % (19764)------------------------------
% 1.45/0.56  % (19764)------------------------------
% 1.61/0.56  % (19759)Success in time 0.2 s
%------------------------------------------------------------------------------
