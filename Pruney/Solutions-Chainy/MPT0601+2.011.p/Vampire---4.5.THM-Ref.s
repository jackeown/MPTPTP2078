%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:08 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 113 expanded)
%              Number of leaves         :   16 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :  162 ( 264 expanded)
%              Number of equality atoms :   47 (  76 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f263,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f72,f100,f234,f245,f262])).

fof(f262,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f47,f252])).

fof(f252,plain,
    ( ! [X0] : k1_xboole_0 != k2_xboole_0(k1_xboole_0,X0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(superposition,[],[f51,f247])).

fof(f247,plain,
    ( k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | ~ spl10_1
    | ~ spl10_2
    | ~ spl10_6 ),
    inference(unit_resulting_resolution,[],[f69,f103,f233])).

fof(f233,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k11_relat_1(sK1,X0)
        | ~ r1_tarski(k1_enumset1(X0,X0,X0),k1_relat_1(sK1))
        | k1_xboole_0 = k1_enumset1(X0,X0,X0) )
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f232])).

fof(f232,plain,
    ( spl10_6
  <=> ! [X0] :
        ( k1_xboole_0 != k11_relat_1(sK1,X0)
        | ~ r1_tarski(k1_enumset1(X0,X0,X0),k1_relat_1(sK1))
        | k1_xboole_0 = k1_enumset1(X0,X0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f103,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_relat_1(sK1))
    | ~ spl10_1 ),
    inference(unit_resulting_resolution,[],[f66,f66,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f46,f48])).

fof(f48,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X2)
      | r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f66,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl10_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f69,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl10_2
  <=> k1_xboole_0 = k11_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f51,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1) ),
    inference(definition_unfolding,[],[f42,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f48])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f245,plain,(
    spl10_5 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl10_5 ),
    inference(unit_resulting_resolution,[],[f29,f230])).

fof(f230,plain,
    ( ~ v1_relat_1(sK1)
    | spl10_5 ),
    inference(avatar_component_clause,[],[f228])).

fof(f228,plain,
    ( spl10_5
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f29,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f234,plain,
    ( ~ spl10_5
    | spl10_6 ),
    inference(avatar_split_clause,[],[f116,f232,f228])).

fof(f116,plain,(
    ! [X0] :
      ( k1_xboole_0 != k11_relat_1(sK1,X0)
      | k1_xboole_0 = k1_enumset1(X0,X0,X0)
      | ~ r1_tarski(k1_enumset1(X0,X0,X0),k1_relat_1(sK1))
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f41,f57])).

fof(f57,plain,(
    ! [X0] : k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_enumset1(X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f29,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f32,f49])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k9_relat_1(X1,X0)
          & r1_tarski(X0,k1_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

fof(f100,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl10_1
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f77,f85,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f85,plain,
    ( ~ v1_relat_1(k11_relat_1(sK1,sK0))
    | spl10_1
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f70,f77,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ! [X1,X2] : ~ r2_hidden(k4_tarski(X1,X2),X0)
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

fof(f70,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f77,plain,
    ( ! [X0] : ~ r2_hidden(X0,k11_relat_1(sK1,sK0))
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f29,f73,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f73,plain,
    ( ! [X0] : ~ r2_hidden(k4_tarski(sK0,X0),sK1)
    | spl10_1 ),
    inference(unit_resulting_resolution,[],[f65,f56])).

fof(f56,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k1_relat_1(X0))
      | ~ r2_hidden(k4_tarski(X2,X3),X0) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f65,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f72,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f28,f68,f64])).

fof(f28,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f71,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f27,f68,f64])).

fof(f27,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (18796)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.50  % (18779)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (18779)Refutation not found, incomplete strategy% (18779)------------------------------
% 0.20/0.51  % (18779)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (18779)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (18779)Memory used [KB]: 10746
% 0.20/0.51  % (18779)Time elapsed: 0.100 s
% 0.20/0.51  % (18779)------------------------------
% 0.20/0.51  % (18779)------------------------------
% 0.20/0.51  % (18777)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.51  % (18787)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (18793)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (18783)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (18790)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (18792)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.52  % (18784)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.52  % (18787)Refutation not found, incomplete strategy% (18787)------------------------------
% 0.20/0.52  % (18787)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (18787)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (18787)Memory used [KB]: 10746
% 0.20/0.52  % (18787)Time elapsed: 0.115 s
% 0.20/0.52  % (18787)------------------------------
% 0.20/0.52  % (18787)------------------------------
% 0.20/0.52  % (18802)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.52  % (18798)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (18781)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (18780)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (18786)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.53  % (18801)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.35/0.53  % (18789)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.53  % (18778)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.35/0.53  % (18781)Refutation found. Thanks to Tanya!
% 1.35/0.53  % SZS status Theorem for theBenchmark
% 1.35/0.53  % (18788)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.54  % (18805)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.35/0.54  % (18782)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.35/0.54  % (18804)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.35/0.54  % (18797)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.54  % (18785)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.54  % (18785)Refutation not found, incomplete strategy% (18785)------------------------------
% 1.35/0.54  % (18785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (18785)Termination reason: Refutation not found, incomplete strategy
% 1.35/0.54  
% 1.35/0.54  % (18785)Memory used [KB]: 10746
% 1.35/0.54  % (18785)Time elapsed: 0.125 s
% 1.35/0.54  % (18785)------------------------------
% 1.35/0.54  % (18785)------------------------------
% 1.35/0.54  % SZS output start Proof for theBenchmark
% 1.35/0.54  fof(f263,plain,(
% 1.35/0.54    $false),
% 1.35/0.54    inference(avatar_sat_refutation,[],[f71,f72,f100,f234,f245,f262])).
% 1.35/0.54  fof(f262,plain,(
% 1.35/0.54    ~spl10_1 | ~spl10_2 | ~spl10_6),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f258])).
% 1.35/0.54  fof(f258,plain,(
% 1.35/0.54    $false | (~spl10_1 | ~spl10_2 | ~spl10_6)),
% 1.35/0.54    inference(unit_resulting_resolution,[],[f47,f252])).
% 1.35/0.54  fof(f252,plain,(
% 1.35/0.54    ( ! [X0] : (k1_xboole_0 != k2_xboole_0(k1_xboole_0,X0)) ) | (~spl10_1 | ~spl10_2 | ~spl10_6)),
% 1.35/0.54    inference(superposition,[],[f51,f247])).
% 1.35/0.54  fof(f247,plain,(
% 1.35/0.54    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | (~spl10_1 | ~spl10_2 | ~spl10_6)),
% 1.35/0.54    inference(unit_resulting_resolution,[],[f69,f103,f233])).
% 1.35/0.54  fof(f233,plain,(
% 1.35/0.54    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | ~r1_tarski(k1_enumset1(X0,X0,X0),k1_relat_1(sK1)) | k1_xboole_0 = k1_enumset1(X0,X0,X0)) ) | ~spl10_6),
% 1.35/0.54    inference(avatar_component_clause,[],[f232])).
% 1.35/0.54  fof(f232,plain,(
% 1.35/0.54    spl10_6 <=> ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | ~r1_tarski(k1_enumset1(X0,X0,X0),k1_relat_1(sK1)) | k1_xboole_0 = k1_enumset1(X0,X0,X0))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.35/0.54  fof(f103,plain,(
% 1.35/0.54    r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_relat_1(sK1)) | ~spl10_1),
% 1.35/0.54    inference(unit_resulting_resolution,[],[f66,f66,f52])).
% 1.35/0.54  fof(f52,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (r1_tarski(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f46,f48])).
% 1.35/0.54  fof(f48,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f3])).
% 1.35/0.54  fof(f3,axiom,(
% 1.35/0.54    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.35/0.54  fof(f46,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X2) | r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f9])).
% 1.35/0.54  fof(f9,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.35/0.54  fof(f66,plain,(
% 1.35/0.54    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl10_1),
% 1.35/0.54    inference(avatar_component_clause,[],[f64])).
% 1.35/0.54  fof(f64,plain,(
% 1.35/0.54    spl10_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.35/0.54  fof(f69,plain,(
% 1.35/0.54    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~spl10_2),
% 1.35/0.54    inference(avatar_component_clause,[],[f68])).
% 1.35/0.54  fof(f68,plain,(
% 1.35/0.54    spl10_2 <=> k1_xboole_0 = k11_relat_1(sK1,sK0)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.35/0.54  fof(f51,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f42,f49])).
% 1.35/0.54  fof(f49,plain,(
% 1.35/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.35/0.54    inference(definition_unfolding,[],[f43,f48])).
% 1.35/0.54  fof(f43,plain,(
% 1.35/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f2])).
% 1.35/0.54  fof(f2,axiom,(
% 1.35/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.35/0.54  fof(f42,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f10])).
% 1.35/0.54  fof(f10,axiom,(
% 1.35/0.54    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.35/0.54  fof(f47,plain,(
% 1.35/0.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.35/0.54    inference(cnf_transformation,[],[f1])).
% 1.35/0.54  fof(f1,axiom,(
% 1.35/0.54    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.35/0.54  fof(f245,plain,(
% 1.35/0.54    spl10_5),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f235])).
% 1.35/0.54  fof(f235,plain,(
% 1.35/0.54    $false | spl10_5),
% 1.35/0.54    inference(unit_resulting_resolution,[],[f29,f230])).
% 1.35/0.54  fof(f230,plain,(
% 1.35/0.54    ~v1_relat_1(sK1) | spl10_5),
% 1.35/0.54    inference(avatar_component_clause,[],[f228])).
% 1.35/0.54  fof(f228,plain,(
% 1.35/0.54    spl10_5 <=> v1_relat_1(sK1)),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 1.35/0.54  fof(f29,plain,(
% 1.35/0.54    v1_relat_1(sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f19])).
% 1.35/0.54  fof(f19,plain,(
% 1.35/0.54    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 1.35/0.54    inference(ennf_transformation,[],[f18])).
% 1.35/0.54  fof(f18,negated_conjecture,(
% 1.35/0.54    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.35/0.54    inference(negated_conjecture,[],[f17])).
% 1.35/0.54  fof(f17,conjecture,(
% 1.35/0.54    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 1.35/0.54  fof(f234,plain,(
% 1.35/0.54    ~spl10_5 | spl10_6),
% 1.35/0.54    inference(avatar_split_clause,[],[f116,f232,f228])).
% 1.35/0.54  fof(f116,plain,(
% 1.35/0.54    ( ! [X0] : (k1_xboole_0 != k11_relat_1(sK1,X0) | k1_xboole_0 = k1_enumset1(X0,X0,X0) | ~r1_tarski(k1_enumset1(X0,X0,X0),k1_relat_1(sK1)) | ~v1_relat_1(sK1)) )),
% 1.35/0.54    inference(superposition,[],[f41,f57])).
% 1.35/0.54  fof(f57,plain,(
% 1.35/0.54    ( ! [X0] : (k11_relat_1(sK1,X0) = k9_relat_1(sK1,k1_enumset1(X0,X0,X0))) )),
% 1.35/0.54    inference(unit_resulting_resolution,[],[f29,f50])).
% 1.35/0.54  fof(f50,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_enumset1(X1,X1,X1))) )),
% 1.35/0.54    inference(definition_unfolding,[],[f32,f49])).
% 1.35/0.54  fof(f32,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~v1_relat_1(X0) | k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f21])).
% 1.35/0.54  fof(f21,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)) | ~v1_relat_1(X0))),
% 1.35/0.54    inference(ennf_transformation,[],[f11])).
% 1.35/0.54  fof(f11,axiom,(
% 1.35/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : k11_relat_1(X0,X1) = k9_relat_1(X0,k1_tarski(X1)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_relat_1)).
% 1.35/0.54  fof(f41,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f26])).
% 1.35/0.54  fof(f26,plain,(
% 1.35/0.54    ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0 | ~v1_relat_1(X1))),
% 1.35/0.54    inference(flattening,[],[f25])).
% 1.35/0.54  fof(f25,plain,(
% 1.35/0.54    ! [X0,X1] : ((k1_xboole_0 != k9_relat_1(X1,X0) | ~r1_tarski(X0,k1_relat_1(X1)) | k1_xboole_0 = X0) | ~v1_relat_1(X1))),
% 1.35/0.54    inference(ennf_transformation,[],[f14])).
% 1.35/0.54  fof(f14,axiom,(
% 1.35/0.54    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k9_relat_1(X1,X0) & r1_tarski(X0,k1_relat_1(X1)) & k1_xboole_0 != X0))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).
% 1.35/0.54  fof(f100,plain,(
% 1.35/0.54    spl10_1 | spl10_2),
% 1.35/0.54    inference(avatar_contradiction_clause,[],[f98])).
% 1.35/0.54  fof(f98,plain,(
% 1.35/0.54    $false | (spl10_1 | spl10_2)),
% 1.35/0.54    inference(unit_resulting_resolution,[],[f77,f85,f39])).
% 1.35/0.54  fof(f39,plain,(
% 1.35/0.54    ( ! [X0] : (r2_hidden(sK7(X0),X0) | v1_relat_1(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f24])).
% 1.35/0.54  fof(f24,plain,(
% 1.35/0.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f12])).
% 1.35/0.54  fof(f12,axiom,(
% 1.35/0.54    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 1.35/0.54  fof(f85,plain,(
% 1.35/0.54    ~v1_relat_1(k11_relat_1(sK1,sK0)) | (spl10_1 | spl10_2)),
% 1.35/0.54    inference(unit_resulting_resolution,[],[f70,f77,f33])).
% 1.35/0.54  fof(f33,plain,(
% 1.35/0.54    ( ! [X0] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0),sK3(X0)),X0) | k1_xboole_0 = X0) )),
% 1.35/0.54    inference(cnf_transformation,[],[f23])).
% 1.35/0.54  fof(f23,plain,(
% 1.35/0.54    ! [X0] : (k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0) | ~v1_relat_1(X0))),
% 1.35/0.54    inference(flattening,[],[f22])).
% 1.35/0.54  fof(f22,plain,(
% 1.35/0.54    ! [X0] : ((k1_xboole_0 = X0 | ? [X1,X2] : r2_hidden(k4_tarski(X1,X2),X0)) | ~v1_relat_1(X0))),
% 1.35/0.54    inference(ennf_transformation,[],[f16])).
% 1.35/0.54  fof(f16,axiom,(
% 1.35/0.54    ! [X0] : (v1_relat_1(X0) => (! [X1,X2] : ~r2_hidden(k4_tarski(X1,X2),X0) => k1_xboole_0 = X0))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).
% 1.35/0.54  fof(f70,plain,(
% 1.35/0.54    k1_xboole_0 != k11_relat_1(sK1,sK0) | spl10_2),
% 1.35/0.54    inference(avatar_component_clause,[],[f68])).
% 1.35/0.54  fof(f77,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(X0,k11_relat_1(sK1,sK0))) ) | spl10_1),
% 1.35/0.54    inference(unit_resulting_resolution,[],[f29,f73,f30])).
% 1.35/0.54  fof(f30,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f20])).
% 1.35/0.54  fof(f20,plain,(
% 1.35/0.54    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 1.35/0.54    inference(ennf_transformation,[],[f15])).
% 1.35/0.54  fof(f15,axiom,(
% 1.35/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 1.35/0.54  fof(f73,plain,(
% 1.35/0.54    ( ! [X0] : (~r2_hidden(k4_tarski(sK0,X0),sK1)) ) | spl10_1),
% 1.35/0.54    inference(unit_resulting_resolution,[],[f65,f56])).
% 1.35/0.54  fof(f56,plain,(
% 1.35/0.54    ( ! [X2,X0,X3] : (r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(k4_tarski(X2,X3),X0)) )),
% 1.35/0.54    inference(equality_resolution,[],[f34])).
% 1.35/0.54  fof(f34,plain,(
% 1.35/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 1.35/0.54    inference(cnf_transformation,[],[f13])).
% 1.35/0.54  fof(f13,axiom,(
% 1.35/0.54    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 1.35/0.54  fof(f65,plain,(
% 1.35/0.54    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl10_1),
% 1.35/0.54    inference(avatar_component_clause,[],[f64])).
% 1.35/0.54  fof(f72,plain,(
% 1.35/0.54    ~spl10_1 | spl10_2),
% 1.35/0.54    inference(avatar_split_clause,[],[f28,f68,f64])).
% 1.35/0.54  fof(f28,plain,(
% 1.35/0.54    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 1.35/0.54    inference(cnf_transformation,[],[f19])).
% 1.35/0.54  fof(f71,plain,(
% 1.35/0.54    spl10_1 | ~spl10_2),
% 1.35/0.54    inference(avatar_split_clause,[],[f27,f68,f64])).
% 1.35/0.54  fof(f27,plain,(
% 1.35/0.54    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 1.35/0.54    inference(cnf_transformation,[],[f19])).
% 1.35/0.54  % SZS output end Proof for theBenchmark
% 1.35/0.54  % (18781)------------------------------
% 1.35/0.54  % (18781)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (18781)Termination reason: Refutation
% 1.35/0.54  
% 1.35/0.54  % (18781)Memory used [KB]: 6396
% 1.35/0.54  % (18781)Time elapsed: 0.117 s
% 1.35/0.54  % (18781)------------------------------
% 1.35/0.54  % (18781)------------------------------
% 1.35/0.54  % (18794)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.55  % (18773)Success in time 0.188 s
%------------------------------------------------------------------------------
