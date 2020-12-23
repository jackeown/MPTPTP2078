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
% DateTime   : Thu Dec  3 12:55:27 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.44s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 236 expanded)
%              Number of leaves         :   20 (  71 expanded)
%              Depth                    :   10
%              Number of atoms          :  219 ( 568 expanded)
%              Number of equality atoms :   21 (  67 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f736,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f130,f582,f601,f605,f646,f713])).

fof(f713,plain,
    ( ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_contradiction_clause,[],[f700])).

fof(f700,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(unit_resulting_resolution,[],[f62,f54,f667,f53])).

fof(f53,plain,(
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

fof(f667,plain,
    ( r1_tarski(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(backward_demodulation,[],[f586,f596])).

fof(f596,plain,
    ( sK0 = sK1
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f594])).

fof(f594,plain,
    ( spl2_4
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f586,plain,
    ( r1_tarski(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK1)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f37,f81,f118,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f118,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl2_2
  <=> r1_ordinal1(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

% (21563)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
fof(f81,plain,(
    v3_ordinal1(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f38,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k2_xboole_0(X0,k1_enumset1(X0,X0,X0))) ) ),
    inference(definition_unfolding,[],[f42,f58])).

fof(f58,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_enumset1(X0,X0,X0)) ),
    inference(definition_unfolding,[],[f43,f57])).

fof(f57,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f55,f56])).

fof(f56,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f55,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f42,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f38,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_hidden(X0,X1)
          <~> r1_ordinal1(k1_ordinal1(X0),X1) )
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X0,X1)
            <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
          <=> r1_ordinal1(k1_ordinal1(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).

fof(f37,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f62,plain,(
    ! [X0] : k2_xboole_0(X0,k1_enumset1(X0,X0,X0)) != X0 ),
    inference(definition_unfolding,[],[f44,f58])).

fof(f44,plain,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_ordinal1(X0) != X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).

fof(f646,plain,
    ( ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f643])).

fof(f643,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f37,f81,f118,f610,f40])).

fof(f610,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),sK1)
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f607,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f607,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f600,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f600,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f598])).

fof(f598,plain,
    ( spl2_5
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f605,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f602])).

fof(f602,plain,
    ( $false
    | spl2_3 ),
    inference(unit_resulting_resolution,[],[f38,f592])).

fof(f592,plain,
    ( ~ v3_ordinal1(sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f590])).

fof(f590,plain,
    ( spl2_3
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f601,plain,
    ( ~ spl2_3
    | spl2_4
    | spl2_5
    | spl2_1 ),
    inference(avatar_split_clause,[],[f584,f113,f598,f594,f590])).

fof(f113,plain,
    ( spl2_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f584,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 = sK1
    | ~ v3_ordinal1(sK0)
    | spl2_1 ),
    inference(resolution,[],[f115,f72])).

fof(f72,plain,(
    ! [X0] :
      ( r2_hidden(X0,sK1)
      | r2_hidden(sK1,X0)
      | sK1 = X0
      | ~ v3_ordinal1(X0) ) ),
    inference(resolution,[],[f37,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f115,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f582,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f147,f131,f160,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f160,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK1)
    | spl2_2 ),
    inference(unit_resulting_resolution,[],[f37,f81,f119,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r1_tarski(X0,X1)
      | r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f119,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f131,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f114,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_enumset1(X0,X0,X0),X1) ) ),
    inference(definition_unfolding,[],[f46,f57])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f114,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f113])).

fof(f147,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f38,f37,f143,f40])).

fof(f143,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f38,f37,f137,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f137,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f38,f132,f76])).

fof(f76,plain,(
    ! [X3] :
      ( r1_tarski(sK1,X3)
      | ~ v3_ordinal1(X3)
      | ~ r1_ordinal1(sK1,X3) ) ),
    inference(resolution,[],[f37,f40])).

fof(f132,plain,
    ( ~ r1_tarski(sK1,sK0)
    | ~ spl2_1 ),
    inference(unit_resulting_resolution,[],[f114,f45])).

fof(f130,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f60,f117,f113])).

fof(f60,plain,
    ( r1_ordinal1(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f35,f58])).

fof(f35,plain,
    ( r1_ordinal1(k1_ordinal1(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f120,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f59,f117,f113])).

fof(f59,plain,
    ( ~ r1_ordinal1(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(definition_unfolding,[],[f36,f58])).

fof(f36,plain,
    ( ~ r1_ordinal1(k1_ordinal1(sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:10:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (21534)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (21541)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.22/0.52  % (21535)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.22/0.52  % (21549)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.22/0.53  % (21536)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.22/0.53  % (21542)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.22/0.53  % (21558)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.22/0.53  % (21537)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.22/0.53  % (21546)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.22/0.53  % (21545)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.22/0.53  % (21539)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.22/0.54  % (21538)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.22/0.54  % (21556)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.22/0.54  % (21559)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.22/0.54  % (21551)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.22/0.54  % (21560)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.22/0.54  % (21554)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.44/0.54  % (21543)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.44/0.55  % (21561)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.44/0.55  % (21544)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.44/0.55  % (21540)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.44/0.55  % (21552)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.44/0.55  % (21555)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.44/0.55  % (21544)Refutation not found, incomplete strategy% (21544)------------------------------
% 1.44/0.55  % (21544)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.55  % (21544)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.55  
% 1.44/0.55  % (21544)Memory used [KB]: 10746
% 1.44/0.55  % (21544)Time elapsed: 0.139 s
% 1.44/0.55  % (21544)------------------------------
% 1.44/0.55  % (21544)------------------------------
% 1.44/0.55  % (21557)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.44/0.55  % (21547)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.44/0.56  % (21559)Refutation found. Thanks to Tanya!
% 1.44/0.56  % SZS status Theorem for theBenchmark
% 1.44/0.56  % (21550)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.44/0.56  % (21550)Refutation not found, incomplete strategy% (21550)------------------------------
% 1.44/0.56  % (21550)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (21550)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.56  
% 1.44/0.56  % (21550)Memory used [KB]: 10618
% 1.44/0.56  % (21550)Time elapsed: 0.147 s
% 1.44/0.56  % (21550)------------------------------
% 1.44/0.56  % (21550)------------------------------
% 1.44/0.56  % (21548)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.44/0.56  % (21553)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.44/0.56  % SZS output start Proof for theBenchmark
% 1.44/0.56  fof(f736,plain,(
% 1.44/0.56    $false),
% 1.44/0.56    inference(avatar_sat_refutation,[],[f120,f130,f582,f601,f605,f646,f713])).
% 1.44/0.56  fof(f713,plain,(
% 1.44/0.56    ~spl2_2 | ~spl2_4),
% 1.44/0.56    inference(avatar_contradiction_clause,[],[f700])).
% 1.44/0.56  fof(f700,plain,(
% 1.44/0.56    $false | (~spl2_2 | ~spl2_4)),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f62,f54,f667,f53])).
% 1.44/0.56  fof(f53,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.44/0.56    inference(cnf_transformation,[],[f1])).
% 1.44/0.56  fof(f1,axiom,(
% 1.44/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.44/0.56  fof(f667,plain,(
% 1.44/0.56    r1_tarski(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK0) | (~spl2_2 | ~spl2_4)),
% 1.44/0.56    inference(backward_demodulation,[],[f586,f596])).
% 1.44/0.56  fof(f596,plain,(
% 1.44/0.56    sK0 = sK1 | ~spl2_4),
% 1.44/0.56    inference(avatar_component_clause,[],[f594])).
% 1.44/0.56  fof(f594,plain,(
% 1.44/0.56    spl2_4 <=> sK0 = sK1),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 1.44/0.56  fof(f586,plain,(
% 1.44/0.56    r1_tarski(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK1) | ~spl2_2),
% 1.44/0.56    inference(unit_resulting_resolution,[],[f37,f81,f118,f40])).
% 1.44/0.56  fof(f40,plain,(
% 1.44/0.56    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 1.44/0.56    inference(cnf_transformation,[],[f25])).
% 1.44/0.56  fof(f25,plain,(
% 1.44/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.44/0.56    inference(flattening,[],[f24])).
% 1.44/0.56  fof(f24,plain,(
% 1.44/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.44/0.56    inference(ennf_transformation,[],[f16])).
% 1.44/0.56  fof(f16,axiom,(
% 1.44/0.56    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.44/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.44/0.56  fof(f118,plain,(
% 1.44/0.56    r1_ordinal1(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK1) | ~spl2_2),
% 1.44/0.56    inference(avatar_component_clause,[],[f117])).
% 1.44/0.56  fof(f117,plain,(
% 1.44/0.56    spl2_2 <=> r1_ordinal1(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK1)),
% 1.44/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.44/0.57  % (21563)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.44/0.57  fof(f81,plain,(
% 1.44/0.57    v3_ordinal1(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)))),
% 1.44/0.57    inference(unit_resulting_resolution,[],[f38,f61])).
% 1.44/0.57  fof(f61,plain,(
% 1.44/0.57    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(k2_xboole_0(X0,k1_enumset1(X0,X0,X0)))) )),
% 1.44/0.57    inference(definition_unfolding,[],[f42,f58])).
% 1.44/0.57  fof(f58,plain,(
% 1.44/0.57    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_enumset1(X0,X0,X0))) )),
% 1.44/0.57    inference(definition_unfolding,[],[f43,f57])).
% 1.44/0.57  fof(f57,plain,(
% 1.44/0.57    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.44/0.57    inference(definition_unfolding,[],[f55,f56])).
% 1.44/0.57  fof(f56,plain,(
% 1.44/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f6])).
% 1.44/0.57  fof(f6,axiom,(
% 1.44/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.44/0.57  fof(f55,plain,(
% 1.44/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f5])).
% 1.44/0.57  fof(f5,axiom,(
% 1.44/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.44/0.57  fof(f43,plain,(
% 1.44/0.57    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f15])).
% 1.44/0.57  fof(f15,axiom,(
% 1.44/0.57    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.44/0.57  fof(f42,plain,(
% 1.44/0.57    ( ! [X0] : (~v3_ordinal1(X0) | v3_ordinal1(k1_ordinal1(X0))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f28])).
% 1.44/0.57  fof(f28,plain,(
% 1.44/0.57    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.44/0.57    inference(ennf_transformation,[],[f19])).
% 1.44/0.57  fof(f19,axiom,(
% 1.44/0.57    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_ordinal1)).
% 1.44/0.57  fof(f38,plain,(
% 1.44/0.57    v3_ordinal1(sK0)),
% 1.44/0.57    inference(cnf_transformation,[],[f23])).
% 1.44/0.57  fof(f23,plain,(
% 1.44/0.57    ? [X0] : (? [X1] : ((r2_hidden(X0,X1) <~> r1_ordinal1(k1_ordinal1(X0),X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.44/0.57    inference(ennf_transformation,[],[f22])).
% 1.44/0.57  fof(f22,negated_conjecture,(
% 1.44/0.57    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.44/0.57    inference(negated_conjecture,[],[f21])).
% 1.44/0.57  fof(f21,conjecture,(
% 1.44/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) <=> r1_ordinal1(k1_ordinal1(X0),X1))))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_ordinal1)).
% 1.44/0.57  fof(f37,plain,(
% 1.44/0.57    v3_ordinal1(sK1)),
% 1.44/0.57    inference(cnf_transformation,[],[f23])).
% 1.44/0.57  fof(f54,plain,(
% 1.44/0.57    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.44/0.57    inference(cnf_transformation,[],[f3])).
% 1.44/0.57  fof(f3,axiom,(
% 1.44/0.57    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.44/0.57  fof(f62,plain,(
% 1.44/0.57    ( ! [X0] : (k2_xboole_0(X0,k1_enumset1(X0,X0,X0)) != X0) )),
% 1.44/0.57    inference(definition_unfolding,[],[f44,f58])).
% 1.44/0.57  fof(f44,plain,(
% 1.44/0.57    ( ! [X0] : (k1_ordinal1(X0) != X0) )),
% 1.44/0.57    inference(cnf_transformation,[],[f17])).
% 1.44/0.57  fof(f17,axiom,(
% 1.44/0.57    ! [X0] : k1_ordinal1(X0) != X0),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_ordinal1)).
% 1.44/0.57  fof(f646,plain,(
% 1.44/0.57    ~spl2_2 | ~spl2_5),
% 1.44/0.57    inference(avatar_contradiction_clause,[],[f643])).
% 1.44/0.57  fof(f643,plain,(
% 1.44/0.57    $false | (~spl2_2 | ~spl2_5)),
% 1.44/0.57    inference(unit_resulting_resolution,[],[f37,f81,f118,f610,f40])).
% 1.44/0.57  fof(f610,plain,(
% 1.44/0.57    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),sK1)) ) | ~spl2_5),
% 1.44/0.57    inference(unit_resulting_resolution,[],[f607,f50])).
% 1.44/0.57  fof(f50,plain,(
% 1.44/0.57    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f34])).
% 1.44/0.57  fof(f34,plain,(
% 1.44/0.57    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.44/0.57    inference(ennf_transformation,[],[f2])).
% 1.44/0.57  fof(f2,axiom,(
% 1.44/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.44/0.57  fof(f607,plain,(
% 1.44/0.57    ~r1_tarski(sK0,sK1) | ~spl2_5),
% 1.44/0.57    inference(unit_resulting_resolution,[],[f600,f45])).
% 1.44/0.57  fof(f45,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f29])).
% 1.44/0.57  fof(f29,plain,(
% 1.44/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.44/0.57    inference(ennf_transformation,[],[f20])).
% 1.44/0.57  fof(f20,axiom,(
% 1.44/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.44/0.57  fof(f600,plain,(
% 1.44/0.57    r2_hidden(sK1,sK0) | ~spl2_5),
% 1.44/0.57    inference(avatar_component_clause,[],[f598])).
% 1.44/0.57  fof(f598,plain,(
% 1.44/0.57    spl2_5 <=> r2_hidden(sK1,sK0)),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.44/0.57  fof(f605,plain,(
% 1.44/0.57    spl2_3),
% 1.44/0.57    inference(avatar_contradiction_clause,[],[f602])).
% 1.44/0.57  fof(f602,plain,(
% 1.44/0.57    $false | spl2_3),
% 1.44/0.57    inference(unit_resulting_resolution,[],[f38,f592])).
% 1.44/0.57  fof(f592,plain,(
% 1.44/0.57    ~v3_ordinal1(sK0) | spl2_3),
% 1.44/0.57    inference(avatar_component_clause,[],[f590])).
% 1.44/0.57  fof(f590,plain,(
% 1.44/0.57    spl2_3 <=> v3_ordinal1(sK0)),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.44/0.57  fof(f601,plain,(
% 1.44/0.57    ~spl2_3 | spl2_4 | spl2_5 | spl2_1),
% 1.44/0.57    inference(avatar_split_clause,[],[f584,f113,f598,f594,f590])).
% 1.44/0.57  fof(f113,plain,(
% 1.44/0.57    spl2_1 <=> r2_hidden(sK0,sK1)),
% 1.44/0.57    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.44/0.57  fof(f584,plain,(
% 1.44/0.57    r2_hidden(sK1,sK0) | sK0 = sK1 | ~v3_ordinal1(sK0) | spl2_1),
% 1.44/0.57    inference(resolution,[],[f115,f72])).
% 1.44/0.57  fof(f72,plain,(
% 1.44/0.57    ( ! [X0] : (r2_hidden(X0,sK1) | r2_hidden(sK1,X0) | sK1 = X0 | ~v3_ordinal1(X0)) )),
% 1.44/0.57    inference(resolution,[],[f37,f48])).
% 1.44/0.57  fof(f48,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f31])).
% 1.44/0.57  fof(f31,plain,(
% 1.44/0.57    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.44/0.57    inference(flattening,[],[f30])).
% 1.44/0.57  fof(f30,plain,(
% 1.44/0.57    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.44/0.57    inference(ennf_transformation,[],[f18])).
% 1.44/0.57  fof(f18,axiom,(
% 1.44/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 1.44/0.57  fof(f115,plain,(
% 1.44/0.57    ~r2_hidden(sK0,sK1) | spl2_1),
% 1.44/0.57    inference(avatar_component_clause,[],[f113])).
% 1.44/0.57  fof(f582,plain,(
% 1.44/0.57    ~spl2_1 | spl2_2),
% 1.44/0.57    inference(avatar_contradiction_clause,[],[f580])).
% 1.44/0.57  fof(f580,plain,(
% 1.44/0.57    $false | (~spl2_1 | spl2_2)),
% 1.44/0.57    inference(unit_resulting_resolution,[],[f147,f131,f160,f49])).
% 1.44/0.57  fof(f49,plain,(
% 1.44/0.57    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f33])).
% 1.44/0.57  fof(f33,plain,(
% 1.44/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.44/0.57    inference(flattening,[],[f32])).
% 1.44/0.57  fof(f32,plain,(
% 1.44/0.57    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.44/0.57    inference(ennf_transformation,[],[f4])).
% 1.44/0.57  fof(f4,axiom,(
% 1.44/0.57    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.44/0.57  fof(f160,plain,(
% 1.44/0.57    ~r1_tarski(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK1) | spl2_2),
% 1.44/0.57    inference(unit_resulting_resolution,[],[f37,f81,f119,f39])).
% 1.44/0.57  fof(f39,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | ~r1_tarski(X0,X1) | r1_ordinal1(X0,X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f25])).
% 1.44/0.57  fof(f119,plain,(
% 1.44/0.57    ~r1_ordinal1(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK1) | spl2_2),
% 1.44/0.57    inference(avatar_component_clause,[],[f117])).
% 1.44/0.57  fof(f131,plain,(
% 1.44/0.57    r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | ~spl2_1),
% 1.44/0.57    inference(unit_resulting_resolution,[],[f114,f64])).
% 1.44/0.57  fof(f64,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_enumset1(X0,X0,X0),X1)) )),
% 1.44/0.57    inference(definition_unfolding,[],[f46,f57])).
% 1.44/0.57  fof(f46,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f12])).
% 1.44/0.57  fof(f12,axiom,(
% 1.44/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 1.44/0.57  fof(f114,plain,(
% 1.44/0.57    r2_hidden(sK0,sK1) | ~spl2_1),
% 1.44/0.57    inference(avatar_component_clause,[],[f113])).
% 1.44/0.57  fof(f147,plain,(
% 1.44/0.57    r1_tarski(sK0,sK1) | ~spl2_1),
% 1.44/0.57    inference(unit_resulting_resolution,[],[f38,f37,f143,f40])).
% 1.44/0.57  fof(f143,plain,(
% 1.44/0.57    r1_ordinal1(sK0,sK1) | ~spl2_1),
% 1.44/0.57    inference(unit_resulting_resolution,[],[f38,f37,f137,f41])).
% 1.44/0.57  fof(f41,plain,(
% 1.44/0.57    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r1_ordinal1(X1,X0)) )),
% 1.44/0.57    inference(cnf_transformation,[],[f27])).
% 1.44/0.57  fof(f27,plain,(
% 1.44/0.57    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.44/0.57    inference(flattening,[],[f26])).
% 1.44/0.57  fof(f26,plain,(
% 1.44/0.57    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.44/0.57    inference(ennf_transformation,[],[f14])).
% 1.44/0.57  fof(f14,axiom,(
% 1.44/0.57    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 1.44/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 1.44/0.57  fof(f137,plain,(
% 1.44/0.57    ~r1_ordinal1(sK1,sK0) | ~spl2_1),
% 1.44/0.57    inference(unit_resulting_resolution,[],[f38,f132,f76])).
% 1.44/0.57  fof(f76,plain,(
% 1.44/0.57    ( ! [X3] : (r1_tarski(sK1,X3) | ~v3_ordinal1(X3) | ~r1_ordinal1(sK1,X3)) )),
% 1.44/0.57    inference(resolution,[],[f37,f40])).
% 1.44/0.57  fof(f132,plain,(
% 1.44/0.57    ~r1_tarski(sK1,sK0) | ~spl2_1),
% 1.44/0.57    inference(unit_resulting_resolution,[],[f114,f45])).
% 1.44/0.57  fof(f130,plain,(
% 1.44/0.57    spl2_1 | spl2_2),
% 1.44/0.57    inference(avatar_split_clause,[],[f60,f117,f113])).
% 1.44/0.57  fof(f60,plain,(
% 1.44/0.57    r1_ordinal1(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK1) | r2_hidden(sK0,sK1)),
% 1.44/0.57    inference(definition_unfolding,[],[f35,f58])).
% 1.44/0.57  fof(f35,plain,(
% 1.44/0.57    r1_ordinal1(k1_ordinal1(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.44/0.57    inference(cnf_transformation,[],[f23])).
% 1.44/0.57  fof(f120,plain,(
% 1.44/0.57    ~spl2_1 | ~spl2_2),
% 1.44/0.57    inference(avatar_split_clause,[],[f59,f117,f113])).
% 1.44/0.57  fof(f59,plain,(
% 1.44/0.57    ~r1_ordinal1(k2_xboole_0(sK0,k1_enumset1(sK0,sK0,sK0)),sK1) | ~r2_hidden(sK0,sK1)),
% 1.44/0.57    inference(definition_unfolding,[],[f36,f58])).
% 1.44/0.57  fof(f36,plain,(
% 1.44/0.57    ~r1_ordinal1(k1_ordinal1(sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 1.44/0.57    inference(cnf_transformation,[],[f23])).
% 1.44/0.57  % SZS output end Proof for theBenchmark
% 1.44/0.57  % (21559)------------------------------
% 1.44/0.57  % (21559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.57  % (21559)Termination reason: Refutation
% 1.44/0.57  
% 1.44/0.57  % (21559)Memory used [KB]: 6524
% 1.44/0.57  % (21559)Time elapsed: 0.144 s
% 1.44/0.57  % (21559)------------------------------
% 1.44/0.57  % (21559)------------------------------
% 1.44/0.57  % (21533)Success in time 0.205 s
%------------------------------------------------------------------------------
