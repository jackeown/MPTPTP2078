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
% DateTime   : Thu Dec  3 12:47:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 134 expanded)
%              Number of leaves         :   14 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :  191 ( 362 expanded)
%              Number of equality atoms :   21 (  40 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (2388)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f86,f116,f162,f344,f372,f375,f379])).

fof(f379,plain,
    ( ~ spl8_2
    | ~ spl8_8
    | spl8_13 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_8
    | spl8_13 ),
    inference(subsumption_resolution,[],[f135,f376])).

fof(f376,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_2
    | spl8_13 ),
    inference(forward_demodulation,[],[f300,f43])).

fof(f43,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl8_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f300,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
    | spl8_13 ),
    inference(unit_resulting_resolution,[],[f289,f35])).

fof(f35,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0)
      | ~ r2_hidden(X2,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).

fof(f289,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | spl8_13 ),
    inference(unit_resulting_resolution,[],[f285,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r2_hidden(sK2(X1),X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ! [X3] :
              ( ~ r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1) )
          & r2_hidden(X2,X1) )
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( ! [X3] :
                  ~ ( r2_hidden(X3,X2)
                    & r2_hidden(X3,X1) )
              & r2_hidden(X2,X1) )
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

fof(f285,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | spl8_13 ),
    inference(avatar_component_clause,[],[f284])).

fof(f284,plain,
    ( spl8_13
  <=> r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f135,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | ~ spl8_8 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl8_8
  <=> r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).

fof(f375,plain,
    ( spl8_6
    | spl8_8
    | ~ spl8_2
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f374,f129,f42,f133,f126])).

fof(f126,plain,
    ( spl8_6
  <=> ! [X6] : ~ r2_hidden(X6,k2_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f129,plain,
    ( spl8_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f374,plain,
    ( ! [X0] :
        ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(X0,k2_relat_1(k1_xboole_0)) )
    | ~ spl8_2
    | ~ spl8_7 ),
    inference(forward_demodulation,[],[f164,f43])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_relat_1(k1_xboole_0))
        | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0)) )
    | ~ spl8_7 ),
    inference(resolution,[],[f130,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | r2_hidden(sK0(X1),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k1_relat_1(X1))
      | ~ r2_hidden(X0,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k1_relat_1(X1))
          & r2_hidden(X0,k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).

fof(f130,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f372,plain,(
    ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f371])).

fof(f371,plain,
    ( $false
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f350,f23])).

fof(f23,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f350,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl8_13 ),
    inference(unit_resulting_resolution,[],[f286,f286,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
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

fof(f286,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f284])).

fof(f344,plain,
    ( spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_13 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | ~ spl8_6
    | spl8_13 ),
    inference(subsumption_resolution,[],[f294,f127])).

fof(f127,plain,
    ( ! [X6] : ~ r2_hidden(X6,k2_relat_1(k1_xboole_0))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f294,plain,
    ( r2_hidden(sK5(k1_xboole_0,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0))
    | spl8_1
    | ~ spl8_2
    | spl8_13 ),
    inference(unit_resulting_resolution,[],[f40,f289,f118])).

fof(f118,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK5(k1_xboole_0,X0),sK7(k1_xboole_0,X0)),k1_xboole_0)
        | k1_xboole_0 = X0
        | r2_hidden(sK5(k1_xboole_0,X0),X0) )
    | ~ spl8_2 ),
    inference(superposition,[],[f43,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK5(X0,X1),sK7(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k1_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f40,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl8_1
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f162,plain,(
    spl8_7 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl8_7 ),
    inference(subsumption_resolution,[],[f142,f23])).

fof(f142,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f137,f137,f28])).

fof(f137,plain,
    ( r2_hidden(sK3(k1_xboole_0),k1_xboole_0)
    | spl8_7 ),
    inference(unit_resulting_resolution,[],[f131,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

% (2378)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f131,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl8_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f116,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f95,f23])).

fof(f95,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl8_3 ),
    inference(unit_resulting_resolution,[],[f51,f51,f28])).

fof(f51,plain,
    ( r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl8_3
  <=> r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f86,plain,
    ( spl8_2
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f85])).

fof(f85,plain,
    ( $false
    | spl8_2
    | spl8_3 ),
    inference(subsumption_resolution,[],[f64,f23])).

fof(f64,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | spl8_2
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f58,f58,f28])).

fof(f58,plain,
    ( r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | spl8_2
    | spl8_3 ),
    inference(subsumption_resolution,[],[f57,f52])).

fof(f52,plain,
    ( ~ r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f57,plain,
    ( r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl8_2 ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | r2_hidden(k4_tarski(sK5(k1_xboole_0,X0),sK7(k1_xboole_0,X0)),k1_xboole_0)
        | r2_hidden(sK5(k1_xboole_0,X0),X0) )
    | spl8_2 ),
    inference(superposition,[],[f44,f33])).

fof(f44,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f45,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f19,f42,f38])).

fof(f19,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

% (2380)Refutation not found, incomplete strategy% (2380)------------------------------
% (2380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f12,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f9])).

% (2380)Termination reason: Refutation not found, incomplete strategy

fof(f9,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f8])).

% (2380)Memory used [KB]: 10746
fof(f8,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

% (2380)Time elapsed: 0.126 s
% (2380)------------------------------
% (2380)------------------------------
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:54:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (2365)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.50  % (2369)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.51  % (2370)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (2362)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (2368)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.52  % (2368)Refutation not found, incomplete strategy% (2368)------------------------------
% 0.20/0.52  % (2368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (2368)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (2368)Memory used [KB]: 10618
% 0.20/0.52  % (2368)Time elapsed: 0.114 s
% 0.20/0.52  % (2368)------------------------------
% 0.20/0.52  % (2368)------------------------------
% 0.20/0.52  % (2373)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (2360)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (2379)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.53  % (2361)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (2370)Refutation not found, incomplete strategy% (2370)------------------------------
% 0.20/0.53  % (2370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2370)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2370)Memory used [KB]: 10618
% 0.20/0.53  % (2370)Time elapsed: 0.109 s
% 0.20/0.53  % (2370)------------------------------
% 0.20/0.53  % (2370)------------------------------
% 0.20/0.53  % (2367)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (2384)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.53  % (2382)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (2360)Refutation not found, incomplete strategy% (2360)------------------------------
% 0.20/0.53  % (2360)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2360)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2360)Memory used [KB]: 1663
% 0.20/0.53  % (2360)Time elapsed: 0.114 s
% 0.20/0.53  % (2360)------------------------------
% 0.20/0.53  % (2360)------------------------------
% 0.20/0.53  % (2363)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (2380)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.53  % (2385)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.53  % (2386)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.53  % (2369)Refutation found. Thanks to Tanya!
% 0.20/0.53  % SZS status Theorem for theBenchmark
% 0.20/0.53  % SZS output start Proof for theBenchmark
% 0.20/0.53  % (2388)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  fof(f380,plain,(
% 0.20/0.53    $false),
% 0.20/0.53    inference(avatar_sat_refutation,[],[f45,f86,f116,f162,f344,f372,f375,f379])).
% 0.20/0.53  fof(f379,plain,(
% 0.20/0.53    ~spl8_2 | ~spl8_8 | spl8_13),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f378])).
% 0.20/0.53  fof(f378,plain,(
% 0.20/0.53    $false | (~spl8_2 | ~spl8_8 | spl8_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f135,f376])).
% 0.20/0.53  fof(f376,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl8_2 | spl8_13)),
% 0.20/0.53    inference(forward_demodulation,[],[f300,f43])).
% 0.20/0.53  fof(f43,plain,(
% 0.20/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl8_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f42])).
% 0.20/0.53  fof(f42,plain,(
% 0.20/0.53    spl8_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.20/0.53  fof(f300,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0))) ) | spl8_13),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f289,f35])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    ( ! [X2,X0] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,k1_relat_1(X0))) )),
% 0.20/0.53    inference(equality_resolution,[],[f32])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,sK6(X0,X2)),X0) | ~r2_hidden(X2,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.53  fof(f289,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | spl8_13),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f285,f25])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r2_hidden(sK2(X1),X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0,X1] : (? [X2] : (! [X3] : (~r2_hidden(X3,X2) | ~r2_hidden(X3,X1)) & r2_hidden(X2,X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0,X1] : ~(! [X2] : ~(! [X3] : ~(r2_hidden(X3,X2) & r2_hidden(X3,X1)) & r2_hidden(X2,X1)) & r2_hidden(X0,X1))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).
% 0.20/0.53  fof(f285,plain,(
% 0.20/0.53    ~r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | spl8_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f284])).
% 0.20/0.53  fof(f284,plain,(
% 0.20/0.53    spl8_13 <=> r2_hidden(sK2(k1_xboole_0),k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    r2_hidden(sK0(k1_xboole_0),k1_xboole_0) | ~spl8_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f133])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    spl8_8 <=> r2_hidden(sK0(k1_xboole_0),k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_8])])).
% 0.20/0.53  fof(f375,plain,(
% 0.20/0.53    spl8_6 | spl8_8 | ~spl8_2 | ~spl8_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f374,f129,f42,f133,f126])).
% 0.20/0.53  fof(f126,plain,(
% 0.20/0.53    spl8_6 <=> ! [X6] : ~r2_hidden(X6,k2_relat_1(k1_xboole_0))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.20/0.53  fof(f129,plain,(
% 0.20/0.53    spl8_7 <=> v1_relat_1(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.20/0.53  fof(f374,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK0(k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k2_relat_1(k1_xboole_0))) ) | (~spl8_2 | ~spl8_7)),
% 0.20/0.53    inference(forward_demodulation,[],[f164,f43])).
% 0.20/0.53  fof(f164,plain,(
% 0.20/0.53    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(k1_xboole_0)) | r2_hidden(sK0(k1_xboole_0),k1_relat_1(k1_xboole_0))) ) | ~spl8_7),
% 0.20/0.53    inference(resolution,[],[f130,f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,k2_relat_1(X1)) | r2_hidden(sK0(X1),k1_relat_1(X1))) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0,X1] : (? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(flattening,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k1_relat_1(X1)) | ~r2_hidden(X0,k2_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.20/0.53    inference(ennf_transformation,[],[f7])).
% 0.20/0.53  fof(f7,axiom,(
% 0.20/0.53    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k1_relat_1(X1)) & r2_hidden(X0,k2_relat_1(X1))))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_relat_1)).
% 0.20/0.53  fof(f130,plain,(
% 0.20/0.53    v1_relat_1(k1_xboole_0) | ~spl8_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f129])).
% 0.20/0.53  fof(f372,plain,(
% 0.20/0.53    ~spl8_13),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f371])).
% 0.20/0.53  fof(f371,plain,(
% 0.20/0.53    $false | ~spl8_13),
% 0.20/0.53    inference(subsumption_resolution,[],[f350,f23])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.53  fof(f350,plain,(
% 0.20/0.53    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl8_13),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f286,f286,f28])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.20/0.53    inference(ennf_transformation,[],[f10])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.53    inference(rectify,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.20/0.53  fof(f286,plain,(
% 0.20/0.53    r2_hidden(sK2(k1_xboole_0),k1_xboole_0) | ~spl8_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f284])).
% 0.20/0.53  fof(f344,plain,(
% 0.20/0.53    spl8_1 | ~spl8_2 | ~spl8_6 | spl8_13),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f343])).
% 0.20/0.53  fof(f343,plain,(
% 0.20/0.53    $false | (spl8_1 | ~spl8_2 | ~spl8_6 | spl8_13)),
% 0.20/0.53    inference(subsumption_resolution,[],[f294,f127])).
% 0.20/0.53  fof(f127,plain,(
% 0.20/0.53    ( ! [X6] : (~r2_hidden(X6,k2_relat_1(k1_xboole_0))) ) | ~spl8_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f126])).
% 0.20/0.53  fof(f294,plain,(
% 0.20/0.53    r2_hidden(sK5(k1_xboole_0,k2_relat_1(k1_xboole_0)),k2_relat_1(k1_xboole_0)) | (spl8_1 | ~spl8_2 | spl8_13)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f40,f289,f118])).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(k4_tarski(sK5(k1_xboole_0,X0),sK7(k1_xboole_0,X0)),k1_xboole_0) | k1_xboole_0 = X0 | r2_hidden(sK5(k1_xboole_0,X0),X0)) ) | ~spl8_2),
% 0.20/0.53    inference(superposition,[],[f43,f33])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK5(X0,X1),sK7(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1) | k1_relat_1(X0) = X1) )),
% 0.20/0.53    inference(cnf_transformation,[],[f6])).
% 0.20/0.53  fof(f40,plain,(
% 0.20/0.53    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl8_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    spl8_1 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.20/0.53  fof(f162,plain,(
% 0.20/0.53    spl8_7),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f161])).
% 0.20/0.53  fof(f161,plain,(
% 0.20/0.53    $false | spl8_7),
% 0.20/0.53    inference(subsumption_resolution,[],[f142,f23])).
% 0.20/0.53  fof(f142,plain,(
% 0.20/0.53    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | spl8_7),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f137,f137,f28])).
% 0.20/0.53  fof(f137,plain,(
% 0.20/0.53    r2_hidden(sK3(k1_xboole_0),k1_xboole_0) | spl8_7),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f131,f26])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_relat_1(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 0.20/0.53    inference(unused_predicate_definition_removal,[],[f5])).
% 0.20/0.53  % (2378)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.20/0.53  fof(f131,plain,(
% 0.20/0.53    ~v1_relat_1(k1_xboole_0) | spl8_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f129])).
% 0.20/0.53  fof(f116,plain,(
% 0.20/0.53    ~spl8_3),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f115])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    $false | ~spl8_3),
% 0.20/0.53    inference(subsumption_resolution,[],[f95,f23])).
% 0.20/0.53  fof(f95,plain,(
% 0.20/0.53    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl8_3),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f51,f51,f28])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl8_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f50])).
% 0.20/0.53  fof(f50,plain,(
% 0.20/0.53    spl8_3 <=> r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    spl8_2 | spl8_3),
% 0.20/0.53    inference(avatar_contradiction_clause,[],[f85])).
% 0.20/0.53  fof(f85,plain,(
% 0.20/0.53    $false | (spl8_2 | spl8_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f64,f23])).
% 0.20/0.53  fof(f64,plain,(
% 0.20/0.53    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (spl8_2 | spl8_3)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f58,f58,f28])).
% 0.20/0.53  fof(f58,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | (spl8_2 | spl8_3)),
% 0.20/0.53    inference(subsumption_resolution,[],[f57,f52])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ~r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl8_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f50])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    r2_hidden(k4_tarski(sK5(k1_xboole_0,k1_xboole_0),sK7(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(sK5(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl8_2),
% 0.20/0.53    inference(equality_resolution,[],[f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(k4_tarski(sK5(k1_xboole_0,X0),sK7(k1_xboole_0,X0)),k1_xboole_0) | r2_hidden(sK5(k1_xboole_0,X0),X0)) ) | spl8_2),
% 0.20/0.53    inference(superposition,[],[f44,f33])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl8_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f42])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ~spl8_1 | ~spl8_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f19,f42,f38])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  % (2380)Refutation not found, incomplete strategy% (2380)------------------------------
% 0.20/0.53  % (2380)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.20/0.53    inference(ennf_transformation,[],[f9])).
% 0.20/0.53  % (2380)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  fof(f9,negated_conjecture,(
% 0.20/0.53    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.20/0.53    inference(negated_conjecture,[],[f8])).
% 0.20/0.53  % (2380)Memory used [KB]: 10746
% 0.20/0.53  fof(f8,conjecture,(
% 0.20/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.20/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.20/0.53  % (2380)Time elapsed: 0.126 s
% 0.20/0.53  % (2380)------------------------------
% 0.20/0.53  % (2380)------------------------------
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (2369)------------------------------
% 0.20/0.53  % (2369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2369)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (2369)Memory used [KB]: 10874
% 0.20/0.53  % (2369)Time elapsed: 0.107 s
% 0.20/0.53  % (2369)------------------------------
% 0.20/0.53  % (2369)------------------------------
% 0.20/0.53  % (2385)Refutation not found, incomplete strategy% (2385)------------------------------
% 0.20/0.53  % (2385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (2385)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (2385)Memory used [KB]: 6140
% 0.20/0.53  % (2385)Time elapsed: 0.124 s
% 0.20/0.53  % (2385)------------------------------
% 0.20/0.53  % (2385)------------------------------
% 0.20/0.53  % (2359)Success in time 0.175 s
%------------------------------------------------------------------------------
