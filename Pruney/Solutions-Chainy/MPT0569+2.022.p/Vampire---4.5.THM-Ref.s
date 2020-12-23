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
% DateTime   : Thu Dec  3 12:50:29 EST 2020

% Result     : Theorem 1.10s
% Output     : Refutation 1.10s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 355 expanded)
%              Number of leaves         :   13 ( 100 expanded)
%              Depth                    :   17
%              Number of atoms          :  178 ( 975 expanded)
%              Number of equality atoms :   37 ( 122 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f330,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f112,f244,f328])).

fof(f328,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f327])).

fof(f327,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f53,f322,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != X0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

% (25848)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% (25843)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (25825)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (25822)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (25842)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f322,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl8_1
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f304,f304,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
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

fof(f304,plain,
    ( r2_hidden(sK6(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0)
    | ~ spl8_1
    | spl8_2 ),
    inference(forward_demodulation,[],[f300,f74])).

fof(f74,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f72,plain,
    ( spl8_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f300,plain,
    ( r2_hidden(sK6(sK1,sK2(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f33,f249,f248,f257,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X3,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X3),X2)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X0,k10_relat_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k10_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X0,X3),X2)
            & r2_hidden(X3,k2_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

fof(f257,plain,
    ( r2_hidden(k4_tarski(sK6(sK1,sK2(k2_relat_1(sK1),sK0)),sK2(k2_relat_1(sK1),sK0)),sK1)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f248,f62])).

fof(f62,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK6(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK6(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f248,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f77,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f77,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl8_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f249,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0)
    | spl8_2 ),
    inference(unit_resulting_resolution,[],[f77,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <~> r1_xboole_0(k2_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k10_relat_1(X1,X0)
        <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f244,plain,
    ( spl8_1
    | ~ spl8_2 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | spl8_1
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f73,f237])).

fof(f237,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f236,f64])).

fof(f64,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f33,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f236,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f233,f166])).

fof(f166,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl8_2 ),
    inference(backward_demodulation,[],[f138,f156])).

fof(f156,plain,
    ( ! [X0] : k1_xboole_0 = k2_relat_1(k4_xboole_0(X0,X0))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f125,f144,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK7(X0,X1),sK5(X0,X1)),X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f144,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl8_2 ),
    inference(superposition,[],[f125,f52])).

fof(f52,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f125,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f120,f121])).

fof(f121,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))) = X0
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f101,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f101,plain,
    ( ! [X0] : r1_xboole_0(X0,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f85,f39])).

fof(f85,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f80,f81])).

fof(f81,plain,
    ( k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f78,f36])).

fof(f78,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f80,plain,
    ( ! [X0] : ~ r2_hidden(X0,k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),sK0)))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f78,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f40,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f120,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f101,f60])).

fof(f138,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X0) = k2_relat_1(k4_xboole_0(X1,X1))
    | ~ spl8_2 ),
    inference(unit_resulting_resolution,[],[f125,f125,f48])).

fof(f233,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))
    | ~ spl8_2 ),
    inference(superposition,[],[f65,f81])).

fof(f65,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X0))) ),
    inference(unit_resulting_resolution,[],[f33,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f50,f55])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f73,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f112,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f32,f76,f72])).

fof(f32,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f31,f76,f72])).

fof(f31,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:05:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.49  % (25838)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.50  % (25847)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.50  % (25846)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.50  % (25820)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.50  % (25830)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (25823)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (25830)Refutation not found, incomplete strategy% (25830)------------------------------
% 0.20/0.51  % (25830)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (25827)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (25831)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (25826)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.10/0.52  % (25835)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.10/0.52  % (25830)Termination reason: Refutation not found, incomplete strategy
% 1.10/0.52  
% 1.10/0.52  % (25830)Memory used [KB]: 10746
% 1.10/0.52  % (25830)Time elapsed: 0.106 s
% 1.10/0.52  % (25830)------------------------------
% 1.10/0.52  % (25830)------------------------------
% 1.10/0.52  % (25821)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.10/0.52  % (25837)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.10/0.52  % (25834)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.10/0.52  % (25823)Refutation found. Thanks to Tanya!
% 1.10/0.52  % SZS status Theorem for theBenchmark
% 1.10/0.52  % SZS output start Proof for theBenchmark
% 1.10/0.52  fof(f330,plain,(
% 1.10/0.52    $false),
% 1.10/0.52    inference(avatar_sat_refutation,[],[f79,f112,f244,f328])).
% 1.10/0.52  fof(f328,plain,(
% 1.10/0.52    ~spl8_1 | spl8_2),
% 1.10/0.52    inference(avatar_contradiction_clause,[],[f327])).
% 1.10/0.52  fof(f327,plain,(
% 1.10/0.52    $false | (~spl8_1 | spl8_2)),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f53,f322,f35])).
% 1.10/0.52  fof(f35,plain,(
% 1.10/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != X0 | r1_xboole_0(X0,X1)) )),
% 1.10/0.52    inference(cnf_transformation,[],[f10])).
% 1.10/0.52  % (25848)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.10/0.52  % (25843)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.10/0.52  % (25825)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.10/0.52  % (25822)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.10/0.52  % (25842)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.10/0.52  fof(f10,axiom,(
% 1.10/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.10/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.10/0.52  fof(f322,plain,(
% 1.10/0.52    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl8_1 | spl8_2)),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f304,f304,f37])).
% 1.10/0.52  fof(f37,plain,(
% 1.10/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.10/0.52    inference(cnf_transformation,[],[f26])).
% 1.10/0.52  fof(f26,plain,(
% 1.10/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.10/0.52    inference(ennf_transformation,[],[f22])).
% 1.10/0.52  fof(f22,plain,(
% 1.10/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.10/0.52    inference(rectify,[],[f3])).
% 1.10/0.52  fof(f3,axiom,(
% 1.10/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.10/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.10/0.52  fof(f304,plain,(
% 1.10/0.52    r2_hidden(sK6(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0) | (~spl8_1 | spl8_2)),
% 1.10/0.52    inference(forward_demodulation,[],[f300,f74])).
% 1.10/0.52  fof(f74,plain,(
% 1.10/0.52    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl8_1),
% 1.10/0.52    inference(avatar_component_clause,[],[f72])).
% 1.10/0.52  fof(f72,plain,(
% 1.10/0.52    spl8_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.10/0.52  fof(f300,plain,(
% 1.10/0.52    r2_hidden(sK6(sK1,sK2(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0)) | spl8_2),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f33,f249,f248,f257,f45])).
% 1.10/0.52  fof(f45,plain,(
% 1.10/0.52    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X3,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X3),X2) | ~r2_hidden(X3,X1) | r2_hidden(X0,k10_relat_1(X2,X1))) )),
% 1.10/0.52    inference(cnf_transformation,[],[f28])).
% 1.10/0.52  fof(f28,plain,(
% 1.10/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))) | ~v1_relat_1(X2))),
% 1.10/0.52    inference(ennf_transformation,[],[f17])).
% 1.10/0.52  fof(f17,axiom,(
% 1.10/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k10_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X0,X3),X2) & r2_hidden(X3,k2_relat_1(X2)))))),
% 1.10/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).
% 1.10/0.52  fof(f257,plain,(
% 1.10/0.52    r2_hidden(k4_tarski(sK6(sK1,sK2(k2_relat_1(sK1),sK0)),sK2(k2_relat_1(sK1),sK0)),sK1) | spl8_2),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f248,f62])).
% 1.10/0.52  fof(f62,plain,(
% 1.10/0.52    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK6(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.10/0.52    inference(equality_resolution,[],[f47])).
% 1.10/0.52  fof(f47,plain,(
% 1.10/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK6(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.10/0.52    inference(cnf_transformation,[],[f16])).
% 1.10/0.52  fof(f16,axiom,(
% 1.10/0.52    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.10/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.10/0.52  fof(f248,plain,(
% 1.10/0.52    r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | spl8_2),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f77,f38])).
% 1.10/0.52  fof(f38,plain,(
% 1.10/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.10/0.52    inference(cnf_transformation,[],[f26])).
% 1.10/0.52  fof(f77,plain,(
% 1.10/0.52    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl8_2),
% 1.10/0.52    inference(avatar_component_clause,[],[f76])).
% 1.10/0.52  fof(f76,plain,(
% 1.10/0.52    spl8_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.10/0.52    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.10/0.52  fof(f249,plain,(
% 1.10/0.52    r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0) | spl8_2),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f77,f39])).
% 1.10/0.52  fof(f39,plain,(
% 1.10/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.10/0.52    inference(cnf_transformation,[],[f26])).
% 1.10/0.52  fof(f33,plain,(
% 1.10/0.52    v1_relat_1(sK1)),
% 1.10/0.52    inference(cnf_transformation,[],[f24])).
% 1.10/0.52  fof(f24,plain,(
% 1.10/0.52    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.10/0.52    inference(ennf_transformation,[],[f21])).
% 1.10/0.52  fof(f21,negated_conjecture,(
% 1.10/0.52    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.10/0.52    inference(negated_conjecture,[],[f20])).
% 1.10/0.52  fof(f20,conjecture,(
% 1.10/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.10/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.10/0.52  fof(f53,plain,(
% 1.10/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 1.10/0.52    inference(cnf_transformation,[],[f8])).
% 1.10/0.52  fof(f8,axiom,(
% 1.10/0.52    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 1.10/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 1.10/0.52  fof(f244,plain,(
% 1.10/0.52    spl8_1 | ~spl8_2),
% 1.10/0.52    inference(avatar_contradiction_clause,[],[f239])).
% 1.10/0.52  fof(f239,plain,(
% 1.10/0.52    $false | (spl8_1 | ~spl8_2)),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f73,f237])).
% 1.10/0.52  fof(f237,plain,(
% 1.10/0.52    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl8_2),
% 1.10/0.52    inference(forward_demodulation,[],[f236,f64])).
% 1.10/0.52  fof(f64,plain,(
% 1.10/0.52    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f33,f51])).
% 1.10/0.52  fof(f51,plain,(
% 1.10/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)) )),
% 1.10/0.52    inference(cnf_transformation,[],[f30])).
% 1.10/0.52  fof(f30,plain,(
% 1.10/0.52    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.10/0.52    inference(ennf_transformation,[],[f19])).
% 1.10/0.52  fof(f19,axiom,(
% 1.10/0.52    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 1.10/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 1.10/0.52  fof(f236,plain,(
% 1.10/0.52    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0) | ~spl8_2),
% 1.10/0.52    inference(forward_demodulation,[],[f233,f166])).
% 1.10/0.52  fof(f166,plain,(
% 1.10/0.52    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl8_2),
% 1.10/0.52    inference(backward_demodulation,[],[f138,f156])).
% 1.10/0.52  fof(f156,plain,(
% 1.10/0.52    ( ! [X0] : (k1_xboole_0 = k2_relat_1(k4_xboole_0(X0,X0))) ) | ~spl8_2),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f125,f144,f48])).
% 1.10/0.52  fof(f48,plain,(
% 1.10/0.52    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK7(X0,X1),sK5(X0,X1)),X0) | r2_hidden(sK5(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.10/0.52    inference(cnf_transformation,[],[f16])).
% 1.10/0.52  fof(f144,plain,(
% 1.10/0.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl8_2),
% 1.10/0.52    inference(superposition,[],[f125,f52])).
% 1.10/0.52  fof(f52,plain,(
% 1.10/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.10/0.52    inference(cnf_transformation,[],[f6])).
% 1.10/0.52  fof(f6,axiom,(
% 1.10/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.10/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.10/0.52  fof(f125,plain,(
% 1.10/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) ) | ~spl8_2),
% 1.10/0.52    inference(forward_demodulation,[],[f120,f121])).
% 1.10/0.52  fof(f121,plain,(
% 1.10/0.52    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))) = X0) ) | ~spl8_2),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f101,f36])).
% 1.10/0.52  fof(f36,plain,(
% 1.10/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.10/0.52    inference(cnf_transformation,[],[f10])).
% 1.10/0.52  fof(f101,plain,(
% 1.10/0.52    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))) ) | ~spl8_2),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f85,f39])).
% 1.10/0.52  fof(f85,plain,(
% 1.10/0.52    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))) ) | ~spl8_2),
% 1.10/0.52    inference(forward_demodulation,[],[f80,f81])).
% 1.10/0.52  fof(f81,plain,(
% 1.10/0.52    k2_relat_1(sK1) = k4_xboole_0(k2_relat_1(sK1),sK0) | ~spl8_2),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f78,f36])).
% 1.10/0.52  fof(f78,plain,(
% 1.10/0.52    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl8_2),
% 1.10/0.52    inference(avatar_component_clause,[],[f76])).
% 1.10/0.52  fof(f80,plain,(
% 1.10/0.52    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),sK0)))) ) | ~spl8_2),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f78,f60])).
% 1.10/0.52  fof(f60,plain,(
% 1.10/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.10/0.52    inference(definition_unfolding,[],[f40,f55])).
% 1.10/0.52  fof(f55,plain,(
% 1.10/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.10/0.52    inference(cnf_transformation,[],[f7])).
% 1.10/0.52  fof(f7,axiom,(
% 1.10/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.10/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.10/0.52  fof(f40,plain,(
% 1.10/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.10/0.52    inference(cnf_transformation,[],[f27])).
% 1.10/0.52  fof(f27,plain,(
% 1.10/0.52    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.10/0.52    inference(ennf_transformation,[],[f23])).
% 1.10/0.52  fof(f23,plain,(
% 1.10/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.10/0.52    inference(rectify,[],[f4])).
% 1.10/0.52  fof(f4,axiom,(
% 1.10/0.52    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.10/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.10/0.52  fof(f120,plain,(
% 1.10/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1)))))) ) | ~spl8_2),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f101,f60])).
% 1.10/0.52  fof(f138,plain,(
% 1.10/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k2_relat_1(k4_xboole_0(X1,X1))) ) | ~spl8_2),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f125,f125,f48])).
% 1.10/0.52  fof(f233,plain,(
% 1.10/0.52    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k2_relat_1(sK1))) | ~spl8_2),
% 1.10/0.52    inference(superposition,[],[f65,f81])).
% 1.10/0.52  fof(f65,plain,(
% 1.10/0.52    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k4_xboole_0(k2_relat_1(sK1),k4_xboole_0(k2_relat_1(sK1),X0)))) )),
% 1.10/0.52    inference(unit_resulting_resolution,[],[f33,f61])).
% 1.10/0.52  fof(f61,plain,(
% 1.10/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k4_xboole_0(k2_relat_1(X1),k4_xboole_0(k2_relat_1(X1),X0)))) )),
% 1.10/0.52    inference(definition_unfolding,[],[f50,f55])).
% 1.10/0.52  fof(f50,plain,(
% 1.10/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 1.10/0.52    inference(cnf_transformation,[],[f29])).
% 1.10/0.52  fof(f29,plain,(
% 1.10/0.52    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.10/0.52    inference(ennf_transformation,[],[f18])).
% 1.10/0.52  fof(f18,axiom,(
% 1.10/0.52    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.10/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.10/0.52  fof(f73,plain,(
% 1.10/0.52    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl8_1),
% 1.10/0.52    inference(avatar_component_clause,[],[f72])).
% 1.10/0.52  fof(f112,plain,(
% 1.10/0.52    ~spl8_1 | ~spl8_2),
% 1.10/0.52    inference(avatar_split_clause,[],[f32,f76,f72])).
% 1.10/0.52  fof(f32,plain,(
% 1.10/0.52    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 1.10/0.52    inference(cnf_transformation,[],[f24])).
% 1.10/0.52  fof(f79,plain,(
% 1.10/0.52    spl8_1 | spl8_2),
% 1.10/0.52    inference(avatar_split_clause,[],[f31,f76,f72])).
% 1.10/0.52  fof(f31,plain,(
% 1.10/0.52    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.10/0.52    inference(cnf_transformation,[],[f24])).
% 1.10/0.52  % SZS output end Proof for theBenchmark
% 1.10/0.52  % (25823)------------------------------
% 1.10/0.52  % (25823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.10/0.52  % (25823)Termination reason: Refutation
% 1.10/0.52  
% 1.10/0.52  % (25823)Memory used [KB]: 6396
% 1.10/0.52  % (25823)Time elapsed: 0.102 s
% 1.10/0.52  % (25823)------------------------------
% 1.10/0.52  % (25823)------------------------------
% 1.10/0.52  % (25828)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.10/0.53  % (25839)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.10/0.53  % (25844)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.10/0.53  % (25832)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.10/0.53  % (25845)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.10/0.53  % (25840)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.10/0.53  % (25836)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.25/0.53  % (25836)Refutation not found, incomplete strategy% (25836)------------------------------
% 1.25/0.53  % (25836)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (25836)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (25836)Memory used [KB]: 10618
% 1.25/0.53  % (25836)Time elapsed: 0.130 s
% 1.25/0.53  % (25836)------------------------------
% 1.25/0.53  % (25836)------------------------------
% 1.25/0.53  % (25829)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.25/0.54  % (25829)Refutation not found, incomplete strategy% (25829)------------------------------
% 1.25/0.54  % (25829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (25829)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.54  
% 1.25/0.54  % (25829)Memory used [KB]: 10618
% 1.25/0.54  % (25829)Time elapsed: 0.124 s
% 1.25/0.54  % (25829)------------------------------
% 1.25/0.54  % (25829)------------------------------
% 1.25/0.54  % (25828)Refutation not found, incomplete strategy% (25828)------------------------------
% 1.25/0.54  % (25828)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.54  % (25818)Success in time 0.171 s
%------------------------------------------------------------------------------
