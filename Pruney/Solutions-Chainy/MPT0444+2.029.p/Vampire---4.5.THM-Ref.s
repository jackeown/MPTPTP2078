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
% DateTime   : Thu Dec  3 12:47:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  87 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  128 ( 202 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f248,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f118,f215,f219,f231,f242])).

fof(f242,plain,
    ( ~ spl2_3
    | spl2_8
    | ~ spl2_16 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | ~ spl2_3
    | spl2_8
    | ~ spl2_16 ),
    inference(unit_resulting_resolution,[],[f51,f209,f91,f117,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f117,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl2_8
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f91,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X1) ),
    inference(forward_demodulation,[],[f86,f53])).

fof(f53,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X1)) ),
    inference(superposition,[],[f34,f53])).

fof(f34,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f209,plain,
    ( v1_relat_1(k3_xboole_0(sK0,sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl2_16
  <=> v1_relat_1(k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f51,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f49,plain,
    ( spl2_3
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f231,plain,(
    spl2_17 ),
    inference(avatar_contradiction_clause,[],[f228])).

fof(f228,plain,
    ( $false
    | spl2_17 ),
    inference(unit_resulting_resolution,[],[f28,f214])).

fof(f214,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | spl2_17 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl2_17
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

% (7208)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (7205)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f219,plain,
    ( ~ spl2_1
    | spl2_16 ),
    inference(avatar_split_clause,[],[f217,f208,f39])).

fof(f39,plain,
    ( spl2_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f217,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_16 ),
    inference(resolution,[],[f210,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k3_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k3_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

fof(f210,plain,
    ( ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f208])).

fof(f215,plain,
    ( ~ spl2_16
    | ~ spl2_17
    | ~ spl2_1
    | spl2_7 ),
    inference(avatar_split_clause,[],[f203,f111,f39,f212,f208])).

fof(f111,plain,
    ( spl2_7
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f203,plain,
    ( ~ v1_relat_1(sK0)
    | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK0)
    | ~ v1_relat_1(k3_xboole_0(sK0,sK1))
    | spl2_7 ),
    inference(resolution,[],[f27,f113])).

fof(f113,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f111])).

fof(f118,plain,
    ( ~ spl2_7
    | ~ spl2_8
    | spl2_2 ),
    inference(avatar_split_clause,[],[f104,f44,f115,f111])).

fof(f44,plain,
    ( spl2_2
  <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f104,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))
    | ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))
    | spl2_2 ),
    inference(resolution,[],[f35,f46])).

fof(f46,plain,
    ( ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))
    | spl2_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f52,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f21,f49])).

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).

fof(f47,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    ~ r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f42,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f23,f39])).

fof(f23,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n001.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:03:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (7195)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (7200)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (7206)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (7213)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.51  % (7197)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (7199)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (7209)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (7204)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (7219)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (7203)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (7207)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (7201)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (7216)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (7215)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (7217)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.54  % (7194)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (7196)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.54  % (7209)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f248,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f42,f47,f52,f118,f215,f219,f231,f242])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    ~spl2_3 | spl2_8 | ~spl2_16),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f240])).
% 0.21/0.54  fof(f240,plain,(
% 0.21/0.54    $false | (~spl2_3 | spl2_8 | ~spl2_16)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f51,f209,f91,f117,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f16])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(flattening,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) | spl2_8),
% 0.21/0.54    inference(avatar_component_clause,[],[f115])).
% 0.21/0.54  fof(f115,plain,(
% 0.21/0.54    spl2_8 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X1)) )),
% 0.21/0.54    inference(forward_demodulation,[],[f86,f53])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.54    inference(resolution,[],[f30,f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.54    inference(equality_resolution,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X1,X1))) )),
% 0.21/0.54    inference(superposition,[],[f34,f53])).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 0.21/0.54  fof(f209,plain,(
% 0.21/0.54    v1_relat_1(k3_xboole_0(sK0,sK1)) | ~spl2_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f208])).
% 0.21/0.54  fof(f208,plain,(
% 0.21/0.54    spl2_16 <=> v1_relat_1(k3_xboole_0(sK0,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    v1_relat_1(sK1) | ~spl2_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f49])).
% 0.21/0.54  fof(f49,plain,(
% 0.21/0.54    spl2_3 <=> v1_relat_1(sK1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.54  fof(f231,plain,(
% 0.21/0.54    spl2_17),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f228])).
% 0.21/0.54  fof(f228,plain,(
% 0.21/0.54    $false | spl2_17),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f28,f214])).
% 0.21/0.54  fof(f214,plain,(
% 0.21/0.54    ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | spl2_17),
% 0.21/0.54    inference(avatar_component_clause,[],[f212])).
% 0.21/0.54  fof(f212,plain,(
% 0.21/0.54    spl2_17 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.54  % (7208)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (7205)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.21/0.54  fof(f219,plain,(
% 0.21/0.54    ~spl2_1 | spl2_16),
% 0.21/0.54    inference(avatar_split_clause,[],[f217,f208,f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    spl2_1 <=> v1_relat_1(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    ~v1_relat_1(sK0) | spl2_16),
% 0.21/0.54    inference(resolution,[],[f210,f29])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(k3_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k3_xboole_0(X0,X1)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).
% 0.21/0.54  fof(f210,plain,(
% 0.21/0.54    ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f208])).
% 0.21/0.54  fof(f215,plain,(
% 0.21/0.54    ~spl2_16 | ~spl2_17 | ~spl2_1 | spl2_7),
% 0.21/0.54    inference(avatar_split_clause,[],[f203,f111,f39,f212,f208])).
% 0.21/0.54  fof(f111,plain,(
% 0.21/0.54    spl2_7 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.54  fof(f203,plain,(
% 0.21/0.54    ~v1_relat_1(sK0) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK0) | ~v1_relat_1(k3_xboole_0(sK0,sK1)) | spl2_7),
% 0.21/0.54    inference(resolution,[],[f27,f113])).
% 0.21/0.54  fof(f113,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) | spl2_7),
% 0.21/0.54    inference(avatar_component_clause,[],[f111])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    ~spl2_7 | ~spl2_8 | spl2_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f104,f44,f115,f111])).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    spl2_2 <=> r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.54  fof(f104,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK1)) | ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k2_relat_1(sK0)) | spl2_2),
% 0.21/0.54    inference(resolution,[],[f35,f46])).
% 0.21/0.54  fof(f46,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1))) | spl2_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f44])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f20])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.54    inference(flattening,[],[f19])).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.54    inference(ennf_transformation,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    spl2_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f21,f49])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    v1_relat_1(sK1)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,plain,(
% 0.21/0.54    ? [X0] : (? [X1] : (~r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1))) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,negated_conjecture,(
% 0.21/0.54    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.54    inference(negated_conjecture,[],[f10])).
% 0.21/0.54  fof(f10,conjecture,(
% 0.21/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k3_xboole_0(X0,X1)),k3_xboole_0(k2_relat_1(X0),k2_relat_1(X1)))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_relat_1)).
% 0.21/0.54  fof(f47,plain,(
% 0.21/0.54    ~spl2_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f22,f44])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ~r1_tarski(k2_relat_1(k3_xboole_0(sK0,sK1)),k3_xboole_0(k2_relat_1(sK0),k2_relat_1(sK1)))),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    spl2_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f23,f39])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    v1_relat_1(sK0)),
% 0.21/0.54    inference(cnf_transformation,[],[f12])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (7209)------------------------------
% 0.21/0.54  % (7209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7209)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (7209)Memory used [KB]: 6268
% 0.21/0.54  % (7209)Time elapsed: 0.066 s
% 0.21/0.54  % (7209)------------------------------
% 0.21/0.54  % (7209)------------------------------
% 0.21/0.54  % (7218)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (7193)Success in time 0.185 s
%------------------------------------------------------------------------------
