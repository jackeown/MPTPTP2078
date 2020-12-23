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
% DateTime   : Thu Dec  3 12:47:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 115 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :   12
%              Number of atoms          :  137 ( 323 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f377,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f154,f290,f336,f376])).

fof(f376,plain,
    ( ~ spl2_7
    | spl2_5 ),
    inference(avatar_split_clause,[],[f375,f152,f159])).

fof(f159,plain,
    ( spl2_7
  <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f152,plain,
    ( spl2_5
  <=> r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f375,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | spl2_5 ),
    inference(resolution,[],[f153,f43])).

fof(f43,plain,(
    ! [X1] :
      ( r1_tarski(X1,k3_relat_1(sK1))
      | ~ r1_tarski(X1,k2_relat_1(sK1)) ) ),
    inference(superposition,[],[f29,f37])).

fof(f37,plain,(
    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1)) ),
    inference(resolution,[],[f24,f19])).

fof(f19,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f153,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f152])).

fof(f336,plain,(
    spl2_4 ),
    inference(avatar_contradiction_clause,[],[f335])).

fof(f335,plain,
    ( $false
    | spl2_4 ),
    inference(subsumption_resolution,[],[f334,f150])).

fof(f150,plain,
    ( ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))
    | spl2_4 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl2_4
  <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f334,plain,(
    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f327,f23])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f327,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_relat_1(sK1))
    | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(superposition,[],[f42,f203])).

fof(f203,plain,(
    k1_xboole_0 = k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(subsumption_resolution,[],[f196,f19])).

fof(f196,plain,
    ( ~ v1_relat_1(sK1)
    | k1_xboole_0 = k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1)) ),
    inference(resolution,[],[f83,f20])).

fof(f20,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f83,plain,(
    ! [X1] :
      ( ~ r1_tarski(sK0,X1)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k4_xboole_0(k1_relat_1(sK0),k1_relat_1(X1)) ) ),
    inference(resolution,[],[f49,f22])).

fof(f22,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_tarski(X1,X0)
      | ~ v1_relat_1(X0)
      | k1_xboole_0 = k4_xboole_0(k1_relat_1(X1),k1_relat_1(X0)) ) ),
    inference(resolution,[],[f25,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

fof(f42,plain,(
    ! [X0] :
      ( ~ r1_tarski(k4_xboole_0(X0,k1_relat_1(sK1)),k2_relat_1(sK1))
      | r1_tarski(X0,k3_relat_1(sK1)) ) ),
    inference(superposition,[],[f30,f37])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f290,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f289])).

fof(f289,plain,
    ( $false
    | spl2_7 ),
    inference(subsumption_resolution,[],[f288,f22])).

fof(f288,plain,
    ( ~ v1_relat_1(sK0)
    | spl2_7 ),
    inference(subsumption_resolution,[],[f287,f20])).

fof(f287,plain,
    ( ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | spl2_7 ),
    inference(subsumption_resolution,[],[f286,f19])).

fof(f286,plain,
    ( ~ v1_relat_1(sK1)
    | ~ r1_tarski(sK0,sK1)
    | ~ v1_relat_1(sK0)
    | spl2_7 ),
    inference(resolution,[],[f160,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f160,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))
    | spl2_7 ),
    inference(avatar_component_clause,[],[f159])).

fof(f154,plain,
    ( ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f141,f152,f149])).

fof(f141,plain,
    ( ~ r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))
    | ~ r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(resolution,[],[f46,f21])).

fof(f21,plain,(
    ~ r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0] :
      ( r1_tarski(k3_relat_1(sK0),X0)
      | ~ r1_tarski(k2_relat_1(sK0),X0)
      | ~ r1_tarski(k1_relat_1(sK0),X0) ) ),
    inference(superposition,[],[f31,f38])).

fof(f38,plain,(
    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0)) ),
    inference(resolution,[],[f24,f22])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:57:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.42  % (9851)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.21/0.43  % (9853)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.21/0.44  % (9844)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.44  % (9850)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.45  % (9846)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.21/0.45  % (9847)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.45  % (9855)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.45  % (9852)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.21/0.45  % (9848)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.46  % (9849)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.47  % (9845)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.21/0.47  % (9847)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f377,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f154,f290,f336,f376])).
% 0.21/0.47  fof(f376,plain,(
% 0.21/0.47    ~spl2_7 | spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f375,f152,f159])).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    spl2_7 <=> r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    spl2_5 <=> r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.47  fof(f375,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | spl2_5),
% 0.21/0.47    inference(resolution,[],[f153,f43])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X1] : (r1_tarski(X1,k3_relat_1(sK1)) | ~r1_tarski(X1,k2_relat_1(sK1))) )),
% 0.21/0.47    inference(superposition,[],[f29,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    k3_relat_1(sK1) = k2_xboole_0(k1_relat_1(sK1),k2_relat_1(sK1))),
% 0.21/0.47    inference(resolution,[],[f24,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    v1_relat_1(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f8])).
% 0.21/0.47  fof(f8,conjecture,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | spl2_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f152])).
% 0.21/0.47  fof(f336,plain,(
% 0.21/0.47    spl2_4),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f335])).
% 0.21/0.47  fof(f335,plain,(
% 0.21/0.47    $false | spl2_4),
% 0.21/0.47    inference(subsumption_resolution,[],[f334,f150])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1)) | spl2_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f149])).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    spl2_4 <=> r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.47  fof(f334,plain,(
% 0.21/0.47    r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f327,f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.47  fof(f327,plain,(
% 0.21/0.47    ~r1_tarski(k1_xboole_0,k2_relat_1(sK1)) | r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.47    inference(superposition,[],[f42,f203])).
% 0.21/0.47  fof(f203,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f196,f19])).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    ~v1_relat_1(sK1) | k1_xboole_0 = k4_xboole_0(k1_relat_1(sK0),k1_relat_1(sK1))),
% 0.21/0.47    inference(resolution,[],[f83,f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X1] : (~r1_tarski(sK0,X1) | ~v1_relat_1(X1) | k1_xboole_0 = k4_xboole_0(k1_relat_1(sK0),k1_relat_1(X1))) )),
% 0.21/0.47    inference(resolution,[],[f49,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    v1_relat_1(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_tarski(X1,X0) | ~v1_relat_1(X0) | k1_xboole_0 = k4_xboole_0(k1_relat_1(X1),k1_relat_1(X0))) )),
% 0.21/0.47    inference(resolution,[],[f25,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(flattening,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(k4_xboole_0(X0,k1_relat_1(sK1)),k2_relat_1(sK1)) | r1_tarski(X0,k3_relat_1(sK1))) )),
% 0.21/0.47    inference(superposition,[],[f30,f37])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.21/0.47  fof(f290,plain,(
% 0.21/0.47    spl2_7),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f289])).
% 0.21/0.47  fof(f289,plain,(
% 0.21/0.47    $false | spl2_7),
% 0.21/0.47    inference(subsumption_resolution,[],[f288,f22])).
% 0.21/0.47  fof(f288,plain,(
% 0.21/0.47    ~v1_relat_1(sK0) | spl2_7),
% 0.21/0.47    inference(subsumption_resolution,[],[f287,f20])).
% 0.21/0.47  fof(f287,plain,(
% 0.21/0.47    ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0) | spl2_7),
% 0.21/0.47    inference(subsumption_resolution,[],[f286,f19])).
% 0.21/0.47  fof(f286,plain,(
% 0.21/0.47    ~v1_relat_1(sK1) | ~r1_tarski(sK0,sK1) | ~v1_relat_1(sK0) | spl2_7),
% 0.21/0.47    inference(resolution,[],[f160,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~r1_tarski(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f160,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(sK0),k2_relat_1(sK1)) | spl2_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f159])).
% 0.21/0.47  fof(f154,plain,(
% 0.21/0.47    ~spl2_4 | ~spl2_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f141,f152,f149])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ~r1_tarski(k2_relat_1(sK0),k3_relat_1(sK1)) | ~r1_tarski(k1_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.47    inference(resolution,[],[f46,f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ~r1_tarski(k3_relat_1(sK0),k3_relat_1(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0] : (r1_tarski(k3_relat_1(sK0),X0) | ~r1_tarski(k2_relat_1(sK0),X0) | ~r1_tarski(k1_relat_1(sK0),X0)) )),
% 0.21/0.47    inference(superposition,[],[f31,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    k3_relat_1(sK0) = k2_xboole_0(k1_relat_1(sK0),k2_relat_1(sK0))),
% 0.21/0.47    inference(resolution,[],[f24,f22])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (9847)------------------------------
% 0.21/0.47  % (9847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (9847)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (9847)Memory used [KB]: 11001
% 0.21/0.47  % (9847)Time elapsed: 0.029 s
% 0.21/0.47  % (9847)------------------------------
% 0.21/0.47  % (9847)------------------------------
% 0.21/0.48  % (9843)Success in time 0.118 s
%------------------------------------------------------------------------------
