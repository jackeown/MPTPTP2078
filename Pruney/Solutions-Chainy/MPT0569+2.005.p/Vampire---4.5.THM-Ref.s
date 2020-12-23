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
% DateTime   : Thu Dec  3 12:50:27 EST 2020

% Result     : Theorem 1.21s
% Output     : Refutation 1.21s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 132 expanded)
%              Number of leaves         :   11 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  151 ( 355 expanded)
%              Number of equality atoms :   30 (  61 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f495,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f110,f137,f494])).

% (17238)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f494,plain,
    ( ~ spl10_1
    | spl10_2 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | ~ spl10_1
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f26,f482,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f482,plain,
    ( r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),sK0)),k3_xboole_0(k1_xboole_0,k1_xboole_0))
    | ~ spl10_1
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f477,f477,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f477,plain,
    ( r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0)
    | ~ spl10_1
    | spl10_2 ),
    inference(forward_demodulation,[],[f460,f66])).

fof(f66,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl10_1
  <=> k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f460,plain,
    ( r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0))
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f142,f141,f172])).

fof(f172,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK4(sK1,X2),k10_relat_1(sK1,X3))
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f60,f45])).

fof(f45,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,k2_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X2),X2),X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

fof(f60,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(k4_tarski(X8,X9),sK1)
      | ~ r2_hidden(X9,X10)
      | r2_hidden(X8,k10_relat_1(sK1,X10)) ) ),
    inference(resolution,[],[f21,f50])).

fof(f50,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k10_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k10_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X3,X4),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f21,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f141,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1))
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f138,f49])).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f138,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),k3_xboole_0(k2_relat_1(sK1),sK0))
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f69,f25])).

% (17243)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl10_2
  <=> r1_xboole_0(k2_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f142,plain,
    ( r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0)
    | spl10_2 ),
    inference(unit_resulting_resolution,[],[f138,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f26,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f137,plain,
    ( spl10_1
    | ~ spl10_2 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl10_1
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f65,f132])).

fof(f132,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    | ~ spl10_2 ),
    inference(forward_demodulation,[],[f131,f54])).

fof(f54,plain,(
    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f21,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f131,plain,
    ( k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0)
    | ~ spl10_2 ),
    inference(superposition,[],[f53,f73])).

fof(f73,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl10_2 ),
    inference(unit_resulting_resolution,[],[f70,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f70,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f53,plain,(
    ! [X0] : k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0)) ),
    inference(unit_resulting_resolution,[],[f21,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f65,plain,
    ( k1_xboole_0 != k10_relat_1(sK1,sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f110,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f20,f68,f64])).

fof(f20,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 != k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f19,f68,f64])).

fof(f19,plain,
    ( r1_xboole_0(k2_relat_1(sK1),sK0)
    | k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:15:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (17242)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.48  % (17266)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.49  % (17258)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.49  % (17241)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.49  % (17250)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.50  % (17260)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.50  % (17252)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.50  % (17249)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (17244)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.51  % (17265)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.21/0.51  % (17241)Refutation found. Thanks to Tanya!
% 1.21/0.51  % SZS status Theorem for theBenchmark
% 1.21/0.51  % (17240)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.21/0.51  % (17239)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.21/0.51  % SZS output start Proof for theBenchmark
% 1.21/0.51  fof(f495,plain,(
% 1.21/0.51    $false),
% 1.21/0.51    inference(avatar_sat_refutation,[],[f71,f110,f137,f494])).
% 1.21/0.51  % (17238)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.21/0.51  fof(f494,plain,(
% 1.21/0.51    ~spl10_1 | spl10_2),
% 1.21/0.51    inference(avatar_contradiction_clause,[],[f489])).
% 1.21/0.51  fof(f489,plain,(
% 1.21/0.51    $false | (~spl10_1 | spl10_2)),
% 1.21/0.51    inference(unit_resulting_resolution,[],[f26,f482,f24])).
% 1.21/0.51  fof(f24,plain,(
% 1.21/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.21/0.51    inference(cnf_transformation,[],[f15])).
% 1.21/0.51  fof(f15,plain,(
% 1.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.21/0.51    inference(ennf_transformation,[],[f13])).
% 1.21/0.51  fof(f13,plain,(
% 1.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.21/0.51    inference(rectify,[],[f3])).
% 1.21/0.51  fof(f3,axiom,(
% 1.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.21/0.52  fof(f482,plain,(
% 1.21/0.52    r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),sK0)),k3_xboole_0(k1_xboole_0,k1_xboole_0)) | (~spl10_1 | spl10_2)),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f477,f477,f47])).
% 1.21/0.52  fof(f47,plain,(
% 1.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_xboole_0(X0,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.21/0.52    inference(equality_resolution,[],[f37])).
% 1.21/0.52  fof(f37,plain,(
% 1.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X0) | ~r2_hidden(X3,X1) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.21/0.52    inference(cnf_transformation,[],[f1])).
% 1.21/0.52  fof(f1,axiom,(
% 1.21/0.52    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.21/0.52  fof(f477,plain,(
% 1.21/0.52    r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),sK0)),k1_xboole_0) | (~spl10_1 | spl10_2)),
% 1.21/0.52    inference(forward_demodulation,[],[f460,f66])).
% 1.21/0.52  fof(f66,plain,(
% 1.21/0.52    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl10_1),
% 1.21/0.52    inference(avatar_component_clause,[],[f64])).
% 1.21/0.52  fof(f64,plain,(
% 1.21/0.52    spl10_1 <=> k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.21/0.52  fof(f460,plain,(
% 1.21/0.52    r2_hidden(sK4(sK1,sK2(k2_relat_1(sK1),sK0)),k10_relat_1(sK1,sK0)) | spl10_2),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f142,f141,f172])).
% 1.21/0.52  fof(f172,plain,(
% 1.21/0.52    ( ! [X2,X3] : (r2_hidden(sK4(sK1,X2),k10_relat_1(sK1,X3)) | ~r2_hidden(X2,X3) | ~r2_hidden(X2,k2_relat_1(sK1))) )),
% 1.21/0.52    inference(resolution,[],[f60,f45])).
% 1.21/0.52  fof(f45,plain,(
% 1.21/0.52    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,k2_relat_1(X0))) )),
% 1.21/0.52    inference(equality_resolution,[],[f28])).
% 1.21/0.52  fof(f28,plain,(
% 1.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X2),X2),X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 1.21/0.52    inference(cnf_transformation,[],[f8])).
% 1.21/0.52  fof(f8,axiom,(
% 1.21/0.52    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).
% 1.21/0.52  fof(f60,plain,(
% 1.21/0.52    ( ! [X10,X8,X9] : (~r2_hidden(k4_tarski(X8,X9),sK1) | ~r2_hidden(X9,X10) | r2_hidden(X8,k10_relat_1(sK1,X10))) )),
% 1.21/0.52    inference(resolution,[],[f21,f50])).
% 1.21/0.52  fof(f50,plain,(
% 1.21/0.52    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,k10_relat_1(X0,X1))) )),
% 1.21/0.52    inference(equality_resolution,[],[f44])).
% 1.21/0.52  fof(f44,plain,(
% 1.21/0.52    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,X2) | k10_relat_1(X0,X1) != X2) )),
% 1.21/0.52    inference(cnf_transformation,[],[f18])).
% 1.21/0.52  fof(f18,plain,(
% 1.21/0.52    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))) | ~v1_relat_1(X0))),
% 1.21/0.52    inference(ennf_transformation,[],[f7])).
% 1.21/0.52  fof(f7,axiom,(
% 1.21/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X3,X4),X0)))))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).
% 1.21/0.52  fof(f21,plain,(
% 1.21/0.52    v1_relat_1(sK1)),
% 1.21/0.52    inference(cnf_transformation,[],[f14])).
% 1.21/0.52  fof(f14,plain,(
% 1.21/0.52    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <~> r1_xboole_0(k2_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.21/0.52    inference(ennf_transformation,[],[f12])).
% 1.21/0.52  fof(f12,negated_conjecture,(
% 1.21/0.52    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.21/0.52    inference(negated_conjecture,[],[f11])).
% 1.21/0.52  fof(f11,conjecture,(
% 1.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 1.21/0.52  fof(f141,plain,(
% 1.21/0.52    r2_hidden(sK2(k2_relat_1(sK1),sK0),k2_relat_1(sK1)) | spl10_2),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f138,f49])).
% 1.21/0.52  fof(f49,plain,(
% 1.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 1.21/0.52    inference(equality_resolution,[],[f35])).
% 1.21/0.52  fof(f35,plain,(
% 1.21/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.21/0.52    inference(cnf_transformation,[],[f1])).
% 1.21/0.52  fof(f138,plain,(
% 1.21/0.52    r2_hidden(sK2(k2_relat_1(sK1),sK0),k3_xboole_0(k2_relat_1(sK1),sK0)) | spl10_2),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f69,f25])).
% 1.21/0.52  % (17243)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.21/0.52  fof(f25,plain,(
% 1.21/0.52    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f15])).
% 1.21/0.52  fof(f69,plain,(
% 1.21/0.52    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl10_2),
% 1.21/0.52    inference(avatar_component_clause,[],[f68])).
% 1.21/0.52  fof(f68,plain,(
% 1.21/0.52    spl10_2 <=> r1_xboole_0(k2_relat_1(sK1),sK0)),
% 1.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.21/0.52  fof(f142,plain,(
% 1.21/0.52    r2_hidden(sK2(k2_relat_1(sK1),sK0),sK0) | spl10_2),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f138,f48])).
% 1.21/0.52  fof(f48,plain,(
% 1.21/0.52    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,k3_xboole_0(X0,X1))) )),
% 1.21/0.52    inference(equality_resolution,[],[f36])).
% 1.21/0.52  fof(f36,plain,(
% 1.21/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.21/0.52    inference(cnf_transformation,[],[f1])).
% 1.21/0.52  fof(f26,plain,(
% 1.21/0.52    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f4])).
% 1.21/0.52  fof(f4,axiom,(
% 1.21/0.52    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.21/0.52  fof(f137,plain,(
% 1.21/0.52    spl10_1 | ~spl10_2),
% 1.21/0.52    inference(avatar_contradiction_clause,[],[f133])).
% 1.21/0.52  fof(f133,plain,(
% 1.21/0.52    $false | (spl10_1 | ~spl10_2)),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f65,f132])).
% 1.21/0.52  fof(f132,plain,(
% 1.21/0.52    k1_xboole_0 = k10_relat_1(sK1,sK0) | ~spl10_2),
% 1.21/0.52    inference(forward_demodulation,[],[f131,f54])).
% 1.21/0.52  fof(f54,plain,(
% 1.21/0.52    k1_xboole_0 = k10_relat_1(sK1,k1_xboole_0)),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f21,f38])).
% 1.21/0.52  fof(f38,plain,(
% 1.21/0.52    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)) )),
% 1.21/0.52    inference(cnf_transformation,[],[f17])).
% 1.21/0.52  fof(f17,plain,(
% 1.21/0.52    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 1.21/0.52    inference(ennf_transformation,[],[f10])).
% 1.21/0.52  fof(f10,axiom,(
% 1.21/0.52    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 1.21/0.52  fof(f131,plain,(
% 1.21/0.52    k10_relat_1(sK1,sK0) = k10_relat_1(sK1,k1_xboole_0) | ~spl10_2),
% 1.21/0.52    inference(superposition,[],[f53,f73])).
% 1.21/0.52  fof(f73,plain,(
% 1.21/0.52    k1_xboole_0 = k3_xboole_0(k2_relat_1(sK1),sK0) | ~spl10_2),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f70,f23])).
% 1.21/0.52  fof(f23,plain,(
% 1.21/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.21/0.52    inference(cnf_transformation,[],[f2])).
% 1.21/0.52  fof(f2,axiom,(
% 1.21/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.21/0.52  fof(f70,plain,(
% 1.21/0.52    r1_xboole_0(k2_relat_1(sK1),sK0) | ~spl10_2),
% 1.21/0.52    inference(avatar_component_clause,[],[f68])).
% 1.21/0.52  fof(f53,plain,(
% 1.21/0.52    ( ! [X0] : (k10_relat_1(sK1,X0) = k10_relat_1(sK1,k3_xboole_0(k2_relat_1(sK1),X0))) )),
% 1.21/0.52    inference(unit_resulting_resolution,[],[f21,f31])).
% 1.21/0.52  fof(f31,plain,(
% 1.21/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))) )),
% 1.21/0.52    inference(cnf_transformation,[],[f16])).
% 1.21/0.52  fof(f16,plain,(
% 1.21/0.52    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.21/0.52    inference(ennf_transformation,[],[f9])).
% 1.21/0.52  fof(f9,axiom,(
% 1.21/0.52    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 1.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 1.21/0.52  fof(f65,plain,(
% 1.21/0.52    k1_xboole_0 != k10_relat_1(sK1,sK0) | spl10_1),
% 1.21/0.52    inference(avatar_component_clause,[],[f64])).
% 1.21/0.52  fof(f110,plain,(
% 1.21/0.52    ~spl10_1 | ~spl10_2),
% 1.21/0.52    inference(avatar_split_clause,[],[f20,f68,f64])).
% 1.21/0.52  fof(f20,plain,(
% 1.21/0.52    ~r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 != k10_relat_1(sK1,sK0)),
% 1.21/0.52    inference(cnf_transformation,[],[f14])).
% 1.21/0.52  fof(f71,plain,(
% 1.21/0.52    spl10_1 | spl10_2),
% 1.21/0.52    inference(avatar_split_clause,[],[f19,f68,f64])).
% 1.21/0.52  fof(f19,plain,(
% 1.21/0.52    r1_xboole_0(k2_relat_1(sK1),sK0) | k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 1.21/0.52    inference(cnf_transformation,[],[f14])).
% 1.21/0.52  % SZS output end Proof for theBenchmark
% 1.21/0.52  % (17241)------------------------------
% 1.21/0.52  % (17241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.21/0.52  % (17241)Termination reason: Refutation
% 1.21/0.52  
% 1.21/0.52  % (17241)Memory used [KB]: 6652
% 1.21/0.52  % (17241)Time elapsed: 0.103 s
% 1.21/0.52  % (17241)------------------------------
% 1.21/0.52  % (17241)------------------------------
% 1.21/0.52  % (17236)Success in time 0.163 s
%------------------------------------------------------------------------------
