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
% DateTime   : Thu Dec  3 12:50:38 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  81 expanded)
%              Number of leaves         :   11 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :  133 ( 247 expanded)
%              Number of equality atoms :   25 (  70 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f166,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f147,f157,f165])).

fof(f165,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f162])).

fof(f162,plain,
    ( $false
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f26,f161,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f161,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_xboole_0,X0)
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f159,f34])).

fof(f34,plain,(
    ~ sQ2_eqProxy(k1_xboole_0,sK0) ),
    inference(equality_proxy_replacement,[],[f21,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( sQ2_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).

% (7244)Refutation not found, incomplete strategy% (7244)------------------------------
% (7244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f21,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( k1_xboole_0 = k10_relat_1(sK1,sK0)
    & r1_tarski(sK0,k2_relat_1(sK1))
    & k1_xboole_0 != sK0
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).

fof(f17,plain,
    ( ? [X0,X1] :
        ( k1_xboole_0 = k10_relat_1(X1,X0)
        & r1_tarski(X0,k2_relat_1(X1))
        & k1_xboole_0 != X0
        & v1_relat_1(X1) )
   => ( k1_xboole_0 = k10_relat_1(sK1,sK0)
      & r1_tarski(sK0,k2_relat_1(sK1))
      & k1_xboole_0 != sK0
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k10_relat_1(X1,X0)
      & r1_tarski(X0,k2_relat_1(X1))
      & k1_xboole_0 != X0
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
            & r1_tarski(X0,k2_relat_1(X1))
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( k1_xboole_0 = k10_relat_1(X1,X0)
          & r1_tarski(X0,k2_relat_1(X1))
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

fof(f159,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | sQ2_eqProxy(k1_xboole_0,sK0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f146,f24])).

fof(f24,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X0,X1)
        | sQ2_eqProxy(X0,sK0) )
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl3_2
  <=> ! [X1,X0] :
        ( sQ2_eqProxy(X0,sK0)
        | ~ r1_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f26,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f157,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f155,f20])).

fof(f20,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f155,plain,
    ( ~ v1_relat_1(sK1)
    | spl3_1 ),
    inference(subsumption_resolution,[],[f151,f33])).

fof(f33,plain,(
    sQ2_eqProxy(k1_xboole_0,k10_relat_1(sK1,sK0)) ),
    inference(equality_proxy_replacement,[],[f23,f32])).

fof(f23,plain,(
    k1_xboole_0 = k10_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f151,plain,
    ( ~ sQ2_eqProxy(k1_xboole_0,k10_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | spl3_1 ),
    inference(resolution,[],[f149,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | ~ sQ2_eqProxy(k1_xboole_0,k10_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f28,f32])).

% (7245)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f28,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 != k10_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k10_relat_1(X1,X0)
          | ~ r1_xboole_0(k2_relat_1(X1),X0) )
        & ( r1_xboole_0(k2_relat_1(X1),X0)
          | k1_xboole_0 != k10_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

fof(f149,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK1),sK0)
    | spl3_1 ),
    inference(resolution,[],[f143,f30])).

fof(f143,plain,
    ( ~ r1_xboole_0(sK0,k2_relat_1(sK1))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f141])).

fof(f141,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,k2_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f147,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f125,f145,f141])).

fof(f125,plain,(
    ! [X0,X1] :
      ( sQ2_eqProxy(X0,sK0)
      | ~ r1_xboole_0(sK0,k2_relat_1(sK1))
      | ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f100,f22])).

fof(f22,plain,(
    r1_tarski(sK0,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f100,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ r1_tarski(X5,X6)
      | sQ2_eqProxy(X7,X5)
      | ~ r1_xboole_0(X5,X6)
      | ~ r1_tarski(X7,X8)
      | ~ r1_xboole_0(X7,X8) ) ),
    inference(resolution,[],[f52,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f52,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_xboole_0(X5)
      | ~ r1_xboole_0(X3,X4)
      | sQ2_eqProxy(X5,X3)
      | ~ r1_tarski(X3,X4) ) ),
    inference(resolution,[],[f27,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | sQ2_eqProxy(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f31,f32])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:46:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (7236)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (7237)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (7236)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (7244)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f166,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f147,f157,f165])).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    ~spl3_2),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f162])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    $false | ~spl3_2),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f26,f161,f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0)) ) | ~spl3_2),
% 0.20/0.47    inference(subsumption_resolution,[],[f159,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ~sQ2_eqProxy(k1_xboole_0,sK0)),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f21,f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X1,X0] : (sQ2_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.47    introduced(equality_proxy_definition,[new_symbols(naming,[sQ2_eqProxy])])).
% 0.20/0.47  % (7244)Refutation not found, incomplete strategy% (7244)------------------------------
% 0.20/0.47  % (7244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    k1_xboole_0 != sK0),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1)) => (k1_xboole_0 = k10_relat_1(sK1,sK0) & r1_tarski(sK0,k2_relat_1(sK1)) & k1_xboole_0 != sK0 & v1_relat_1(sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f11,plain,(
% 0.20/0.47    ? [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0 & v1_relat_1(X1))),
% 0.20/0.47    inference(flattening,[],[f10])).
% 0.20/0.47  fof(f10,plain,(
% 0.20/0.47    ? [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0) & v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.47    inference(negated_conjecture,[],[f8])).
% 0.20/0.47  fof(f8,conjecture,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => ~(k1_xboole_0 = k10_relat_1(X1,X0) & r1_tarski(X0,k2_relat_1(X1)) & k1_xboole_0 != X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    ( ! [X0] : (~r1_xboole_0(k1_xboole_0,X0) | sQ2_eqProxy(k1_xboole_0,sK0)) ) | ~spl3_2),
% 0.20/0.47    inference(resolution,[],[f146,f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X1) | sQ2_eqProxy(X0,sK0)) ) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f145])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    spl3_2 <=> ! [X1,X0] : (sQ2_eqProxy(X0,sK0) | ~r1_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    spl3_1),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f156])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    $false | spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f155,f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    v1_relat_1(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    ~v1_relat_1(sK1) | spl3_1),
% 0.20/0.47    inference(subsumption_resolution,[],[f151,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    sQ2_eqProxy(k1_xboole_0,k10_relat_1(sK1,sK0))),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f23,f32])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    k1_xboole_0 = k10_relat_1(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    ~sQ2_eqProxy(k1_xboole_0,k10_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | spl3_1),
% 0.20/0.47    inference(resolution,[],[f149,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(k2_relat_1(X1),X0) | ~sQ2_eqProxy(k1_xboole_0,k10_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f28,f32])).
% 0.20/0.47  % (7245)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ( ! [X0,X1] : (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0,X1] : (((k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0)) & (r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 != k10_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(nnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    ~r1_xboole_0(k2_relat_1(sK1),sK0) | spl3_1),
% 0.20/0.47    inference(resolution,[],[f143,f30])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    ~r1_xboole_0(sK0,k2_relat_1(sK1)) | spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f141])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    spl3_1 <=> r1_xboole_0(sK0,k2_relat_1(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    ~spl3_1 | spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f125,f145,f141])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ( ! [X0,X1] : (sQ2_eqProxy(X0,sK0) | ~r1_xboole_0(sK0,k2_relat_1(sK1)) | ~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.47    inference(resolution,[],[f100,f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    r1_tarski(sK0,k2_relat_1(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    ( ! [X6,X8,X7,X5] : (~r1_tarski(X5,X6) | sQ2_eqProxy(X7,X5) | ~r1_xboole_0(X5,X6) | ~r1_tarski(X7,X8) | ~r1_xboole_0(X7,X8)) )),
% 0.20/0.47    inference(resolution,[],[f52,f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_xboole_0(X1) | ~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.20/0.47    inference(flattening,[],[f12])).
% 0.20/0.47  fof(f12,plain,(
% 0.20/0.47    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X4,X5,X3] : (~v1_xboole_0(X5) | ~r1_xboole_0(X3,X4) | sQ2_eqProxy(X5,X3) | ~r1_tarski(X3,X4)) )),
% 0.20/0.47    inference(resolution,[],[f27,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_xboole_0(X1) | sQ2_eqProxy(X0,X1) | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(equality_proxy_replacement,[],[f31,f32])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (7236)------------------------------
% 0.20/0.47  % (7236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (7236)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (7236)Memory used [KB]: 6140
% 0.20/0.47  % (7236)Time elapsed: 0.059 s
% 0.20/0.47  % (7236)------------------------------
% 0.20/0.47  % (7236)------------------------------
% 0.20/0.48  % (7230)Success in time 0.12 s
%------------------------------------------------------------------------------
