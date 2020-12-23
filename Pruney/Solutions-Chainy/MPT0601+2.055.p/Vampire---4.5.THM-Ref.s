%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 109 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   12
%              Number of atoms          :  194 ( 377 expanded)
%              Number of equality atoms :   29 (  79 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f204,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f133,f136,f203])).

fof(f203,plain,
    ( ~ spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f200])).

fof(f200,plain,
    ( $false
    | ~ spl7_1
    | ~ spl7_2 ),
    inference(unit_resulting_resolution,[],[f141,f66,f28,f56,f176])).

fof(f176,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X2,X0)
      | ~ sQ6_eqProxy(X0,X1)
      | ~ sQ6_eqProxy(X2,k1_tarski(X3))
      | ~ r2_hidden(X3,X1) ) ),
    inference(resolution,[],[f54,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(X1,X3)
      | ~ sQ6_eqProxy(X2,X3)
      | ~ r1_xboole_0(X0,X2)
      | ~ sQ6_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f39])).

fof(f39,plain,(
    ! [X1,X0] :
      ( sQ6_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).

fof(f56,plain,(
    ! [X0] : sQ6_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f39])).

fof(f28,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f66,plain,
    ( sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl7_2
  <=> sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f141,plain,
    ( r2_hidden(sK5(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f139,f25])).

fof(f25,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
      | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
    & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
      | r2_hidden(sK0,k1_relat_1(sK1)) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( ( k1_xboole_0 = k11_relat_1(X1,X0)
          | ~ r2_hidden(X0,k1_relat_1(X1)) )
        & ( k1_xboole_0 != k11_relat_1(X1,X0)
          | r2_hidden(X0,k1_relat_1(X1)) )
        & v1_relat_1(X1) )
   => ( ( k1_xboole_0 = k11_relat_1(sK1,sK0)
        | ~ r2_hidden(sK0,k1_relat_1(sK1)) )
      & ( k1_xboole_0 != k11_relat_1(sK1,sK0)
        | r2_hidden(sK0,k1_relat_1(sK1)) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k11_relat_1(X1,X0)
        | ~ r2_hidden(X0,k1_relat_1(X1)) )
      & ( k1_xboole_0 != k11_relat_1(X1,X0)
        | r2_hidden(X0,k1_relat_1(X1)) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,k1_relat_1(X1))
      <~> k1_xboole_0 != k11_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r2_hidden(X0,k1_relat_1(X1))
        <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,k1_relat_1(X1))
      <=> k1_xboole_0 != k11_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).

fof(f139,plain,
    ( r2_hidden(sK5(sK1,sK0),k11_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f138,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | r2_hidden(X1,k11_relat_1(X2,X0))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | ~ r2_hidden(X1,k11_relat_1(X2,X0)) )
        & ( r2_hidden(X1,k11_relat_1(X2,X0))
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> r2_hidden(X1,k11_relat_1(X2,X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).

fof(f138,plain,
    ( r2_hidden(k4_tarski(sK0,sK5(sK1,sK0)),sK1)
    | ~ spl7_1 ),
    inference(resolution,[],[f61,f38])).

fof(f38,plain,(
    ! [X0,X5] :
      ( ~ r2_hidden(X5,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
      | ~ r2_hidden(X5,X1)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
            | ~ r2_hidden(sK3(X0,X1),X1) )
          & ( r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
            | r2_hidden(sK3(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f22,f21,f20])).

fof(f20,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] : ~ r2_hidden(k4_tarski(sK3(X0,X1),X3),X0)
          | ~ r2_hidden(sK3(X0,X1),X1) )
        & ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
          | r2_hidden(sK3(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0)
     => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X5,X0] :
      ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
     => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] : r2_hidden(k4_tarski(X2,X4),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] : ~ r2_hidden(k4_tarski(X5,X6),X0) )
            & ( ? [X7] : r2_hidden(k4_tarski(X5,X7),X0)
              | ~ r2_hidden(X5,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_relat_1(X0) = X1
        | ? [X2] :
            ( ( ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] : ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X2,X1) ) )
        | k1_relat_1(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

fof(f61,plain,
    ( r2_hidden(sK0,k1_relat_1(sK1))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl7_1
  <=> r2_hidden(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f136,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f134,f66])).

fof(f134,plain,
    ( ~ sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | spl7_1 ),
    inference(subsumption_resolution,[],[f41,f62])).

fof(f62,plain,
    ( ~ r2_hidden(sK0,k1_relat_1(sK1))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f41,plain,
    ( ~ sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(equality_proxy_replacement,[],[f26,f39])).

fof(f26,plain,
    ( k1_xboole_0 != k11_relat_1(sK1,sK0)
    | r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f133,plain,
    ( spl7_1
    | spl7_2 ),
    inference(avatar_contradiction_clause,[],[f132])).

fof(f132,plain,
    ( $false
    | spl7_1
    | spl7_2 ),
    inference(subsumption_resolution,[],[f129,f65])).

fof(f65,plain,
    ( ~ sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f129,plain,
    ( sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | spl7_1 ),
    inference(resolution,[],[f124,f62])).

fof(f124,plain,(
    ! [X1] :
      ( r2_hidden(X1,k1_relat_1(sK1))
      | sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,X1)) ) ),
    inference(resolution,[],[f121,f37])).

fof(f37,plain,(
    ! [X6,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X5,X6),X0)
      | r2_hidden(X5,k1_relat_1(X0)) ) ),
    inference(equality_resolution,[],[f31])).

fof(f31,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | ~ r2_hidden(k4_tarski(X5,X6),X0)
      | k1_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f121,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,sK2(k11_relat_1(sK1,X0))),sK1)
      | sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,X0)) ) ),
    inference(resolution,[],[f87,f25])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(k4_tarski(X0,sK2(k11_relat_1(X1,X0))),X1)
      | sQ6_eqProxy(k1_xboole_0,k11_relat_1(X1,X0)) ) ),
    inference(resolution,[],[f36,f42])).

fof(f42,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | sQ6_eqProxy(k1_xboole_0,X0) ) ),
    inference(equality_proxy_replacement,[],[f29,f39])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f16])).

fof(f16,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k11_relat_1(X2,X0))
      | r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f67,plain,
    ( ~ spl7_1
    | spl7_2 ),
    inference(avatar_split_clause,[],[f40,f64,f60])).

fof(f40,plain,
    ( sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(equality_proxy_replacement,[],[f27,f39])).

fof(f27,plain,
    ( k1_xboole_0 = k11_relat_1(sK1,sK0)
    | ~ r2_hidden(sK0,k1_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:55:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (26195)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.43  % (26184)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.43  % (26184)Refutation not found, incomplete strategy% (26184)------------------------------
% 0.20/0.43  % (26184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (26184)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.43  
% 0.20/0.43  % (26184)Memory used [KB]: 10618
% 0.20/0.43  % (26184)Time elapsed: 0.039 s
% 0.20/0.43  % (26184)------------------------------
% 0.20/0.43  % (26184)------------------------------
% 0.20/0.46  % (26186)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.46  % (26186)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f204,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f67,f133,f136,f203])).
% 0.20/0.46  fof(f203,plain,(
% 0.20/0.46    ~spl7_1 | ~spl7_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f200])).
% 0.20/0.46  fof(f200,plain,(
% 0.20/0.46    $false | (~spl7_1 | ~spl7_2)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f141,f66,f28,f56,f176])).
% 0.20/0.46  fof(f176,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X2,X0) | ~sQ6_eqProxy(X0,X1) | ~sQ6_eqProxy(X2,k1_tarski(X3)) | ~r2_hidden(X3,X1)) )),
% 0.20/0.46    inference(resolution,[],[f54,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X2,X0,X3,X1] : (r1_xboole_0(X1,X3) | ~sQ6_eqProxy(X2,X3) | ~r1_xboole_0(X0,X2) | ~sQ6_eqProxy(X0,X1)) )),
% 0.20/0.46    inference(equality_proxy_axiom,[],[f39])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    ! [X1,X0] : (sQ6_eqProxy(X0,X1) <=> X0 = X1)),
% 0.20/0.46    introduced(equality_proxy_definition,[new_symbols(naming,[sQ6_eqProxy])])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    ( ! [X0] : (sQ6_eqProxy(X0,X0)) )),
% 0.20/0.46    inference(equality_proxy_axiom,[],[f39])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.20/0.46  fof(f66,plain,(
% 0.20/0.46    sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | ~spl7_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f64])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    spl7_2 <=> sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.46  fof(f141,plain,(
% 0.20/0.46    r2_hidden(sK5(sK1,sK0),k11_relat_1(sK1,sK0)) | ~spl7_1),
% 0.20/0.46    inference(subsumption_resolution,[],[f139,f25])).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    v1_relat_1(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    (k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1)) => ((k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))) & (k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))) & v1_relat_1(sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ? [X0,X1] : ((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1))) & v1_relat_1(X1))),
% 0.20/0.46    inference(flattening,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X0,X1] : (((k1_xboole_0 = k11_relat_1(X1,X0) | ~r2_hidden(X0,k1_relat_1(X1))) & (k1_xboole_0 != k11_relat_1(X1,X0) | r2_hidden(X0,k1_relat_1(X1)))) & v1_relat_1(X1))),
% 0.20/0.46    inference(nnf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1] : ((r2_hidden(X0,k1_relat_1(X1)) <~> k1_xboole_0 != k11_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.46    inference(negated_conjecture,[],[f6])).
% 0.20/0.46  fof(f6,conjecture,(
% 0.20/0.46    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,k1_relat_1(X1)) <=> k1_xboole_0 != k11_relat_1(X1,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t205_relat_1)).
% 0.20/0.46  fof(f139,plain,(
% 0.20/0.46    r2_hidden(sK5(sK1,sK0),k11_relat_1(sK1,sK0)) | ~v1_relat_1(sK1) | ~spl7_1),
% 0.20/0.46    inference(resolution,[],[f138,f35])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | r2_hidden(X1,k11_relat_1(X2,X0)) | ~v1_relat_1(X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | ~r2_hidden(X1,k11_relat_1(X2,X0))) & (r2_hidden(X1,k11_relat_1(X2,X0)) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_relat_1(X2))),
% 0.20/0.46    inference(nnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))) | ~v1_relat_1(X2))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) <=> r2_hidden(X1,k11_relat_1(X2,X0))))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t204_relat_1)).
% 0.20/0.46  fof(f138,plain,(
% 0.20/0.46    r2_hidden(k4_tarski(sK0,sK5(sK1,sK0)),sK1) | ~spl7_1),
% 0.20/0.46    inference(resolution,[],[f61,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0,X5] : (~r2_hidden(X5,k1_relat_1(X0)) | r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0)) )),
% 0.20/0.46    inference(equality_resolution,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ( ! [X0,X5,X1] : (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1) | k1_relat_1(X0) != X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r2_hidden(sK3(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f19,f22,f21,f20])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1))) => ((! [X3] : ~r2_hidden(k4_tarski(sK3(X0,X1),X3),X0) | ~r2_hidden(sK3(X0,X1),X1)) & (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) | r2_hidden(sK3(X0,X1),X1))))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ! [X1,X0] : (? [X4] : r2_hidden(k4_tarski(sK3(X0,X1),X4),X0) => r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X5,X0] : (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) => r2_hidden(k4_tarski(X5,sK5(X0,X5)),X0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X4] : r2_hidden(k4_tarski(X2,X4),X0) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : ~r2_hidden(k4_tarski(X5,X6),X0)) & (? [X7] : r2_hidden(k4_tarski(X5,X7),X0) | ~r2_hidden(X5,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.46    inference(rectify,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0,X1] : ((k1_relat_1(X0) = X1 | ? [X2] : ((! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : ~r2_hidden(k4_tarski(X2,X3),X0)) & (? [X3] : r2_hidden(k4_tarski(X2,X3),X0) | ~r2_hidden(X2,X1))) | k1_relat_1(X0) != X1))),
% 0.20/0.46    inference(nnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : (k1_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X2,X3),X0)))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    r2_hidden(sK0,k1_relat_1(sK1)) | ~spl7_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f60])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    spl7_1 <=> r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.46  fof(f136,plain,(
% 0.20/0.46    spl7_1 | ~spl7_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f135])).
% 0.20/0.46  fof(f135,plain,(
% 0.20/0.46    $false | (spl7_1 | ~spl7_2)),
% 0.20/0.46    inference(subsumption_resolution,[],[f134,f66])).
% 0.20/0.46  fof(f134,plain,(
% 0.20/0.46    ~sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | spl7_1),
% 0.20/0.46    inference(subsumption_resolution,[],[f41,f62])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    ~r2_hidden(sK0,k1_relat_1(sK1)) | spl7_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f60])).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    ~sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.46    inference(equality_proxy_replacement,[],[f26,f39])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    k1_xboole_0 != k11_relat_1(sK1,sK0) | r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  fof(f133,plain,(
% 0.20/0.46    spl7_1 | spl7_2),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f132])).
% 0.20/0.46  fof(f132,plain,(
% 0.20/0.46    $false | (spl7_1 | spl7_2)),
% 0.20/0.46    inference(subsumption_resolution,[],[f129,f65])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ~sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | spl7_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f64])).
% 0.20/0.46  fof(f129,plain,(
% 0.20/0.46    sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | spl7_1),
% 0.20/0.46    inference(resolution,[],[f124,f62])).
% 0.20/0.46  fof(f124,plain,(
% 0.20/0.46    ( ! [X1] : (r2_hidden(X1,k1_relat_1(sK1)) | sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,X1))) )),
% 0.20/0.46    inference(resolution,[],[f121,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X6,X0,X5] : (~r2_hidden(k4_tarski(X5,X6),X0) | r2_hidden(X5,k1_relat_1(X0))) )),
% 0.20/0.46    inference(equality_resolution,[],[f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X6),X0) | k1_relat_1(X0) != X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f23])).
% 0.20/0.46  fof(f121,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(k4_tarski(X0,sK2(k11_relat_1(sK1,X0))),sK1) | sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,X0))) )),
% 0.20/0.46    inference(resolution,[],[f87,f25])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(k4_tarski(X0,sK2(k11_relat_1(X1,X0))),X1) | sQ6_eqProxy(k1_xboole_0,k11_relat_1(X1,X0))) )),
% 0.20/0.46    inference(resolution,[],[f36,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(sK2(X0),X0) | sQ6_eqProxy(k1_xboole_0,X0)) )),
% 0.20/0.46    inference(equality_proxy_replacement,[],[f29,f39])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.20/0.46    inference(cnf_transformation,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f9,f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.20/0.46    inference(ennf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r2_hidden(X1,k11_relat_1(X2,X0)) | r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f24])).
% 0.20/0.46  fof(f67,plain,(
% 0.20/0.46    ~spl7_1 | spl7_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f40,f64,f60])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    sQ6_eqProxy(k1_xboole_0,k11_relat_1(sK1,sK0)) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.46    inference(equality_proxy_replacement,[],[f27,f39])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    k1_xboole_0 = k11_relat_1(sK1,sK0) | ~r2_hidden(sK0,k1_relat_1(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f15])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (26186)------------------------------
% 0.20/0.46  % (26186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (26186)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (26186)Memory used [KB]: 6140
% 0.20/0.46  % (26186)Time elapsed: 0.056 s
% 0.20/0.46  % (26186)------------------------------
% 0.20/0.46  % (26186)------------------------------
% 0.20/0.47  % (26177)Success in time 0.112 s
%------------------------------------------------------------------------------
