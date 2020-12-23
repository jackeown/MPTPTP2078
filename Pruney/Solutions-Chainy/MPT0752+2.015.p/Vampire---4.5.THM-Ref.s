%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 148 expanded)
%              Number of leaves         :   14 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :  189 ( 426 expanded)
%              Number of equality atoms :    8 (  32 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f429,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f111,f115,f140,f423,f428])).

fof(f428,plain,(
    spl4_4 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f49,f298,f425,f195])).

fof(f195,plain,(
    ! [X14,X13] :
      ( ~ sQ3_eqProxy(k8_relat_1(k1_xboole_0,X13),X14)
      | sQ3_eqProxy(k1_xboole_0,X14)
      | ~ v1_relat_1(X13) ) ),
    inference(resolution,[],[f94,f69])).

fof(f69,plain,(
    ! [X0] :
      ( sQ3_eqProxy(k1_xboole_0,k8_relat_1(k1_xboole_0,X0))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_proxy_replacement,[],[f47,f67])).

fof(f67,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f47,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k1_xboole_0 = k8_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ sQ3_eqProxy(X0,X1)
      | ~ sQ3_eqProxy(X1,X2)
      | sQ3_eqProxy(X0,X2) ) ),
    inference(equality_proxy_axiom,[],[f67])).

fof(f425,plain,
    ( ! [X0] : ~ sQ3_eqProxy(k1_xboole_0,sK1(X0))
    | spl4_4 ),
    inference(resolution,[],[f154,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(X1,X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f67])).

fof(f154,plain,
    ( ! [X0] : ~ sQ3_eqProxy(sK1(X0),k1_xboole_0)
    | spl4_4 ),
    inference(resolution,[],[f147,f52])).

fof(f52,plain,(
    ! [X0] : v5_ordinal1(sK1(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v5_ordinal1(sK1(X0))
      & v1_funct_1(sK1(X0))
      & v5_relat_1(sK1(X0),X0)
      & v1_relat_1(sK1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v5_ordinal1(X1)
          & v1_funct_1(X1)
          & v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
     => ( v5_ordinal1(sK1(X0))
        & v1_funct_1(sK1(X0))
        & v5_relat_1(sK1(X0),X0)
        & v1_relat_1(sK1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f13,axiom,(
    ! [X0] :
    ? [X1] :
      ( v5_ordinal1(X1)
      & v1_funct_1(X1)
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_ordinal1)).

fof(f147,plain,
    ( ! [X0] :
        ( ~ v5_ordinal1(X0)
        | ~ sQ3_eqProxy(X0,k1_xboole_0) )
    | spl4_4 ),
    inference(resolution,[],[f91,f110])).

fof(f110,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_4
  <=> v5_ordinal1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v5_ordinal1(X1)
      | ~ v5_ordinal1(X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f67])).

fof(f298,plain,(
    ! [X1] : sQ3_eqProxy(k8_relat_1(X1,sK1(X1)),sK1(X1)) ),
    inference(subsumption_resolution,[],[f292,f49])).

fof(f292,plain,(
    ! [X1] :
      ( ~ v1_relat_1(sK1(X1))
      | sQ3_eqProxy(k8_relat_1(X1,sK1(X1)),sK1(X1)) ) ),
    inference(resolution,[],[f202,f50])).

fof(f50,plain,(
    ! [X0] : v5_relat_1(sK1(X0),X0) ),
    inference(cnf_transformation,[],[f32])).

fof(f202,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | sQ3_eqProxy(k8_relat_1(X0,X1),X1) ) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X0,X1] :
      ( sQ3_eqProxy(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f71,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | sQ3_eqProxy(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(equality_proxy_replacement,[],[f56,f67])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

fof(f49,plain,(
    ! [X0] : v1_relat_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f423,plain,(
    spl4_3 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | spl4_3 ),
    inference(subsumption_resolution,[],[f421,f49])).

fof(f421,plain,
    ( ~ v1_relat_1(sK1(k1_xboole_0))
    | spl4_3 ),
    inference(subsumption_resolution,[],[f415,f145])).

fof(f145,plain,
    ( ! [X1] : ~ sQ3_eqProxy(k1_xboole_0,sK1(X1))
    | spl4_3 ),
    inference(resolution,[],[f143,f51])).

fof(f51,plain,(
    ! [X0] : v1_funct_1(sK1(X0)) ),
    inference(cnf_transformation,[],[f32])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ sQ3_eqProxy(k1_xboole_0,X0) )
    | spl4_3 ),
    inference(resolution,[],[f141,f93])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ sQ3_eqProxy(X0,k1_xboole_0)
        | ~ v1_funct_1(X0) )
    | spl4_3 ),
    inference(resolution,[],[f89,f106])).

fof(f106,plain,
    ( ~ v1_funct_1(k1_xboole_0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_3
  <=> v1_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f89,plain,(
    ! [X0,X1] :
      ( v1_funct_1(X1)
      | ~ v1_funct_1(X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f67])).

fof(f415,plain,
    ( sQ3_eqProxy(k1_xboole_0,sK1(k1_xboole_0))
    | ~ v1_relat_1(sK1(k1_xboole_0)) ),
    inference(resolution,[],[f298,f195])).

fof(f140,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f92,f49,f123,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f67])).

fof(f123,plain,
    ( ! [X1] : ~ v1_relat_1(X1)
    | spl4_1 ),
    inference(subsumption_resolution,[],[f120,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f120,plain,
    ( ! [X1] :
        ( ~ v1_relat_1(k8_relat_1(k1_xboole_0,X1))
        | ~ v1_relat_1(X1) )
    | spl4_1 ),
    inference(resolution,[],[f118,f69])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ sQ3_eqProxy(k1_xboole_0,X0)
        | ~ v1_relat_1(X0) )
    | spl4_1 ),
    inference(resolution,[],[f116,f93])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ sQ3_eqProxy(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | spl4_1 ),
    inference(resolution,[],[f85,f98])).

fof(f98,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl4_1
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f92,plain,(
    ! [X0] : sQ3_eqProxy(X0,X0) ),
    inference(equality_proxy_axiom,[],[f67])).

fof(f115,plain,(
    spl4_2 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f102,f53])).

fof(f53,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v5_relat_1(k1_xboole_0,X1)
      & v4_relat_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t206_relat_1)).

fof(f102,plain,
    ( ~ v5_relat_1(k1_xboole_0,sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl4_2
  <=> v5_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f111,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f40,f108,f104,f100,f96])).

fof(f40,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ v5_ordinal1(k1_xboole_0)
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v5_relat_1(k1_xboole_0,sK0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ~ v5_ordinal1(k1_xboole_0)
        | ~ v1_funct_1(k1_xboole_0)
        | ~ v5_relat_1(k1_xboole_0,X0)
        | ~ v1_relat_1(k1_xboole_0) )
   => ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,sK0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ~ v5_ordinal1(k1_xboole_0)
      | ~ v1_funct_1(k1_xboole_0)
      | ~ v5_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v5_ordinal1(k1_xboole_0)
        & v1_funct_1(k1_xboole_0)
        & v5_relat_1(k1_xboole_0,X0)
        & v1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v5_ordinal1(k1_xboole_0)
      & v1_funct_1(k1_xboole_0)
      & v5_relat_1(k1_xboole_0,X0)
      & v1_relat_1(k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:23:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (17439)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (17447)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (17444)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (17447)Refutation not found, incomplete strategy% (17447)------------------------------
% 0.21/0.47  % (17447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (17447)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (17447)Memory used [KB]: 1535
% 0.21/0.47  % (17447)Time elapsed: 0.040 s
% 0.21/0.47  % (17447)------------------------------
% 0.21/0.47  % (17447)------------------------------
% 0.21/0.47  % (17454)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (17444)Refutation not found, incomplete strategy% (17444)------------------------------
% 0.21/0.47  % (17444)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (17444)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (17444)Memory used [KB]: 6012
% 0.21/0.47  % (17444)Time elapsed: 0.053 s
% 0.21/0.47  % (17444)------------------------------
% 0.21/0.47  % (17444)------------------------------
% 0.21/0.47  % (17437)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (17446)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (17446)Refutation not found, incomplete strategy% (17446)------------------------------
% 0.21/0.48  % (17446)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17446)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (17446)Memory used [KB]: 6012
% 0.21/0.48  % (17446)Time elapsed: 0.002 s
% 0.21/0.48  % (17446)------------------------------
% 0.21/0.48  % (17446)------------------------------
% 0.21/0.48  % (17437)Refutation not found, incomplete strategy% (17437)------------------------------
% 0.21/0.48  % (17437)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17437)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (17437)Memory used [KB]: 10618
% 0.21/0.48  % (17437)Time elapsed: 0.064 s
% 0.21/0.48  % (17437)------------------------------
% 0.21/0.48  % (17437)------------------------------
% 0.21/0.48  % (17448)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (17435)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (17439)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f429,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f111,f115,f140,f423,f428])).
% 0.21/0.48  fof(f428,plain,(
% 0.21/0.48    spl4_4),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f426])).
% 0.21/0.48  fof(f426,plain,(
% 0.21/0.48    $false | spl4_4),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f49,f298,f425,f195])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    ( ! [X14,X13] : (~sQ3_eqProxy(k8_relat_1(k1_xboole_0,X13),X14) | sQ3_eqProxy(k1_xboole_0,X14) | ~v1_relat_1(X13)) )),
% 0.21/0.48    inference(resolution,[],[f94,f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X0] : (sQ3_eqProxy(k1_xboole_0,k8_relat_1(k1_xboole_0,X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f47,f67])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.48    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = k8_relat_1(k1_xboole_0,X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k8_relat_1(k1_xboole_0,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_relat_1)).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~sQ3_eqProxy(X0,X1) | ~sQ3_eqProxy(X1,X2) | sQ3_eqProxy(X0,X2)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f67])).
% 0.21/0.48  fof(f425,plain,(
% 0.21/0.48    ( ! [X0] : (~sQ3_eqProxy(k1_xboole_0,sK1(X0))) ) | spl4_4),
% 0.21/0.48    inference(resolution,[],[f154,f93])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ3_eqProxy(X1,X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f67])).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    ( ! [X0] : (~sQ3_eqProxy(sK1(X0),k1_xboole_0)) ) | spl4_4),
% 0.21/0.48    inference(resolution,[],[f147,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (v5_ordinal1(sK1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0] : (v5_ordinal1(sK1(X0)) & v1_funct_1(sK1(X0)) & v5_relat_1(sK1(X0),X0) & v1_relat_1(sK1(X0)))),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f13,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0] : (? [X1] : (v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v5_ordinal1(sK1(X0)) & v1_funct_1(sK1(X0)) & v5_relat_1(sK1(X0),X0) & v1_relat_1(sK1(X0))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : ? [X1] : (v5_ordinal1(X1) & v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_ordinal1)).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ( ! [X0] : (~v5_ordinal1(X0) | ~sQ3_eqProxy(X0,k1_xboole_0)) ) | spl4_4),
% 0.21/0.48    inference(resolution,[],[f91,f110])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ~v5_ordinal1(k1_xboole_0) | spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl4_4 <=> v5_ordinal1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v5_ordinal1(X1) | ~v5_ordinal1(X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f67])).
% 0.21/0.48  fof(f298,plain,(
% 0.21/0.48    ( ! [X1] : (sQ3_eqProxy(k8_relat_1(X1,sK1(X1)),sK1(X1))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f292,f49])).
% 0.21/0.48  fof(f292,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_relat_1(sK1(X1)) | sQ3_eqProxy(k8_relat_1(X1,sK1(X1)),sK1(X1))) )),
% 0.21/0.48    inference(resolution,[],[f202,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (v5_relat_1(sK1(X0),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | ~v1_relat_1(X1) | sQ3_eqProxy(k8_relat_1(X0,X1),X1)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f201])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    ( ! [X0,X1] : (sQ3_eqProxy(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(resolution,[],[f71,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(nnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | sQ3_eqProxy(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(equality_proxy_replacement,[],[f56,f67])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(sK1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f423,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f422])).
% 0.21/0.48  fof(f422,plain,(
% 0.21/0.48    $false | spl4_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f421,f49])).
% 0.21/0.48  fof(f421,plain,(
% 0.21/0.48    ~v1_relat_1(sK1(k1_xboole_0)) | spl4_3),
% 0.21/0.48    inference(subsumption_resolution,[],[f415,f145])).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    ( ! [X1] : (~sQ3_eqProxy(k1_xboole_0,sK1(X1))) ) | spl4_3),
% 0.21/0.48    inference(resolution,[],[f143,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(sK1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_1(X0) | ~sQ3_eqProxy(k1_xboole_0,X0)) ) | spl4_3),
% 0.21/0.48    inference(resolution,[],[f141,f93])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    ( ! [X0] : (~sQ3_eqProxy(X0,k1_xboole_0) | ~v1_funct_1(X0)) ) | spl4_3),
% 0.21/0.48    inference(resolution,[],[f89,f106])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ~v1_funct_1(k1_xboole_0) | spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    spl4_3 <=> v1_funct_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_funct_1(X1) | ~v1_funct_1(X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f67])).
% 0.21/0.48  fof(f415,plain,(
% 0.21/0.48    sQ3_eqProxy(k1_xboole_0,sK1(k1_xboole_0)) | ~v1_relat_1(sK1(k1_xboole_0))),
% 0.21/0.48    inference(resolution,[],[f298,f195])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    spl4_1),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    $false | spl4_1),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f92,f49,f123,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~v1_relat_1(X0) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f67])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_relat_1(X1)) ) | spl4_1),
% 0.21/0.48    inference(subsumption_resolution,[],[f120,f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ( ! [X1] : (~v1_relat_1(k8_relat_1(k1_xboole_0,X1)) | ~v1_relat_1(X1)) ) | spl4_1),
% 0.21/0.48    inference(resolution,[],[f118,f69])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ( ! [X0] : (~sQ3_eqProxy(k1_xboole_0,X0) | ~v1_relat_1(X0)) ) | spl4_1),
% 0.21/0.48    inference(resolution,[],[f116,f93])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X0] : (~sQ3_eqProxy(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | spl4_1),
% 0.21/0.48    inference(resolution,[],[f85,f98])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    ~v1_relat_1(k1_xboole_0) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl4_1 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ( ! [X0] : (sQ3_eqProxy(X0,X0)) )),
% 0.21/0.48    inference(equality_proxy_axiom,[],[f67])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    $false | spl4_2),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f102,f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X1] : (v5_relat_1(k1_xboole_0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X1] : v5_relat_1(k1_xboole_0,X1)),
% 0.21/0.48    inference(rectify,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : v5_relat_1(k1_xboole_0,X1)),
% 0.21/0.48    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : (v5_relat_1(k1_xboole_0,X1) & v4_relat_1(k1_xboole_0,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t206_relat_1)).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ~v5_relat_1(k1_xboole_0,sK0) | spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl4_2 <=> v5_relat_1(k1_xboole_0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f108,f104,f100,f96])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) => (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,sK0) | ~v1_relat_1(k1_xboole_0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0] : (~v5_ordinal1(k1_xboole_0) | ~v1_funct_1(k1_xboole_0) | ~v5_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.48    inference(negated_conjecture,[],[f14])).
% 0.21/0.48  fof(f14,conjecture,(
% 0.21/0.48    ! [X0] : (v5_ordinal1(k1_xboole_0) & v1_funct_1(k1_xboole_0) & v5_relat_1(k1_xboole_0,X0) & v1_relat_1(k1_xboole_0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_ordinal1)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (17439)------------------------------
% 0.21/0.48  % (17439)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (17439)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (17439)Memory used [KB]: 6524
% 0.21/0.48  % (17439)Time elapsed: 0.080 s
% 0.21/0.48  % (17439)------------------------------
% 0.21/0.48  % (17439)------------------------------
% 0.21/0.48  % (17433)Success in time 0.123 s
%------------------------------------------------------------------------------
