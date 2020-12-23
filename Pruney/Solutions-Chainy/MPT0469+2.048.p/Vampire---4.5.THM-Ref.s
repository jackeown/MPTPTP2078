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
% DateTime   : Thu Dec  3 12:47:40 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 109 expanded)
%              Number of leaves         :   13 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :  149 ( 225 expanded)
%              Number of equality atoms :   25 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f238,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f69,f84,f115,f225,f227,f237])).

fof(f237,plain,(
    ~ spl5_8 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f232,f22])).

fof(f22,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f232,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0)
    | ~ spl5_8 ),
    inference(resolution,[],[f102,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k1_enumset1(X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f25,f30])).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f102,plain,
    ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl5_8
  <=> r2_hidden(sK0(k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f227,plain,
    ( spl5_6
    | spl5_8
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f226,f96,f35,f100,f93])).

fof(f93,plain,
    ( spl5_6
  <=> ! [X6] : ~ r2_hidden(X6,k1_relat_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f35,plain,
    ( spl5_1
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f96,plain,
    ( spl5_7
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f226,plain,
    ( ! [X0] :
        ( r2_hidden(sK0(k1_xboole_0),k1_xboole_0)
        | ~ r2_hidden(X0,k1_relat_1(k1_xboole_0)) )
    | ~ spl5_1
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f116,f36])).

fof(f36,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(k1_xboole_0))
        | r2_hidden(sK0(k1_xboole_0),k2_relat_1(k1_xboole_0)) )
    | ~ spl5_7 ),
    inference(resolution,[],[f97,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | r2_hidden(sK0(X1),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

fof(f97,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f225,plain,
    ( ~ spl5_1
    | spl5_2
    | ~ spl5_6 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | ~ spl5_1
    | spl5_2
    | ~ spl5_6 ),
    inference(subsumption_resolution,[],[f214,f41])).

fof(f41,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl5_2
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f214,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl5_1
    | ~ spl5_6 ),
    inference(resolution,[],[f176,f94])).

fof(f94,plain,
    ( ! [X6] : ~ r2_hidden(X6,k1_relat_1(k1_xboole_0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f93])).

fof(f176,plain,
    ( ! [X4] :
        ( r2_hidden(sK2(k1_xboole_0,X4),X4)
        | k1_xboole_0 = X4 )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f174,f22])).

fof(f174,plain,
    ( ! [X4,X5] :
        ( k1_xboole_0 = X4
        | r2_hidden(sK2(k1_xboole_0,X4),X4)
        | ~ r1_xboole_0(k1_enumset1(k4_tarski(sK4(k1_xboole_0,X4),sK2(k1_xboole_0,X4)),k4_tarski(sK4(k1_xboole_0,X4),sK2(k1_xboole_0,X4)),X5),k1_xboole_0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f85,f31])).

fof(f85,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(sK4(k1_xboole_0,X0),sK2(k1_xboole_0,X0)),k1_xboole_0)
        | k1_xboole_0 = X0
        | r2_hidden(sK2(k1_xboole_0,X0),X0) )
    | ~ spl5_1 ),
    inference(superposition,[],[f36,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK4(X0,X1),sK2(X0,X1)),X0)
      | r2_hidden(sK2(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f115,plain,(
    spl5_7 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl5_7 ),
    inference(subsumption_resolution,[],[f110,f22])).

fof(f110,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_enumset1(sK1(k1_xboole_0),sK1(k1_xboole_0),X0),k1_xboole_0)
    | spl5_7 ),
    inference(resolution,[],[f104,f31])).

fof(f104,plain,
    ( r2_hidden(sK1(k1_xboole_0),k1_xboole_0)
    | spl5_7 ),
    inference(unit_resulting_resolution,[],[f98,f23])).

fof(f23,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ? [X1] :
          ( ! [X2,X3] : k4_tarski(X2,X3) != X1
          & r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) )
     => v1_relat_1(X0) ) ),
    inference(unused_predicate_definition_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f98,plain,
    ( ~ v1_relat_1(k1_xboole_0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f84,plain,(
    ~ spl5_3 ),
    inference(avatar_contradiction_clause,[],[f83])).

fof(f83,plain,
    ( $false
    | ~ spl5_3 ),
    inference(subsumption_resolution,[],[f79,f22])).

fof(f79,plain,
    ( ! [X1] : ~ r1_xboole_0(k1_enumset1(sK2(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0),X1),k1_xboole_0)
    | ~ spl5_3 ),
    inference(resolution,[],[f48,f31])).

fof(f48,plain,
    ( r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl5_3
  <=> r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f69,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f64,f22])).

fof(f64,plain,
    ( ! [X0] : ~ r1_xboole_0(k1_enumset1(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),X0),k1_xboole_0)
    | spl5_1
    | spl5_3 ),
    inference(resolution,[],[f55,f31])).

fof(f55,plain,
    ( r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | spl5_1
    | spl5_3 ),
    inference(subsumption_resolution,[],[f54,f49])).

fof(f49,plain,
    ( ~ r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f54,plain,
    ( r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0)
    | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)
    | spl5_1 ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,
    ( ! [X0] :
        ( k1_xboole_0 != X0
        | r2_hidden(k4_tarski(sK4(k1_xboole_0,X0),sK2(k1_xboole_0,X0)),k1_xboole_0)
        | r2_hidden(sK2(k1_xboole_0,X0),X0) )
    | spl5_1 ),
    inference(superposition,[],[f37,f28])).

fof(f37,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f42,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f20,f39,f35])).

fof(f20,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:52:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (21960)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (21960)Refutation not found, incomplete strategy% (21960)------------------------------
% 0.21/0.52  % (21960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (21960)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (21960)Memory used [KB]: 10618
% 0.21/0.52  % (21960)Time elapsed: 0.113 s
% 0.21/0.52  % (21960)------------------------------
% 0.21/0.52  % (21960)------------------------------
% 0.21/0.54  % (21954)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (21954)Refutation not found, incomplete strategy% (21954)------------------------------
% 0.21/0.54  % (21954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21954)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21954)Memory used [KB]: 6140
% 0.21/0.54  % (21954)Time elapsed: 0.124 s
% 0.21/0.54  % (21954)------------------------------
% 0.21/0.54  % (21954)------------------------------
% 0.21/0.55  % (21951)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (21968)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.41/0.56  % (21970)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.41/0.56  % (21952)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.41/0.57  % (21952)Refutation not found, incomplete strategy% (21952)------------------------------
% 1.41/0.57  % (21952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.57  % (21975)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.41/0.57  % (21953)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.41/0.57  % (21959)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.41/0.57  % (21952)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.57  
% 1.41/0.57  % (21952)Memory used [KB]: 10618
% 1.41/0.57  % (21952)Time elapsed: 0.139 s
% 1.41/0.57  % (21952)------------------------------
% 1.41/0.57  % (21952)------------------------------
% 1.41/0.57  % (21967)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.41/0.57  % (21956)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.41/0.57  % (21962)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.66/0.58  % (21970)Refutation not found, incomplete strategy% (21970)------------------------------
% 1.66/0.58  % (21970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (21970)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.58  
% 1.66/0.58  % (21970)Memory used [KB]: 10618
% 1.66/0.58  % (21970)Time elapsed: 0.146 s
% 1.66/0.58  % (21970)------------------------------
% 1.66/0.58  % (21970)------------------------------
% 1.66/0.58  % (21975)Refutation not found, incomplete strategy% (21975)------------------------------
% 1.66/0.58  % (21975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (21975)Termination reason: Refutation not found, incomplete strategy
% 1.66/0.58  
% 1.66/0.58  % (21975)Memory used [KB]: 6140
% 1.66/0.58  % (21975)Time elapsed: 0.147 s
% 1.66/0.58  % (21975)------------------------------
% 1.66/0.58  % (21975)------------------------------
% 1.66/0.58  % (21959)Refutation found. Thanks to Tanya!
% 1.66/0.58  % SZS status Theorem for theBenchmark
% 1.66/0.58  % SZS output start Proof for theBenchmark
% 1.66/0.58  fof(f238,plain,(
% 1.66/0.58    $false),
% 1.66/0.58    inference(avatar_sat_refutation,[],[f42,f69,f84,f115,f225,f227,f237])).
% 1.66/0.58  fof(f237,plain,(
% 1.66/0.58    ~spl5_8),
% 1.66/0.58    inference(avatar_contradiction_clause,[],[f236])).
% 1.66/0.58  fof(f236,plain,(
% 1.66/0.58    $false | ~spl5_8),
% 1.66/0.58    inference(subsumption_resolution,[],[f232,f22])).
% 1.66/0.58  fof(f22,plain,(
% 1.66/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f1])).
% 1.66/0.58  fof(f1,axiom,(
% 1.66/0.58    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.66/0.58  fof(f232,plain,(
% 1.66/0.58    ( ! [X0] : (~r1_xboole_0(k1_enumset1(sK0(k1_xboole_0),sK0(k1_xboole_0),X0),k1_xboole_0)) ) | ~spl5_8),
% 1.66/0.58    inference(resolution,[],[f102,f31])).
% 1.66/0.58  fof(f31,plain,(
% 1.66/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(k1_enumset1(X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.66/0.58    inference(definition_unfolding,[],[f25,f30])).
% 1.66/0.58  fof(f30,plain,(
% 1.66/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f2])).
% 1.66/0.58  fof(f2,axiom,(
% 1.66/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.66/0.58  fof(f25,plain,(
% 1.66/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f19])).
% 1.66/0.58  fof(f19,plain,(
% 1.66/0.58    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.66/0.58    inference(ennf_transformation,[],[f8])).
% 1.66/0.58  fof(f8,axiom,(
% 1.66/0.58    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 1.66/0.58  fof(f102,plain,(
% 1.66/0.58    r2_hidden(sK0(k1_xboole_0),k1_xboole_0) | ~spl5_8),
% 1.66/0.58    inference(avatar_component_clause,[],[f100])).
% 1.66/0.58  fof(f100,plain,(
% 1.66/0.58    spl5_8 <=> r2_hidden(sK0(k1_xboole_0),k1_xboole_0)),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.66/0.58  fof(f227,plain,(
% 1.66/0.58    spl5_6 | spl5_8 | ~spl5_1 | ~spl5_7),
% 1.66/0.58    inference(avatar_split_clause,[],[f226,f96,f35,f100,f93])).
% 1.66/0.58  fof(f93,plain,(
% 1.66/0.58    spl5_6 <=> ! [X6] : ~r2_hidden(X6,k1_relat_1(k1_xboole_0))),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.66/0.58  fof(f35,plain,(
% 1.66/0.58    spl5_1 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.66/0.58  fof(f96,plain,(
% 1.66/0.58    spl5_7 <=> v1_relat_1(k1_xboole_0)),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.66/0.58  fof(f226,plain,(
% 1.66/0.58    ( ! [X0] : (r2_hidden(sK0(k1_xboole_0),k1_xboole_0) | ~r2_hidden(X0,k1_relat_1(k1_xboole_0))) ) | (~spl5_1 | ~spl5_7)),
% 1.66/0.58    inference(forward_demodulation,[],[f116,f36])).
% 1.66/0.58  fof(f36,plain,(
% 1.66/0.58    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl5_1),
% 1.66/0.58    inference(avatar_component_clause,[],[f35])).
% 1.66/0.58  fof(f116,plain,(
% 1.66/0.58    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(k1_xboole_0)) | r2_hidden(sK0(k1_xboole_0),k2_relat_1(k1_xboole_0))) ) | ~spl5_7),
% 1.66/0.58    inference(resolution,[],[f97,f21])).
% 1.66/0.58  fof(f21,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r2_hidden(X0,k1_relat_1(X1)) | r2_hidden(sK0(X1),k2_relat_1(X1))) )),
% 1.66/0.58    inference(cnf_transformation,[],[f17])).
% 1.66/0.58  fof(f17,plain,(
% 1.66/0.58    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.66/0.58    inference(flattening,[],[f16])).
% 1.66/0.58  fof(f16,plain,(
% 1.66/0.58    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 1.66/0.58    inference(ennf_transformation,[],[f11])).
% 1.66/0.58  fof(f11,axiom,(
% 1.66/0.58    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).
% 1.66/0.58  fof(f97,plain,(
% 1.66/0.58    v1_relat_1(k1_xboole_0) | ~spl5_7),
% 1.66/0.58    inference(avatar_component_clause,[],[f96])).
% 1.66/0.58  fof(f225,plain,(
% 1.66/0.58    ~spl5_1 | spl5_2 | ~spl5_6),
% 1.66/0.58    inference(avatar_contradiction_clause,[],[f224])).
% 1.66/0.58  fof(f224,plain,(
% 1.66/0.58    $false | (~spl5_1 | spl5_2 | ~spl5_6)),
% 1.66/0.58    inference(subsumption_resolution,[],[f214,f41])).
% 1.66/0.58  fof(f41,plain,(
% 1.66/0.58    k1_xboole_0 != k1_relat_1(k1_xboole_0) | spl5_2),
% 1.66/0.58    inference(avatar_component_clause,[],[f39])).
% 1.66/0.58  fof(f39,plain,(
% 1.66/0.58    spl5_2 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.66/0.58  fof(f214,plain,(
% 1.66/0.58    k1_xboole_0 = k1_relat_1(k1_xboole_0) | (~spl5_1 | ~spl5_6)),
% 1.66/0.58    inference(resolution,[],[f176,f94])).
% 1.66/0.58  fof(f94,plain,(
% 1.66/0.58    ( ! [X6] : (~r2_hidden(X6,k1_relat_1(k1_xboole_0))) ) | ~spl5_6),
% 1.66/0.58    inference(avatar_component_clause,[],[f93])).
% 1.66/0.58  fof(f176,plain,(
% 1.66/0.58    ( ! [X4] : (r2_hidden(sK2(k1_xboole_0,X4),X4) | k1_xboole_0 = X4) ) | ~spl5_1),
% 1.66/0.58    inference(subsumption_resolution,[],[f174,f22])).
% 1.66/0.58  fof(f174,plain,(
% 1.66/0.58    ( ! [X4,X5] : (k1_xboole_0 = X4 | r2_hidden(sK2(k1_xboole_0,X4),X4) | ~r1_xboole_0(k1_enumset1(k4_tarski(sK4(k1_xboole_0,X4),sK2(k1_xboole_0,X4)),k4_tarski(sK4(k1_xboole_0,X4),sK2(k1_xboole_0,X4)),X5),k1_xboole_0)) ) | ~spl5_1),
% 1.66/0.58    inference(resolution,[],[f85,f31])).
% 1.66/0.58  fof(f85,plain,(
% 1.66/0.58    ( ! [X0] : (r2_hidden(k4_tarski(sK4(k1_xboole_0,X0),sK2(k1_xboole_0,X0)),k1_xboole_0) | k1_xboole_0 = X0 | r2_hidden(sK2(k1_xboole_0,X0),X0)) ) | ~spl5_1),
% 1.66/0.58    inference(superposition,[],[f36,f28])).
% 1.66/0.58  fof(f28,plain,(
% 1.66/0.58    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK4(X0,X1),sK2(X0,X1)),X0) | r2_hidden(sK2(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 1.66/0.58    inference(cnf_transformation,[],[f10])).
% 1.66/0.58  fof(f10,axiom,(
% 1.66/0.58    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 1.66/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 1.66/0.59  fof(f115,plain,(
% 1.66/0.59    spl5_7),
% 1.66/0.59    inference(avatar_contradiction_clause,[],[f114])).
% 1.66/0.59  fof(f114,plain,(
% 1.66/0.59    $false | spl5_7),
% 1.66/0.59    inference(subsumption_resolution,[],[f110,f22])).
% 1.66/0.59  fof(f110,plain,(
% 1.66/0.59    ( ! [X0] : (~r1_xboole_0(k1_enumset1(sK1(k1_xboole_0),sK1(k1_xboole_0),X0),k1_xboole_0)) ) | spl5_7),
% 1.66/0.59    inference(resolution,[],[f104,f31])).
% 1.66/0.59  fof(f104,plain,(
% 1.66/0.59    r2_hidden(sK1(k1_xboole_0),k1_xboole_0) | spl5_7),
% 1.66/0.59    inference(unit_resulting_resolution,[],[f98,f23])).
% 1.66/0.59  fof(f23,plain,(
% 1.66/0.59    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_relat_1(X0)) )),
% 1.66/0.59    inference(cnf_transformation,[],[f18])).
% 1.66/0.59  fof(f18,plain,(
% 1.66/0.59    ! [X0] : (v1_relat_1(X0) | ? [X1] : (! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.66/0.59    inference(ennf_transformation,[],[f14])).
% 1.66/0.59  fof(f14,plain,(
% 1.66/0.59    ! [X0] : (! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)) => v1_relat_1(X0))),
% 1.66/0.59    inference(unused_predicate_definition_removal,[],[f9])).
% 1.66/0.59  fof(f9,axiom,(
% 1.66/0.59    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 1.66/0.59  fof(f98,plain,(
% 1.66/0.59    ~v1_relat_1(k1_xboole_0) | spl5_7),
% 1.66/0.59    inference(avatar_component_clause,[],[f96])).
% 1.66/0.59  fof(f84,plain,(
% 1.66/0.59    ~spl5_3),
% 1.66/0.59    inference(avatar_contradiction_clause,[],[f83])).
% 1.66/0.59  fof(f83,plain,(
% 1.66/0.59    $false | ~spl5_3),
% 1.66/0.59    inference(subsumption_resolution,[],[f79,f22])).
% 1.66/0.59  fof(f79,plain,(
% 1.66/0.59    ( ! [X1] : (~r1_xboole_0(k1_enumset1(sK2(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0),X1),k1_xboole_0)) ) | ~spl5_3),
% 1.66/0.59    inference(resolution,[],[f48,f31])).
% 1.66/0.59  fof(f48,plain,(
% 1.66/0.59    r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) | ~spl5_3),
% 1.66/0.59    inference(avatar_component_clause,[],[f47])).
% 1.66/0.59  fof(f47,plain,(
% 1.66/0.59    spl5_3 <=> r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0)),
% 1.66/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.66/0.59  fof(f69,plain,(
% 1.66/0.59    spl5_1 | spl5_3),
% 1.66/0.59    inference(avatar_contradiction_clause,[],[f68])).
% 1.66/0.59  fof(f68,plain,(
% 1.66/0.59    $false | (spl5_1 | spl5_3)),
% 1.66/0.59    inference(subsumption_resolution,[],[f64,f22])).
% 1.66/0.59  fof(f64,plain,(
% 1.66/0.59    ( ! [X0] : (~r1_xboole_0(k1_enumset1(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),X0),k1_xboole_0)) ) | (spl5_1 | spl5_3)),
% 1.66/0.59    inference(resolution,[],[f55,f31])).
% 1.66/0.59  fof(f55,plain,(
% 1.66/0.59    r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | (spl5_1 | spl5_3)),
% 1.66/0.59    inference(subsumption_resolution,[],[f54,f49])).
% 1.66/0.59  fof(f49,plain,(
% 1.66/0.59    ~r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl5_3),
% 1.66/0.59    inference(avatar_component_clause,[],[f47])).
% 1.66/0.59  fof(f54,plain,(
% 1.66/0.59    r2_hidden(k4_tarski(sK4(k1_xboole_0,k1_xboole_0),sK2(k1_xboole_0,k1_xboole_0)),k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,k1_xboole_0),k1_xboole_0) | spl5_1),
% 1.66/0.59    inference(equality_resolution,[],[f43])).
% 1.66/0.59  fof(f43,plain,(
% 1.66/0.59    ( ! [X0] : (k1_xboole_0 != X0 | r2_hidden(k4_tarski(sK4(k1_xboole_0,X0),sK2(k1_xboole_0,X0)),k1_xboole_0) | r2_hidden(sK2(k1_xboole_0,X0),X0)) ) | spl5_1),
% 1.66/0.59    inference(superposition,[],[f37,f28])).
% 1.66/0.59  fof(f37,plain,(
% 1.66/0.59    k1_xboole_0 != k2_relat_1(k1_xboole_0) | spl5_1),
% 1.66/0.59    inference(avatar_component_clause,[],[f35])).
% 1.66/0.59  fof(f42,plain,(
% 1.66/0.59    ~spl5_1 | ~spl5_2),
% 1.66/0.59    inference(avatar_split_clause,[],[f20,f39,f35])).
% 1.66/0.59  fof(f20,plain,(
% 1.66/0.59    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 1.66/0.59    inference(cnf_transformation,[],[f15])).
% 1.66/0.59  fof(f15,plain,(
% 1.66/0.59    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 1.66/0.59    inference(ennf_transformation,[],[f13])).
% 1.66/0.59  fof(f13,negated_conjecture,(
% 1.66/0.59    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 1.66/0.59    inference(negated_conjecture,[],[f12])).
% 1.66/0.59  fof(f12,conjecture,(
% 1.66/0.59    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.66/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.66/0.59  % SZS output end Proof for theBenchmark
% 1.66/0.59  % (21959)------------------------------
% 1.66/0.59  % (21959)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.59  % (21959)Termination reason: Refutation
% 1.66/0.59  
% 1.66/0.59  % (21959)Memory used [KB]: 10746
% 1.66/0.59  % (21959)Time elapsed: 0.161 s
% 1.66/0.59  % (21959)------------------------------
% 1.66/0.59  % (21959)------------------------------
% 1.66/0.59  % (21949)Success in time 0.222 s
%------------------------------------------------------------------------------
