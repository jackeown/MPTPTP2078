%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:12 EST 2020

% Result     : Theorem 1.30s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 368 expanded)
%              Number of leaves         :   22 ( 115 expanded)
%              Depth                    :   18
%              Number of atoms          :  291 ( 769 expanded)
%              Number of equality atoms :   69 ( 321 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f273,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f45,f44,f46,f47,f272])).

fof(f272,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_relat_1(X1),k3_relat_1(X0))
      | ~ r1_tarski(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f271,f246])).

fof(f246,plain,(
    ! [X6,X7] :
      ( r1_tarski(k1_relat_1(X6),k3_relat_1(X7))
      | ~ v1_relat_1(X7)
      | ~ r1_tarski(X6,X7)
      | ~ v1_relat_1(X6) ) ),
    inference(duplicate_literal_removal,[],[f245])).

fof(f245,plain,(
    ! [X6,X7] :
      ( r1_tarski(k1_relat_1(X6),k3_relat_1(X7))
      | ~ v1_relat_1(X7)
      | ~ r1_tarski(X6,X7)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f220,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k1_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f220,plain,(
    ! [X19,X20] :
      ( ~ r1_tarski(X19,k1_relat_1(X20))
      | r1_tarski(X19,k3_relat_1(X20))
      | ~ v1_relat_1(X20) ) ),
    inference(resolution,[],[f207,f126])).

fof(f126,plain,(
    ! [X3] :
      ( r1_tarski(k1_relat_1(X3),k3_relat_1(X3))
      | ~ v1_relat_1(X3) ) ),
    inference(superposition,[],[f82,f81])).

fof(f81,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f48,f80])).

fof(f80,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f54,f78])).

fof(f78,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f55,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f75])).

fof(f75,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f71,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f72,f73])).

fof(f73,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f48,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f82,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f80])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f194,f88])).

fof(f88,plain,(
    ! [X2,X3,X1] : sP0(X1,X1,X2,X3) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2,X3)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( X0 != X1
          & X0 != X2
          & X0 != X3 ) )
      & ( X0 = X1
        | X0 = X2
        | X0 = X3
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X4,X2,X1,X0] :
      ( ( sP0(X4,X2,X1,X0)
        | ( X2 != X4
          & X1 != X4
          & X0 != X4 ) )
      & ( X2 = X4
        | X1 = X4
        | X0 = X4
        | ~ sP0(X4,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X1,X0] :
      ( sP0(X4,X2,X1,X0)
    <=> ( X2 = X4
        | X1 = X4
        | X0 = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

% (1716)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (1723)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (1722)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (1722)Refutation not found, incomplete strategy% (1722)------------------------------
% (1722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1722)Termination reason: Refutation not found, incomplete strategy

% (1722)Memory used [KB]: 10618
% (1722)Time elapsed: 0.140 s
% (1722)------------------------------
% (1722)------------------------------
% (1724)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (1717)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (1712)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (1715)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (1726)Refutation not found, incomplete strategy% (1726)------------------------------
% (1726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1726)Termination reason: Refutation not found, incomplete strategy

% (1726)Memory used [KB]: 1791
% (1726)Time elapsed: 0.139 s
% (1726)------------------------------
% (1726)------------------------------
% (1715)Refutation not found, incomplete strategy% (1715)------------------------------
% (1715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1718)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (1733)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% (1725)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (1725)Refutation not found, incomplete strategy% (1725)------------------------------
% (1725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1725)Termination reason: Refutation not found, incomplete strategy

% (1725)Memory used [KB]: 10746
% (1725)Time elapsed: 0.137 s
% (1725)------------------------------
% (1725)------------------------------
% (1715)Termination reason: Refutation not found, incomplete strategy

% (1715)Memory used [KB]: 10618
% (1715)Time elapsed: 0.140 s
% (1715)------------------------------
% (1715)------------------------------
% (1716)Refutation not found, incomplete strategy% (1716)------------------------------
% (1716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1716)Termination reason: Refutation not found, incomplete strategy

% (1716)Memory used [KB]: 10618
% (1716)Time elapsed: 0.138 s
% (1716)------------------------------
% (1716)------------------------------
% (1732)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
fof(f194,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X3,X2,X2)
      | r1_tarski(X2,X1)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f97,f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(resolution,[],[f91,f62])).

fof(f62,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | ~ sP0(X5,X2,X1,X0)
      | r2_hidden(X5,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ~ sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
            | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
          & ( sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
            | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).

fof(f38,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ~ sP0(X4,X2,X1,X0)
            | ~ r2_hidden(X4,X3) )
          & ( sP0(X4,X2,X1,X0)
            | r2_hidden(X4,X3) ) )
     => ( ( ~ sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
          | ~ r2_hidden(sK4(X0,X1,X2,X3),X3) )
        & ( sP0(sK4(X0,X1,X2,X3),X2,X1,X0)
          | r2_hidden(sK4(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ~ sP0(X5,X2,X1,X0) )
            & ( sP0(X5,X2,X1,X0)
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ~ sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) )
            & ( sP0(X4,X2,X1,X0)
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ~ sP0(X4,X2,X1,X0) )
            & ( sP0(X4,X2,X1,X0)
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( sP1(X0,X1,X2,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> sP0(X4,X2,X1,X0) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f91,plain,(
    ! [X2,X0,X1] : sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f69,f77])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X0,X1,X2,X3) )
      & ( sP1(X0,X1,X2,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X0,X1,X2,X3) ) ),
    inference(definition_folding,[],[f29,f31,f30])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | ~ r1_tarski(X3,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f58,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f56,f79])).

fof(f79,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f53,f78])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k1_setfam_1(X1),X2)
      | ~ r1_tarski(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r2_hidden(X0,X1) )
     => r1_tarski(k1_setfam_1(X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).

fof(f271,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(k3_relat_1(X1),k3_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X1),k3_relat_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X1,X0)
      | ~ v1_relat_1(X1)
      | r1_tarski(k3_relat_1(X1),k3_relat_1(X0))
      | ~ r1_tarski(k1_relat_1(X1),k3_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f250,f125])).

fof(f125,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X2)
      | r1_tarski(k3_relat_1(X1),X2)
      | ~ r1_tarski(k1_relat_1(X1),X2)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f85,f81])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f80])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f250,plain,(
    ! [X6,X7] :
      ( r1_tarski(k2_relat_1(X6),k3_relat_1(X7))
      | ~ v1_relat_1(X7)
      | ~ r1_tarski(X6,X7)
      | ~ v1_relat_1(X6) ) ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,(
    ! [X6,X7] :
      ( r1_tarski(k2_relat_1(X6),k3_relat_1(X7))
      | ~ v1_relat_1(X7)
      | ~ r1_tarski(X6,X7)
      | ~ v1_relat_1(X7)
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f222,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f222,plain,(
    ! [X24,X25] :
      ( ~ r1_tarski(X24,k2_relat_1(X25))
      | r1_tarski(X24,k3_relat_1(X25))
      | ~ v1_relat_1(X25) ) ),
    inference(resolution,[],[f207,f124])).

fof(f124,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(X0),k3_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f108,f81])).

fof(f108,plain,(
    ! [X6,X5] : r1_tarski(X5,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X5))) ),
    inference(superposition,[],[f82,f83])).

fof(f83,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f52,f78,f78])).

fof(f52,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f47,plain,(
    ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
    & r1_tarski(sK2,sK3)
    & v1_relat_1(sK3)
    & v1_relat_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
            & r1_tarski(X0,X1)
            & v1_relat_1(X1) )
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(X1))
          & r1_tarski(sK2,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(X1))
        & r1_tarski(sK2,X1)
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))
      & r1_tarski(sK2,sK3)
      & v1_relat_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(k3_relat_1(X0),k3_relat_1(X1))
          & r1_tarski(X0,X1)
          & v1_relat_1(X1) )
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => ! [X1] :
            ( v1_relat_1(X1)
           => ( r1_tarski(X0,X1)
             => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).

fof(f46,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f44,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f45,plain,(
    v1_relat_1(sK3) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:54:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (1728)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.50  % (1720)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.50  % (1711)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (1703)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (1713)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (1704)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (1714)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (1713)Refutation not found, incomplete strategy% (1713)------------------------------
% 0.21/0.51  % (1713)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (1710)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (1721)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.51  % (1713)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (1713)Memory used [KB]: 10874
% 0.21/0.51  % (1713)Time elapsed: 0.097 s
% 0.21/0.51  % (1713)------------------------------
% 0.21/0.51  % (1713)------------------------------
% 0.21/0.52  % (1726)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.30/0.52  % (1709)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.30/0.52  % (1707)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.30/0.52  % (1706)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.30/0.53  % (1719)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.30/0.53  % (1706)Refutation not found, incomplete strategy% (1706)------------------------------
% 1.30/0.53  % (1706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (1706)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (1706)Memory used [KB]: 10874
% 1.30/0.53  % (1706)Time elapsed: 0.116 s
% 1.30/0.53  % (1706)------------------------------
% 1.30/0.53  % (1706)------------------------------
% 1.30/0.53  % (1734)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.30/0.53  % (1727)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.30/0.53  % (1727)Refutation not found, incomplete strategy% (1727)------------------------------
% 1.30/0.53  % (1727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.53  % (1727)Termination reason: Refutation not found, incomplete strategy
% 1.30/0.53  
% 1.30/0.53  % (1727)Memory used [KB]: 10746
% 1.30/0.53  % (1727)Time elapsed: 0.129 s
% 1.30/0.53  % (1727)------------------------------
% 1.30/0.53  % (1727)------------------------------
% 1.30/0.53  % (1730)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.30/0.53  % (1729)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.30/0.53  % (1731)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.30/0.54  % (1734)Refutation found. Thanks to Tanya!
% 1.30/0.54  % SZS status Theorem for theBenchmark
% 1.30/0.54  % SZS output start Proof for theBenchmark
% 1.30/0.54  fof(f273,plain,(
% 1.30/0.54    $false),
% 1.30/0.54    inference(unit_resulting_resolution,[],[f45,f44,f46,f47,f272])).
% 1.30/0.54  fof(f272,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_tarski(k3_relat_1(X1),k3_relat_1(X0)) | ~r1_tarski(X1,X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(subsumption_resolution,[],[f271,f246])).
% 1.30/0.54  fof(f246,plain,(
% 1.30/0.54    ( ! [X6,X7] : (r1_tarski(k1_relat_1(X6),k3_relat_1(X7)) | ~v1_relat_1(X7) | ~r1_tarski(X6,X7) | ~v1_relat_1(X6)) )),
% 1.30/0.54    inference(duplicate_literal_removal,[],[f245])).
% 1.30/0.54  fof(f245,plain,(
% 1.30/0.54    ( ! [X6,X7] : (r1_tarski(k1_relat_1(X6),k3_relat_1(X7)) | ~v1_relat_1(X7) | ~r1_tarski(X6,X7) | ~v1_relat_1(X7) | ~v1_relat_1(X6)) )),
% 1.30/0.54    inference(resolution,[],[f220,f49])).
% 1.30/0.54  fof(f49,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f23])).
% 1.30/0.54  fof(f23,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(flattening,[],[f22])).
% 1.30/0.54  fof(f22,plain,(
% 1.30/0.54    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f16])).
% 1.30/0.54  fof(f16,axiom,(
% 1.30/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 1.30/0.54  fof(f220,plain,(
% 1.30/0.54    ( ! [X19,X20] : (~r1_tarski(X19,k1_relat_1(X20)) | r1_tarski(X19,k3_relat_1(X20)) | ~v1_relat_1(X20)) )),
% 1.30/0.54    inference(resolution,[],[f207,f126])).
% 1.30/0.54  fof(f126,plain,(
% 1.30/0.54    ( ! [X3] : (r1_tarski(k1_relat_1(X3),k3_relat_1(X3)) | ~v1_relat_1(X3)) )),
% 1.30/0.54    inference(superposition,[],[f82,f81])).
% 1.30/0.54  fof(f81,plain,(
% 1.30/0.54    ( ! [X0] : (k3_relat_1(X0) = k3_tarski(k6_enumset1(k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f48,f80])).
% 1.30/0.54  fof(f80,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.30/0.54    inference(definition_unfolding,[],[f54,f78])).
% 1.30/0.54  fof(f78,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f55,f77])).
% 1.30/0.54  fof(f77,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f57,f76])).
% 1.30/0.54  fof(f76,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f60,f75])).
% 1.30/0.54  fof(f75,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f71,f74])).
% 1.30/0.54  fof(f74,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.30/0.54    inference(definition_unfolding,[],[f72,f73])).
% 1.30/0.54  fof(f73,plain,(
% 1.30/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f11])).
% 1.30/0.54  fof(f11,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 1.30/0.54  fof(f72,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f10])).
% 1.30/0.54  fof(f10,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 1.30/0.54  fof(f71,plain,(
% 1.30/0.54    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f9])).
% 1.30/0.54  fof(f9,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.30/0.54  fof(f60,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f8])).
% 1.30/0.54  fof(f8,axiom,(
% 1.30/0.54    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.30/0.54  fof(f57,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f7])).
% 1.30/0.54  fof(f7,axiom,(
% 1.30/0.54    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.30/0.54  fof(f55,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f6])).
% 1.30/0.54  fof(f6,axiom,(
% 1.30/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.30/0.54  fof(f54,plain,(
% 1.30/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f12])).
% 1.30/0.54  fof(f12,axiom,(
% 1.30/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.30/0.54  fof(f48,plain,(
% 1.30/0.54    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.30/0.54    inference(cnf_transformation,[],[f21])).
% 1.30/0.54  fof(f21,plain,(
% 1.30/0.54    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 1.30/0.54    inference(ennf_transformation,[],[f15])).
% 1.30/0.54  fof(f15,axiom,(
% 1.30/0.54    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 1.30/0.54  fof(f82,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.30/0.54    inference(definition_unfolding,[],[f51,f80])).
% 1.30/0.54  fof(f51,plain,(
% 1.30/0.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.30/0.54    inference(cnf_transformation,[],[f2])).
% 1.30/0.54  fof(f2,axiom,(
% 1.30/0.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.30/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.30/0.54  fof(f207,plain,(
% 1.30/0.54    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 1.30/0.54    inference(resolution,[],[f194,f88])).
% 1.30/0.54  fof(f88,plain,(
% 1.30/0.54    ( ! [X2,X3,X1] : (sP0(X1,X1,X2,X3)) )),
% 1.30/0.54    inference(equality_resolution,[],[f68])).
% 1.30/0.54  fof(f68,plain,(
% 1.30/0.54    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2,X3) | X0 != X1) )),
% 1.30/0.54    inference(cnf_transformation,[],[f42])).
% 1.30/0.54  fof(f42,plain,(
% 1.30/0.54    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | (X0 != X1 & X0 != X2 & X0 != X3)) & (X0 = X1 | X0 = X2 | X0 = X3 | ~sP0(X0,X1,X2,X3)))),
% 1.30/0.54    inference(rectify,[],[f41])).
% 1.30/0.54  fof(f41,plain,(
% 1.30/0.54    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~sP0(X4,X2,X1,X0)))),
% 1.30/0.54    inference(flattening,[],[f40])).
% 1.30/0.54  fof(f40,plain,(
% 1.30/0.54    ! [X4,X2,X1,X0] : ((sP0(X4,X2,X1,X0) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~sP0(X4,X2,X1,X0)))),
% 1.30/0.54    inference(nnf_transformation,[],[f30])).
% 1.30/0.54  fof(f30,plain,(
% 1.30/0.54    ! [X4,X2,X1,X0] : (sP0(X4,X2,X1,X0) <=> (X2 = X4 | X1 = X4 | X0 = X4))),
% 1.30/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.30/0.54  % (1716)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.30/0.54  % (1723)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.30/0.54  % (1722)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.46/0.54  % (1722)Refutation not found, incomplete strategy% (1722)------------------------------
% 1.46/0.54  % (1722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (1722)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.54  
% 1.46/0.54  % (1722)Memory used [KB]: 10618
% 1.46/0.54  % (1722)Time elapsed: 0.140 s
% 1.46/0.54  % (1722)------------------------------
% 1.46/0.54  % (1722)------------------------------
% 1.46/0.54  % (1724)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.46/0.54  % (1717)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.46/0.54  % (1712)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.46/0.54  % (1715)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.46/0.54  % (1726)Refutation not found, incomplete strategy% (1726)------------------------------
% 1.46/0.54  % (1726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.54  % (1726)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.54  
% 1.46/0.54  % (1726)Memory used [KB]: 1791
% 1.46/0.54  % (1726)Time elapsed: 0.139 s
% 1.46/0.54  % (1726)------------------------------
% 1.46/0.54  % (1726)------------------------------
% 1.46/0.55  % (1715)Refutation not found, incomplete strategy% (1715)------------------------------
% 1.46/0.55  % (1715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (1718)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.46/0.55  % (1733)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.46/0.55  % (1725)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.46/0.55  % (1725)Refutation not found, incomplete strategy% (1725)------------------------------
% 1.46/0.55  % (1725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (1725)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (1725)Memory used [KB]: 10746
% 1.46/0.55  % (1725)Time elapsed: 0.137 s
% 1.46/0.55  % (1725)------------------------------
% 1.46/0.55  % (1725)------------------------------
% 1.46/0.55  % (1715)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (1715)Memory used [KB]: 10618
% 1.46/0.55  % (1715)Time elapsed: 0.140 s
% 1.46/0.55  % (1715)------------------------------
% 1.46/0.55  % (1715)------------------------------
% 1.46/0.55  % (1716)Refutation not found, incomplete strategy% (1716)------------------------------
% 1.46/0.55  % (1716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (1716)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (1716)Memory used [KB]: 10618
% 1.46/0.55  % (1716)Time elapsed: 0.138 s
% 1.46/0.55  % (1716)------------------------------
% 1.46/0.55  % (1716)------------------------------
% 1.46/0.56  % (1732)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.46/0.56  fof(f194,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (~sP0(X0,X3,X2,X2) | r1_tarski(X2,X1) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(resolution,[],[f97,f92])).
% 1.46/0.56  fof(f92,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k6_enumset1(X3,X3,X3,X3,X3,X3,X2,X1)) | ~sP0(X0,X1,X2,X3)) )),
% 1.46/0.56    inference(resolution,[],[f91,f62])).
% 1.46/0.56  fof(f62,plain,(
% 1.46/0.56    ( ! [X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3) | ~sP0(X5,X2,X1,X0) | r2_hidden(X5,X3)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f39])).
% 1.46/0.56  fof(f39,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ((~sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f37,f38])).
% 1.46/0.56  fof(f38,plain,(
% 1.46/0.56    ! [X3,X2,X1,X0] : (? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3))) => ((~sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | ~r2_hidden(sK4(X0,X1,X2,X3),X3)) & (sP0(sK4(X0,X1,X2,X3),X2,X1,X0) | r2_hidden(sK4(X0,X1,X2,X3),X3))))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f37,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | ~sP0(X5,X2,X1,X0)) & (sP0(X5,X2,X1,X0) | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.46/0.56    inference(rectify,[],[f36])).
% 1.46/0.56  fof(f36,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : ((~sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3)) & (sP0(X4,X2,X1,X0) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ~sP0(X4,X2,X1,X0)) & (sP0(X4,X2,X1,X0) | ~r2_hidden(X4,X3))) | ~sP1(X0,X1,X2,X3)))),
% 1.46/0.56    inference(nnf_transformation,[],[f31])).
% 1.46/0.56  fof(f31,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : (sP1(X0,X1,X2,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> sP0(X4,X2,X1,X0)))),
% 1.46/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.46/0.56  fof(f91,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (sP1(X0,X1,X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))) )),
% 1.46/0.56    inference(equality_resolution,[],[f87])).
% 1.46/0.56  fof(f87,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 1.46/0.56    inference(definition_unfolding,[],[f69,f77])).
% 1.46/0.56  fof(f69,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 1.46/0.56    inference(cnf_transformation,[],[f43])).
% 1.46/0.56  fof(f43,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X0,X1,X2,X3)) & (sP1(X0,X1,X2,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 1.46/0.56    inference(nnf_transformation,[],[f32])).
% 1.46/0.56  fof(f32,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X0,X1,X2,X3))),
% 1.46/0.56    inference(definition_folding,[],[f29,f31,f30])).
% 1.46/0.56  fof(f29,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 1.46/0.56    inference(ennf_transformation,[],[f5])).
% 1.46/0.56  fof(f5,axiom,(
% 1.46/0.56    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 1.46/0.56  fof(f97,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | ~r1_tarski(X3,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(superposition,[],[f58,f84])).
% 1.46/0.56  fof(f84,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(definition_unfolding,[],[f56,f79])).
% 1.46/0.56  fof(f79,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.46/0.56    inference(definition_unfolding,[],[f53,f78])).
% 1.46/0.56  fof(f53,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f13])).
% 1.46/0.56  fof(f13,axiom,(
% 1.46/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.46/0.56  fof(f56,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f24])).
% 1.46/0.56  fof(f24,plain,(
% 1.46/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.46/0.56    inference(ennf_transformation,[],[f1])).
% 1.46/0.56  fof(f1,axiom,(
% 1.46/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.46/0.56  fof(f58,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f26])).
% 1.46/0.56  fof(f26,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | ~r1_tarski(X0,X2) | ~r2_hidden(X0,X1))),
% 1.46/0.56    inference(flattening,[],[f25])).
% 1.46/0.56  fof(f25,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (r1_tarski(k1_setfam_1(X1),X2) | (~r1_tarski(X0,X2) | ~r2_hidden(X0,X1)))),
% 1.46/0.56    inference(ennf_transformation,[],[f14])).
% 1.46/0.56  fof(f14,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r2_hidden(X0,X1)) => r1_tarski(k1_setfam_1(X1),X2))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_setfam_1)).
% 1.46/0.56  fof(f271,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X0) | ~v1_relat_1(X1) | r1_tarski(k3_relat_1(X1),k3_relat_1(X0)) | ~r1_tarski(k1_relat_1(X1),k3_relat_1(X0))) )),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f268])).
% 1.46/0.56  fof(f268,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X1,X0) | ~v1_relat_1(X1) | r1_tarski(k3_relat_1(X1),k3_relat_1(X0)) | ~r1_tarski(k1_relat_1(X1),k3_relat_1(X0)) | ~v1_relat_1(X1)) )),
% 1.46/0.56    inference(resolution,[],[f250,f125])).
% 1.46/0.56  fof(f125,plain,(
% 1.46/0.56    ( ! [X2,X1] : (~r1_tarski(k2_relat_1(X1),X2) | r1_tarski(k3_relat_1(X1),X2) | ~r1_tarski(k1_relat_1(X1),X2) | ~v1_relat_1(X1)) )),
% 1.46/0.56    inference(superposition,[],[f85,f81])).
% 1.46/0.56  fof(f85,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(definition_unfolding,[],[f59,f80])).
% 1.46/0.56  fof(f59,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f28])).
% 1.46/0.56  fof(f28,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.46/0.56    inference(flattening,[],[f27])).
% 1.46/0.56  fof(f27,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.46/0.56    inference(ennf_transformation,[],[f3])).
% 1.46/0.56  fof(f3,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.46/0.56  fof(f250,plain,(
% 1.46/0.56    ( ! [X6,X7] : (r1_tarski(k2_relat_1(X6),k3_relat_1(X7)) | ~v1_relat_1(X7) | ~r1_tarski(X6,X7) | ~v1_relat_1(X6)) )),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f249])).
% 1.46/0.56  fof(f249,plain,(
% 1.46/0.56    ( ! [X6,X7] : (r1_tarski(k2_relat_1(X6),k3_relat_1(X7)) | ~v1_relat_1(X7) | ~r1_tarski(X6,X7) | ~v1_relat_1(X7) | ~v1_relat_1(X6)) )),
% 1.46/0.56    inference(resolution,[],[f222,f50])).
% 1.46/0.56  fof(f50,plain,(
% 1.46/0.56    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f23])).
% 1.46/0.56  fof(f222,plain,(
% 1.46/0.56    ( ! [X24,X25] : (~r1_tarski(X24,k2_relat_1(X25)) | r1_tarski(X24,k3_relat_1(X25)) | ~v1_relat_1(X25)) )),
% 1.46/0.56    inference(resolution,[],[f207,f124])).
% 1.46/0.56  fof(f124,plain,(
% 1.46/0.56    ( ! [X0] : (r1_tarski(k2_relat_1(X0),k3_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(superposition,[],[f108,f81])).
% 1.46/0.56  fof(f108,plain,(
% 1.46/0.56    ( ! [X6,X5] : (r1_tarski(X5,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X5)))) )),
% 1.46/0.56    inference(superposition,[],[f82,f83])).
% 1.46/0.56  fof(f83,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 1.46/0.56    inference(definition_unfolding,[],[f52,f78,f78])).
% 1.46/0.56  fof(f52,plain,(
% 1.46/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f4])).
% 1.46/0.56  fof(f4,axiom,(
% 1.46/0.56    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.46/0.56  fof(f47,plain,(
% 1.46/0.56    ~r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3))),
% 1.46/0.56    inference(cnf_transformation,[],[f35])).
% 1.46/0.56  fof(f35,plain,(
% 1.46/0.56    (~r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK3)) & v1_relat_1(sK2)),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f20,f34,f33])).
% 1.46/0.56  fof(f33,plain,(
% 1.46/0.56    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0)) => (? [X1] : (~r1_tarski(k3_relat_1(sK2),k3_relat_1(X1)) & r1_tarski(sK2,X1) & v1_relat_1(X1)) & v1_relat_1(sK2))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f34,plain,(
% 1.46/0.56    ? [X1] : (~r1_tarski(k3_relat_1(sK2),k3_relat_1(X1)) & r1_tarski(sK2,X1) & v1_relat_1(X1)) => (~r1_tarski(k3_relat_1(sK2),k3_relat_1(sK3)) & r1_tarski(sK2,sK3) & v1_relat_1(sK3))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f20,plain,(
% 1.46/0.56    ? [X0] : (? [X1] : (~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.46/0.56    inference(flattening,[],[f19])).
% 1.46/0.56  fof(f19,plain,(
% 1.46/0.56    ? [X0] : (? [X1] : ((~r1_tarski(k3_relat_1(X0),k3_relat_1(X1)) & r1_tarski(X0,X1)) & v1_relat_1(X1)) & v1_relat_1(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f18])).
% 1.46/0.56  fof(f18,negated_conjecture,(
% 1.46/0.56    ~! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.46/0.56    inference(negated_conjecture,[],[f17])).
% 1.46/0.56  fof(f17,conjecture,(
% 1.46/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => r1_tarski(k3_relat_1(X0),k3_relat_1(X1)))))),
% 1.46/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_relat_1)).
% 1.46/0.56  fof(f46,plain,(
% 1.46/0.56    r1_tarski(sK2,sK3)),
% 1.46/0.56    inference(cnf_transformation,[],[f35])).
% 1.46/0.56  fof(f44,plain,(
% 1.46/0.56    v1_relat_1(sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f35])).
% 1.46/0.56  fof(f45,plain,(
% 1.46/0.56    v1_relat_1(sK3)),
% 1.46/0.56    inference(cnf_transformation,[],[f35])).
% 1.46/0.56  % SZS output end Proof for theBenchmark
% 1.46/0.56  % (1734)------------------------------
% 1.46/0.56  % (1734)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (1734)Termination reason: Refutation
% 1.46/0.56  
% 1.46/0.56  % (1734)Memory used [KB]: 1918
% 1.46/0.56  % (1734)Time elapsed: 0.138 s
% 1.46/0.56  % (1734)------------------------------
% 1.46/0.56  % (1734)------------------------------
% 1.46/0.56  % (1702)Success in time 0.2 s
%------------------------------------------------------------------------------
