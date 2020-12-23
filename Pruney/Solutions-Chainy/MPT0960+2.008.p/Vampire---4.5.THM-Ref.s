%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 226 expanded)
%              Number of leaves         :   17 (  63 expanded)
%              Depth                    :   19
%              Number of atoms          :  289 ( 896 expanded)
%              Number of equality atoms :   43 ( 134 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f173,plain,(
    $false ),
    inference(subsumption_resolution,[],[f38,f169])).

fof(f169,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(backward_demodulation,[],[f151,f162])).

fof(f162,plain,(
    ! [X0] : k1_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f99,f148])).

fof(f148,plain,(
    ! [X1] : r1_tarski(X1,k1_relat_1(k1_wellord2(X1))) ),
    inference(resolution,[],[f146,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),k1_wellord2(X1))
      | r1_tarski(X0,k1_relat_1(k1_wellord2(X1))) ) ),
    inference(resolution,[],[f117,f39])).

fof(f39,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f117,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | r1_tarski(X2,k1_relat_1(X3)) ) ),
    inference(forward_demodulation,[],[f116,f41])).

fof(f41,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f116,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ v1_relat_1(X3)
      | r1_tarski(k1_relat_1(k6_relat_1(X2)),k1_relat_1(X3)) ) ),
    inference(resolution,[],[f45,f40])).

fof(f40,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f146,plain,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) ),
    inference(subsumption_resolution,[],[f145,f39])).

fof(f145,plain,(
    ! [X0] :
      ( r1_tarski(k6_relat_1(X0),k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X0] :
      ( r1_tarski(k6_relat_1(X0),k1_wellord2(X0))
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f143,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(sK3(X0,X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f28])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

% (7171)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (7171)Refutation not found, incomplete strategy% (7171)------------------------------
% (7171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7175)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% (7178)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% (7182)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (7172)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (7177)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (7171)Termination reason: Refutation not found, incomplete strategy

% (7171)Memory used [KB]: 6012
% (7171)Time elapsed: 0.099 s
% (7171)------------------------------
% (7171)------------------------------
% (7158)Refutation not found, incomplete strategy% (7158)------------------------------
% (7158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7158)Termination reason: Refutation not found, incomplete strategy

% (7158)Memory used [KB]: 10490
% (7158)Time elapsed: 0.104 s
% (7158)------------------------------
% (7158)------------------------------
% (7169)Refutation not found, incomplete strategy% (7169)------------------------------
% (7169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7169)Termination reason: Refutation not found, incomplete strategy

% (7169)Memory used [KB]: 10490
% (7169)Time elapsed: 0.110 s
% (7169)------------------------------
% (7169)------------------------------
% (7181)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (7166)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (7162)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).

% (7159)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% (7164)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% (7173)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% (7159)Refutation not found, incomplete strategy% (7159)------------------------------
% (7159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7159)Termination reason: Refutation not found, incomplete strategy

% (7159)Memory used [KB]: 10618
% (7159)Time elapsed: 0.117 s
% (7159)------------------------------
% (7159)------------------------------
% (7164)Refutation not found, incomplete strategy% (7164)------------------------------
% (7164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7164)Termination reason: Refutation not found, incomplete strategy

% (7164)Memory used [KB]: 10618
% (7164)Time elapsed: 0.083 s
% (7164)------------------------------
% (7164)------------------------------
% (7183)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (7176)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
fof(f143,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,k1_wellord2(X1)),X1)
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) ) ),
    inference(subsumption_resolution,[],[f142,f39])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,k1_wellord2(X1)),X1)
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))
      | ~ v1_relat_1(k1_wellord2(X1)) ) ),
    inference(subsumption_resolution,[],[f141,f69])).

fof(f69,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,k1_wellord2(X1)),X1)
      | ~ r1_tarski(sK3(X0,k1_wellord2(X1)),sK3(X0,k1_wellord2(X1)))
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))
      | ~ v1_relat_1(k1_wellord2(X1)) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,k1_wellord2(X1)),X1)
      | ~ r2_hidden(sK3(X0,k1_wellord2(X1)),X1)
      | ~ r1_tarski(sK3(X0,k1_wellord2(X1)),sK3(X0,k1_wellord2(X1)))
      | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))
      | ~ v1_relat_1(k1_wellord2(X1)) ) ),
    inference(resolution,[],[f138,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1)
      | r1_tarski(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f55,f76])).

fof(f76,plain,(
    ! [X0] : sP0(k1_wellord2(X0),X0) ),
    inference(subsumption_resolution,[],[f75,f39])).

fof(f75,plain,(
    ! [X0] :
      ( sP0(k1_wellord2(X0),X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(resolution,[],[f64,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(definition_folding,[],[f22,f24,f23])).

fof(f23,plain,(
    ! [X1,X0] :
      ( sP0(X1,X0)
    <=> ( ! [X2,X3] :
            ( ( r2_hidden(k4_tarski(X2,X3),X1)
            <=> r1_tarski(X2,X3) )
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        & k3_relat_1(X1) = X0 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> sP0(X1,X0) )
      | ~ sP1(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f64,plain,(
    ! [X0] :
      ( ~ sP1(X0,k1_wellord2(X0))
      | sP0(k1_wellord2(X0),X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( sP0(X1,X0)
      | k1_wellord2(X0) != X1
      | ~ sP1(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ~ sP0(X1,X0) )
        & ( sP0(X1,X0)
          | k1_wellord2(X0) != X1 ) )
      | ~ sP1(X0,X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(k4_tarski(X4,X5),X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
            | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
          & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
            | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
          & r2_hidden(sK5(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X1) )
        | k3_relat_1(X0) != X1 )
      & ( ( ! [X4,X5] :
              ( ( ( r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r1_tarski(X4,X5) )
                & ( r1_tarski(X4,X5)
                  | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          & k3_relat_1(X0) = X1 )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f34])).

fof(f34,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X0) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X0) )
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ( ~ r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | ~ r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
        & ( r1_tarski(sK4(X0,X1),sK5(X0,X1))
          | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0) )
        & r2_hidden(sK5(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X0) )
            & r2_hidden(X3,X1)
            & r2_hidden(X2,X1) )
        | k3_relat_1(X0) != X1 )
      & ( ( ! [X4,X5] :
              ( ( ( r2_hidden(k4_tarski(X4,X5),X0)
                  | ~ r1_tarski(X4,X5) )
                & ( r1_tarski(X4,X5)
                  | ~ r2_hidden(k4_tarski(X4,X5),X0) ) )
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X1) )
          & k3_relat_1(X0) = X1 )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X1) )
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | k3_relat_1(X1) != X0 )
      & ( ( ! [X2,X3] :
              ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                  | ~ r1_tarski(X2,X3) )
                & ( r1_tarski(X2,X3)
                  | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 )
        | ~ sP0(X1,X0) ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ( sP0(X1,X0)
        | ? [X2,X3] :
            ( ( ~ r1_tarski(X2,X3)
              | ~ r2_hidden(k4_tarski(X2,X3),X1) )
            & ( r1_tarski(X2,X3)
              | r2_hidden(k4_tarski(X2,X3),X1) )
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | k3_relat_1(X1) != X0 )
      & ( ( ! [X2,X3] :
              ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                  | ~ r1_tarski(X2,X3) )
                & ( r1_tarski(X2,X3)
                  | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 )
        | ~ sP0(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f99,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_relat_1(k1_wellord2(X0)))
      | k1_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(resolution,[],[f96,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,(
    ! [X3] : r1_tarski(k1_relat_1(k1_wellord2(X3)),X3) ),
    inference(superposition,[],[f47,f88])).

fof(f88,plain,(
    ! [X0] : k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = X0 ),
    inference(forward_demodulation,[],[f86,f77])).

fof(f77,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(resolution,[],[f76,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k3_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) ),
    inference(resolution,[],[f44,f39])).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f151,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),X0)) ),
    inference(backward_demodulation,[],[f78,f150])).

fof(f150,plain,(
    ! [X0] : k2_relat_1(k1_wellord2(X0)) = X0 ),
    inference(subsumption_resolution,[],[f97,f147])).

fof(f147,plain,(
    ! [X0] : r1_tarski(X0,k2_relat_1(k1_wellord2(X0))) ),
    inference(resolution,[],[f146,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_relat_1(X0),k1_wellord2(X1))
      | r1_tarski(X0,k2_relat_1(k1_wellord2(X1))) ) ),
    inference(resolution,[],[f124,f39])).

fof(f124,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X3)
      | ~ r1_tarski(k6_relat_1(X2),X3)
      | r1_tarski(X2,k2_relat_1(X3)) ) ),
    inference(forward_demodulation,[],[f123,f42])).

fof(f42,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f123,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(k6_relat_1(X2),X3)
      | ~ v1_relat_1(X3)
      | r1_tarski(k2_relat_1(k6_relat_1(X2)),k2_relat_1(X3)) ) ),
    inference(resolution,[],[f46,f40])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f97,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k2_relat_1(k1_wellord2(X0)))
      | k2_relat_1(k1_wellord2(X0)) = X0 ) ),
    inference(resolution,[],[f95,f63])).

fof(f95,plain,(
    ! [X0] : r1_tarski(k2_relat_1(k1_wellord2(X0)),X0) ),
    inference(superposition,[],[f71,f88])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f47,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f78,plain,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) ),
    inference(resolution,[],[f43,f39])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f38,plain,(
    ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f26])).

fof(f26,plain,
    ( ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))
   => ~ r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] : ~ r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:49:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (7158)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  % (7165)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.50  % (7163)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (7163)Refutation not found, incomplete strategy% (7163)------------------------------
% 0.20/0.50  % (7163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7163)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  % (7160)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  
% 0.20/0.50  % (7163)Memory used [KB]: 6140
% 0.20/0.50  % (7163)Time elapsed: 0.094 s
% 0.20/0.50  % (7163)------------------------------
% 0.20/0.50  % (7163)------------------------------
% 0.20/0.50  % (7169)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (7168)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (7180)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (7167)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (7165)Refutation not found, incomplete strategy% (7165)------------------------------
% 0.20/0.50  % (7165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (7165)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (7165)Memory used [KB]: 1663
% 0.20/0.50  % (7165)Time elapsed: 0.096 s
% 0.20/0.50  % (7165)------------------------------
% 0.20/0.50  % (7165)------------------------------
% 0.20/0.50  % (7161)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (7179)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (7161)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  fof(f173,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(subsumption_resolution,[],[f38,f169])).
% 0.20/0.50  fof(f169,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))) )),
% 0.20/0.50    inference(backward_demodulation,[],[f151,f162])).
% 0.20/0.50  fof(f162,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f99,f148])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    ( ! [X1] : (r1_tarski(X1,k1_relat_1(k1_wellord2(X1)))) )),
% 0.20/0.50    inference(resolution,[],[f146,f118])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) | r1_tarski(X0,k1_relat_1(k1_wellord2(X1)))) )),
% 0.20/0.50    inference(resolution,[],[f117,f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.20/0.50  fof(f117,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~v1_relat_1(X3) | ~r1_tarski(k6_relat_1(X2),X3) | r1_tarski(X2,k1_relat_1(X3))) )),
% 0.20/0.50    inference(forward_demodulation,[],[f116,f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.50    inference(cnf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,axiom,(
% 0.20/0.50    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    ( ! [X2,X3] : (~r1_tarski(k6_relat_1(X2),X3) | ~v1_relat_1(X3) | r1_tarski(k1_relat_1(k6_relat_1(X2)),k1_relat_1(X3))) )),
% 0.20/0.50    inference(resolution,[],[f45,f40])).
% 0.20/0.50  fof(f40,plain,(
% 0.20/0.50    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f18])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f17])).
% 0.20/0.50  fof(f17,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).
% 0.20/0.50  fof(f146,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k1_wellord2(X0))) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f145,f39])).
% 0.20/0.50  fof(f145,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f144])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    ( ! [X0] : (r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) | r1_tarski(k6_relat_1(X0),k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.50    inference(resolution,[],[f143,f49])).
% 0.20/0.50  fof(f49,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f29])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | (~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1) & r2_hidden(sK3(X0,X1),X0)) | ~v1_relat_1(X1))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f20,f28])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ! [X1,X0] : (? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) => (~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  % (7171)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (7171)Refutation not found, incomplete strategy% (7171)------------------------------
% 0.20/0.51  % (7171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7175)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (7178)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (7182)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.51  % (7172)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (7177)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.51  % (7171)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7171)Memory used [KB]: 6012
% 0.20/0.51  % (7171)Time elapsed: 0.099 s
% 0.20/0.51  % (7171)------------------------------
% 0.20/0.51  % (7171)------------------------------
% 0.20/0.51  % (7158)Refutation not found, incomplete strategy% (7158)------------------------------
% 0.20/0.51  % (7158)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7158)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7158)Memory used [KB]: 10490
% 0.20/0.51  % (7158)Time elapsed: 0.104 s
% 0.20/0.51  % (7158)------------------------------
% 0.20/0.51  % (7158)------------------------------
% 0.20/0.51  % (7169)Refutation not found, incomplete strategy% (7169)------------------------------
% 0.20/0.51  % (7169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (7169)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (7169)Memory used [KB]: 10490
% 0.20/0.51  % (7169)Time elapsed: 0.110 s
% 0.20/0.51  % (7169)------------------------------
% 0.20/0.51  % (7169)------------------------------
% 0.20/0.52  % (7181)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.52  % (7166)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (7162)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1] : ((r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0))) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : (r2_hidden(X2,X0) => r2_hidden(k4_tarski(X2,X2),X1)) => r1_tarski(k6_relat_1(X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).
% 0.20/0.52  % (7159)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (7164)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (7173)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (7159)Refutation not found, incomplete strategy% (7159)------------------------------
% 0.20/0.52  % (7159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7159)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (7159)Memory used [KB]: 10618
% 0.20/0.52  % (7159)Time elapsed: 0.117 s
% 0.20/0.52  % (7159)------------------------------
% 0.20/0.52  % (7159)------------------------------
% 0.20/0.52  % (7164)Refutation not found, incomplete strategy% (7164)------------------------------
% 0.20/0.52  % (7164)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7164)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (7164)Memory used [KB]: 10618
% 0.20/0.52  % (7164)Time elapsed: 0.083 s
% 0.20/0.52  % (7164)------------------------------
% 0.20/0.52  % (7164)------------------------------
% 0.20/0.52  % (7183)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (7176)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,k1_wellord2(X1)),X1) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f142,f39])).
% 0.20/0.52  fof(f142,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,k1_wellord2(X1)),X1) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) | ~v1_relat_1(k1_wellord2(X1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f141,f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(flattening,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,k1_wellord2(X1)),X1) | ~r1_tarski(sK3(X0,k1_wellord2(X1)),sK3(X0,k1_wellord2(X1))) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) | ~v1_relat_1(k1_wellord2(X1))) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f139])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,k1_wellord2(X1)),X1) | ~r2_hidden(sK3(X0,k1_wellord2(X1)),X1) | ~r1_tarski(sK3(X0,k1_wellord2(X1)),sK3(X0,k1_wellord2(X1))) | r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) | ~v1_relat_1(k1_wellord2(X1))) )),
% 0.20/0.52    inference(resolution,[],[f138,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK3(X0,X1),sK3(X0,X1)),X1) | r1_tarski(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),k1_wellord2(X2)) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.52    inference(resolution,[],[f55,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X0] : (sP0(k1_wellord2(X0),X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f75,f39])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X0] : (sP0(k1_wellord2(X0),X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.20/0.52    inference(resolution,[],[f64,f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sP1(X0,X1) | ~v1_relat_1(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (sP1(X0,X1) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(definition_folding,[],[f22,f24,f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X1,X0] : (sP0(X1,X0) <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> sP0(X1,X0)) | ~sP1(X0,X1))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(flattening,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X0] : (~sP1(X0,k1_wellord2(X0)) | sP0(k1_wellord2(X0),X0)) )),
% 0.20/0.52    inference(equality_resolution,[],[f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0,X1] : (sP0(X1,X0) | k1_wellord2(X0) != X1 | ~sP1(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ~sP0(X1,X0)) & (sP0(X1,X0) | k1_wellord2(X0) != X1)) | ~sP1(X0,X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f24])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X4,X0,X5,X1] : (~sP0(X0,X1) | ~r1_tarski(X4,X5) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1) | r2_hidden(k4_tarski(X4,X5),X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ! [X0,X1] : ((sP0(X0,X1) | ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1)) | k3_relat_1(X0) != X1) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X0))) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) & k3_relat_1(X0) = X1) | ~sP0(X0,X1)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) => ((~r1_tarski(sK4(X0,X1),sK5(X0,X1)) | ~r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & (r1_tarski(sK4(X0,X1),sK5(X0,X1)) | r2_hidden(k4_tarski(sK4(X0,X1),sK5(X0,X1)),X0)) & r2_hidden(sK5(X0,X1),X1) & r2_hidden(sK4(X0,X1),X1)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0,X1] : ((sP0(X0,X1) | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X0)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X0)) & r2_hidden(X3,X1) & r2_hidden(X2,X1)) | k3_relat_1(X0) != X1) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X0) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X0))) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X1)) & k3_relat_1(X0) = X1) | ~sP0(X0,X1)))),
% 0.20/0.52    inference(rectify,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X1,X0] : ((sP0(X1,X0) | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | ~sP0(X1,X0)))),
% 0.20/0.52    inference(flattening,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X1,X0] : ((sP0(X1,X0) | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | ~sP0(X1,X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f23])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,k1_relat_1(k1_wellord2(X0))) | k1_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.52    inference(resolution,[],[f96,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f37])).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ( ! [X3] : (r1_tarski(k1_relat_1(k1_wellord2(X3)),X3)) )),
% 0.20/0.52    inference(superposition,[],[f47,f88])).
% 0.20/0.52  fof(f88,plain,(
% 0.20/0.52    ( ! [X0] : (k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))) = X0) )),
% 0.20/0.52    inference(forward_demodulation,[],[f86,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.52    inference(resolution,[],[f76,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~sP0(X0,X1) | k3_relat_1(X0) = X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = k2_xboole_0(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0)))) )),
% 0.20/0.52    inference(resolution,[],[f44,f39])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_relat_1)).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),X0))) )),
% 0.20/0.52    inference(backward_demodulation,[],[f78,f150])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    ( ! [X0] : (k2_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f97,f147])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(X0,k2_relat_1(k1_wellord2(X0)))) )),
% 0.20/0.52    inference(resolution,[],[f146,f125])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r1_tarski(k6_relat_1(X0),k1_wellord2(X1)) | r1_tarski(X0,k2_relat_1(k1_wellord2(X1)))) )),
% 0.20/0.52    inference(resolution,[],[f124,f39])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~v1_relat_1(X3) | ~r1_tarski(k6_relat_1(X2),X3) | r1_tarski(X2,k2_relat_1(X3))) )),
% 0.20/0.52    inference(forward_demodulation,[],[f123,f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f8])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    ( ! [X2,X3] : (~r1_tarski(k6_relat_1(X2),X3) | ~v1_relat_1(X3) | r1_tarski(k2_relat_1(k6_relat_1(X2)),k2_relat_1(X3))) )),
% 0.20/0.52    inference(resolution,[],[f46,f40])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | r1_tarski(k2_relat_1(X0),k2_relat_1(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ( ! [X0] : (~r1_tarski(X0,k2_relat_1(k1_wellord2(X0))) | k2_relat_1(k1_wellord2(X0)) = X0) )),
% 0.20/0.52    inference(resolution,[],[f95,f63])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(k1_wellord2(X0)),X0)) )),
% 0.20/0.52    inference(superposition,[],[f71,f88])).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 0.20/0.52    inference(superposition,[],[f47,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X0] : (r1_tarski(k1_wellord2(X0),k2_zfmisc_1(k1_relat_1(k1_wellord2(X0)),k2_relat_1(k1_wellord2(X0))))) )),
% 0.20/0.52    inference(resolution,[],[f43,f39])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ~r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ~r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0)) => ~r1_tarski(k1_wellord2(sK2),k2_zfmisc_1(sK2,sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0] : ~r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,negated_conjecture,(
% 0.20/0.52    ~! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.20/0.52    inference(negated_conjecture,[],[f12])).
% 0.20/0.52  fof(f12,conjecture,(
% 0.20/0.52    ! [X0] : r1_tarski(k1_wellord2(X0),k2_zfmisc_1(X0,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (7161)------------------------------
% 0.20/0.52  % (7161)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (7161)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (7161)Memory used [KB]: 6268
% 0.20/0.52  % (7161)Time elapsed: 0.100 s
% 0.20/0.52  % (7161)------------------------------
% 0.20/0.52  % (7161)------------------------------
% 0.20/0.53  % (7170)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.53  % (7157)Success in time 0.168 s
%------------------------------------------------------------------------------
