%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0745+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 444 expanded)
%              Number of leaves         :    9 ( 109 expanded)
%              Depth                    :   17
%              Number of atoms          :  181 (1377 expanded)
%              Number of equality atoms :   11 ( 132 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f457,plain,(
    $false ),
    inference(global_subsumption,[],[f262,f440])).

fof(f440,plain,(
    r2_hidden(sK4(sK1(k3_tarski(sK0)),k3_tarski(sK0)),sK7(sK0,sK1(k3_tarski(sK0)))) ),
    inference(unit_resulting_resolution,[],[f346,f217,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f217,plain,(
    r2_hidden(sK4(sK1(k3_tarski(sK0)),k3_tarski(sK0)),sK1(k3_tarski(sK0))) ),
    inference(unit_resulting_resolution,[],[f187,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f187,plain,(
    ~ r1_tarski(sK1(k3_tarski(sK0)),k3_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f181,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r1_tarski(X1,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
    <=> ! [X1] :
          ( r2_hidden(X1,X0)
         => r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

fof(f181,plain,(
    ~ v1_ordinal1(k3_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f174,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v2_ordinal1(X0)
      | ~ v1_ordinal1(X0)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
    <=> ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_ordinal1)).

% (3890)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (3894)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (3885)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% (3882)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (3900)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (3880)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (3892)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% (3881)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (3897)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (3891)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (3889)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (3893)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% (3904)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f174,plain,(
    v2_ordinal1(k3_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f173])).

% (3904)Refutation not found, incomplete strategy% (3904)------------------------------
% (3904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (3904)Termination reason: Refutation not found, incomplete strategy

% (3904)Memory used [KB]: 10746
% (3904)Time elapsed: 0.136 s
% (3904)------------------------------
% (3904)------------------------------
fof(f173,plain,
    ( v2_ordinal1(k3_tarski(sK0))
    | v2_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f159,f132])).

fof(f132,plain,
    ( v3_ordinal1(sK2(k3_tarski(sK0)))
    | v2_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f129,f67])).

fof(f67,plain,(
    ! [X1] :
      ( sP6(sK2(k3_tarski(X1)),X1)
      | v2_ordinal1(k3_tarski(X1)) ) ),
    inference(resolution,[],[f48,f29])).

fof(f29,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ( r2_hidden(X2,X1)
          | X1 = X2
          | r2_hidden(X1,X2)
          | ~ r2_hidden(X2,X0)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_ordinal1(X0)
    <=> ! [X1,X2] :
          ~ ( ~ r2_hidden(X2,X1)
            & X1 != X2
            & ~ r2_hidden(X1,X2)
            & r2_hidden(X2,X0)
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_ordinal1)).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k3_tarski(X0))
      | sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f129,plain,(
    ! [X0] :
      ( ~ sP6(X0,sK0)
      | v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ sP6(X0,sK0)
      | v3_ordinal1(X0)
      | ~ sP6(X0,sK0) ) ),
    inference(resolution,[],[f86,f90])).

fof(f90,plain,(
    ! [X6] :
      ( v3_ordinal1(sK7(sK0,X6))
      | ~ sP6(X6,sK0) ) ),
    inference(resolution,[],[f43,f20])).

fof(f20,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK0)
      | v3_ordinal1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ~ v3_ordinal1(k3_tarski(X0))
      & ! [X1] :
          ( v3_ordinal1(X1)
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

% (3907)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ! [X1] :
            ( r2_hidden(X1,X0)
           => v3_ordinal1(X1) )
       => v3_ordinal1(k3_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
         => v3_ordinal1(X1) )
     => v3_ordinal1(k3_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_ordinal1)).

fof(f43,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK7(X0,X2),X0)
      | ~ sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f6])).

% (3906)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f86,plain,(
    ! [X2,X3] :
      ( ~ v3_ordinal1(sK7(X3,X2))
      | ~ sP6(X2,X3)
      | v3_ordinal1(X2) ) ),
    inference(resolution,[],[f42,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v3_ordinal1(X0)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v3_ordinal1(X1)
     => ( r2_hidden(X0,X1)
       => v3_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_ordinal1)).

fof(f42,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK7(X0,X2))
      | ~ sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f159,plain,
    ( ~ v3_ordinal1(sK2(k3_tarski(sK0)))
    | v2_ordinal1(k3_tarski(sK0)) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,
    ( v2_ordinal1(k3_tarski(sK0))
    | ~ v3_ordinal1(sK2(k3_tarski(sK0)))
    | v2_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f133,f120])).

fof(f120,plain,(
    ! [X12] :
      ( ~ v3_ordinal1(sK3(X12))
      | ~ v3_ordinal1(sK2(X12))
      | v2_ordinal1(X12) ) ),
    inference(global_subsumption,[],[f32,f31,f115])).

fof(f115,plain,(
    ! [X12] :
      ( ~ v3_ordinal1(sK3(X12))
      | r2_hidden(sK2(X12),sK3(X12))
      | sK3(X12) = sK2(X12)
      | ~ v3_ordinal1(sK2(X12))
      | v2_ordinal1(X12) ) ),
    inference(resolution,[],[f24,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK3(X0),sK2(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f13])).

% (3884)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2(X0),sK3(X0))
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0] :
      ( sK2(X0) != sK3(X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f133,plain,
    ( v3_ordinal1(sK3(k3_tarski(sK0)))
    | v2_ordinal1(k3_tarski(sK0)) ),
    inference(resolution,[],[f129,f68])).

fof(f68,plain,(
    ! [X2] :
      ( sP6(sK3(k3_tarski(X2)),X2)
      | v2_ordinal1(k3_tarski(X2)) ) ),
    inference(resolution,[],[f48,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v2_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f21,plain,(
    ~ v3_ordinal1(k3_tarski(sK0)) ),
    inference(cnf_transformation,[],[f11])).

% (3887)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
fof(f346,plain,(
    r1_tarski(sK1(k3_tarski(sK0)),sK7(sK0,sK1(k3_tarski(sK0)))) ),
    inference(unit_resulting_resolution,[],[f186,f204,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,sK7(X1,X0))
      | ~ sP6(X0,X1)
      | ~ v1_ordinal1(sK7(X1,X0)) ) ),
    inference(resolution,[],[f42,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | r1_tarski(X1,X0)
      | ~ v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f204,plain,(
    v1_ordinal1(sK7(sK0,sK1(k3_tarski(sK0)))) ),
    inference(unit_resulting_resolution,[],[f186,f92])).

fof(f92,plain,(
    ! [X1] :
      ( v1_ordinal1(sK7(sK0,X1))
      | ~ sP6(X1,sK0) ) ),
    inference(resolution,[],[f90,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f186,plain,(
    sP6(sK1(k3_tarski(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f181,f66])).

fof(f66,plain,(
    ! [X0] :
      ( sP6(sK1(k3_tarski(X0)),X0)
      | v1_ordinal1(k3_tarski(X0)) ) ),
    inference(resolution,[],[f48,f26])).

fof(f26,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f262,plain,(
    ~ r2_hidden(sK4(sK1(k3_tarski(sK0)),k3_tarski(sK0)),sK7(sK0,sK1(k3_tarski(sK0)))) ),
    inference(unit_resulting_resolution,[],[f207,f257,f41])).

fof(f41,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3)
      | sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f257,plain,(
    ~ sP6(sK4(sK1(k3_tarski(sK0)),k3_tarski(sK0)),sK0) ),
    inference(unit_resulting_resolution,[],[f187,f83])).

fof(f83,plain,(
    ! [X2,X1] :
      ( ~ sP6(sK4(X1,k3_tarski(X2)),X2)
      | r1_tarski(X1,k3_tarski(X2)) ) ),
    inference(resolution,[],[f40,f49])).

fof(f49,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k3_tarski(X0))
      | ~ sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X2,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f207,plain,(
    r2_hidden(sK7(sK0,sK1(k3_tarski(sK0))),sK0) ),
    inference(unit_resulting_resolution,[],[f186,f43])).

%------------------------------------------------------------------------------
