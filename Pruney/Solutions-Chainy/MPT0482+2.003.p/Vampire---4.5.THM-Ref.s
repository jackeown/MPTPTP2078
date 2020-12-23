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
% DateTime   : Thu Dec  3 12:48:15 EST 2020

% Result     : Theorem 1.31s
% Output     : Refutation 1.31s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 110 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   17
%              Number of atoms          :  144 ( 302 expanded)
%              Number of equality atoms :   10 (  41 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(subsumption_resolution,[],[f149,f19])).

fof(f19,plain,(
    sK1 != k5_relat_1(k6_relat_1(sK0),sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k5_relat_1(k6_relat_1(X0),X1) != X1
      & r1_tarski(k1_relat_1(X1),X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( r1_tarski(k1_relat_1(X1),X0)
         => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k1_relat_1(X1),X0)
       => k5_relat_1(k6_relat_1(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

fof(f149,plain,(
    sK1 = k5_relat_1(k6_relat_1(sK0),sK1) ),
    inference(resolution,[],[f148,f96])).

fof(f96,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK1,k5_relat_1(k6_relat_1(X3),sK1))
      | sK1 = k5_relat_1(k6_relat_1(X3),sK1) ) ),
    inference(resolution,[],[f94,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f94,plain,(
    ! [X0] : r1_tarski(k5_relat_1(k6_relat_1(X0),sK1),sK1) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
    ! [X0] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),sK1),sK1)
      | r1_tarski(k5_relat_1(k6_relat_1(X0),sK1),sK1) ) ),
    inference(resolution,[],[f89,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k5_relat_1(k6_relat_1(X0),sK1),X1),sK1)
      | r1_tarski(k5_relat_1(k6_relat_1(X0),sK1),X1) ) ),
    inference(resolution,[],[f88,f36])).

fof(f36,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_relat_1(k6_relat_1(X2),sK1))
      | r2_hidden(sK4(X0,X1),sK1)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f69,f17])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f69,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ v1_relat_1(X11)
      | r2_hidden(sK4(X9,X10),X11)
      | ~ r1_tarski(X9,k5_relat_1(k6_relat_1(X12),X11))
      | r1_tarski(X9,X10) ) ),
    inference(resolution,[],[f46,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1)
        & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).

fof(f46,plain,(
    ! [X4,X2,X5,X3] :
      ( ~ r1_tarski(X3,X5)
      | r1_tarski(X2,X4)
      | r2_hidden(sK4(X2,X4),X5)
      | ~ r1_tarski(X2,X3) ) ),
    inference(resolution,[],[f44,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f148,plain,(
    r1_tarski(sK1,k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,
    ( r1_tarski(sK1,k5_relat_1(k6_relat_1(sK0),sK1))
    | r1_tarski(sK1,k5_relat_1(k6_relat_1(sK0),sK1)) ),
    inference(resolution,[],[f103,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ r2_hidden(k4_tarski(sK2(sK1,X0),sK3(sK1,X0)),X0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f22,f17])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

% (407)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).

fof(f103,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(sK2(sK1,X3),sK3(sK1,X3)),k5_relat_1(k6_relat_1(sK0),sK1))
      | r1_tarski(sK1,X3) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X3] :
      ( r2_hidden(k4_tarski(sK2(sK1,X3),sK3(sK1,X3)),k5_relat_1(k6_relat_1(sK0),sK1))
      | r1_tarski(sK1,X3)
      | r1_tarski(sK1,X3) ) ),
    inference(resolution,[],[f99,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK1,X0),sK0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f62,f36])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK0,X1)
      | r2_hidden(sK2(sK1,X0),X1)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f60,f18])).

fof(f18,plain,(
    r1_tarski(k1_relat_1(sK1),sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_relat_1(sK1),X1)
      | r1_tarski(sK1,X0)
      | r2_hidden(sK2(sK1,X0),X2)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f56,f28])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(sK1,X0),X1)
      | r1_tarski(sK1,X0)
      | ~ r1_tarski(k1_relat_1(sK1),X1) ) ),
    inference(resolution,[],[f53,f28])).

fof(f53,plain,(
    ! [X3] :
      ( r2_hidden(sK2(sK1,X3),k1_relat_1(sK1))
      | r1_tarski(sK1,X3) ) ),
    inference(subsumption_resolution,[],[f51,f17])).

fof(f51,plain,(
    ! [X3] :
      ( r1_tarski(sK1,X3)
      | ~ v1_relat_1(sK1)
      | r2_hidden(sK2(sK1,X3),k1_relat_1(sK1)) ) ),
    inference(resolution,[],[f48,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X0,k1_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f48,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(sK2(sK1,X0),sK3(sK1,X0)),sK1)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f21,f17])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(sK1,X0),X1)
      | r2_hidden(k4_tarski(sK2(sK1,X0),sK3(sK1,X0)),k5_relat_1(k6_relat_1(X1),sK1))
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f98,f48])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X2),sK1)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),sK1)) ) ),
    inference(resolution,[],[f35,f17])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X3)
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),X3)
      | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) )
      | ~ v1_relat_1(X3) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( v1_relat_1(X3)
     => ( r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))
      <=> ( r2_hidden(k4_tarski(X0,X1),X3)
          & r2_hidden(X0,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:44:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.15/0.52  % (417)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.15/0.52  % (409)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.15/0.52  % (399)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.15/0.53  % (396)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.15/0.53  % (397)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.15/0.53  % (400)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.15/0.53  % (397)Refutation not found, incomplete strategy% (397)------------------------------
% 1.15/0.53  % (397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.53  % (397)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.53  
% 1.15/0.53  % (397)Memory used [KB]: 10618
% 1.15/0.53  % (397)Time elapsed: 0.116 s
% 1.15/0.53  % (397)------------------------------
% 1.15/0.53  % (397)------------------------------
% 1.15/0.53  % (417)Refutation not found, incomplete strategy% (417)------------------------------
% 1.15/0.53  % (417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.15/0.53  % (417)Termination reason: Refutation not found, incomplete strategy
% 1.15/0.53  
% 1.15/0.53  % (417)Memory used [KB]: 10746
% 1.15/0.53  % (417)Time elapsed: 0.068 s
% 1.15/0.53  % (417)------------------------------
% 1.15/0.53  % (417)------------------------------
% 1.15/0.53  % (398)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.31/0.53  % (395)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.31/0.53  % (414)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.31/0.54  % (418)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.31/0.54  % (422)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.31/0.54  % (412)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.31/0.54  % (410)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.31/0.54  % (406)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.31/0.54  % (421)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.31/0.55  % (401)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.31/0.55  % (408)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.31/0.55  % (404)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.31/0.55  % (405)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.31/0.55  % (412)Refutation not found, incomplete strategy% (412)------------------------------
% 1.31/0.55  % (412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (405)Refutation not found, incomplete strategy% (405)------------------------------
% 1.31/0.55  % (405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (405)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (405)Memory used [KB]: 10618
% 1.31/0.55  % (405)Time elapsed: 0.141 s
% 1.31/0.55  % (405)------------------------------
% 1.31/0.55  % (405)------------------------------
% 1.31/0.55  % (402)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.31/0.55  % (412)Termination reason: Refutation not found, incomplete strategy
% 1.31/0.55  
% 1.31/0.55  % (412)Memory used [KB]: 10746
% 1.31/0.55  % (412)Time elapsed: 0.143 s
% 1.31/0.55  % (412)------------------------------
% 1.31/0.55  % (412)------------------------------
% 1.31/0.55  % (401)Refutation found. Thanks to Tanya!
% 1.31/0.55  % SZS status Theorem for theBenchmark
% 1.31/0.55  % SZS output start Proof for theBenchmark
% 1.31/0.55  fof(f157,plain,(
% 1.31/0.55    $false),
% 1.31/0.55    inference(subsumption_resolution,[],[f149,f19])).
% 1.31/0.55  fof(f19,plain,(
% 1.31/0.55    sK1 != k5_relat_1(k6_relat_1(sK0),sK1)),
% 1.31/0.55    inference(cnf_transformation,[],[f10])).
% 1.31/0.55  fof(f10,plain,(
% 1.31/0.55    ? [X0,X1] : (k5_relat_1(k6_relat_1(X0),X1) != X1 & r1_tarski(k1_relat_1(X1),X0) & v1_relat_1(X1))),
% 1.31/0.55    inference(flattening,[],[f9])).
% 1.31/0.55  fof(f9,plain,(
% 1.31/0.55    ? [X0,X1] : ((k5_relat_1(k6_relat_1(X0),X1) != X1 & r1_tarski(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 1.31/0.55    inference(ennf_transformation,[],[f8])).
% 1.31/0.55  fof(f8,negated_conjecture,(
% 1.31/0.55    ~! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.31/0.55    inference(negated_conjecture,[],[f7])).
% 1.31/0.55  fof(f7,conjecture,(
% 1.31/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k1_relat_1(X1),X0) => k5_relat_1(k6_relat_1(X0),X1) = X1))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).
% 1.31/0.55  fof(f149,plain,(
% 1.31/0.55    sK1 = k5_relat_1(k6_relat_1(sK0),sK1)),
% 1.31/0.55    inference(resolution,[],[f148,f96])).
% 1.31/0.55  fof(f96,plain,(
% 1.31/0.55    ( ! [X3] : (~r1_tarski(sK1,k5_relat_1(k6_relat_1(X3),sK1)) | sK1 = k5_relat_1(k6_relat_1(X3),sK1)) )),
% 1.31/0.55    inference(resolution,[],[f94,f27])).
% 1.31/0.55  fof(f27,plain,(
% 1.31/0.55    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.31/0.55    inference(cnf_transformation,[],[f2])).
% 1.31/0.55  fof(f2,axiom,(
% 1.31/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.31/0.55  fof(f94,plain,(
% 1.31/0.55    ( ! [X0] : (r1_tarski(k5_relat_1(k6_relat_1(X0),sK1),sK1)) )),
% 1.31/0.55    inference(duplicate_literal_removal,[],[f92])).
% 1.31/0.55  fof(f92,plain,(
% 1.31/0.55    ( ! [X0] : (r1_tarski(k5_relat_1(k6_relat_1(X0),sK1),sK1) | r1_tarski(k5_relat_1(k6_relat_1(X0),sK1),sK1)) )),
% 1.31/0.55    inference(resolution,[],[f89,f30])).
% 1.31/0.55  fof(f30,plain,(
% 1.31/0.55    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f13])).
% 1.31/0.55  fof(f13,plain,(
% 1.31/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.31/0.55    inference(ennf_transformation,[],[f1])).
% 1.31/0.55  fof(f1,axiom,(
% 1.31/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.31/0.55  fof(f89,plain,(
% 1.31/0.55    ( ! [X0,X1] : (r2_hidden(sK4(k5_relat_1(k6_relat_1(X0),sK1),X1),sK1) | r1_tarski(k5_relat_1(k6_relat_1(X0),sK1),X1)) )),
% 1.31/0.55    inference(resolution,[],[f88,f36])).
% 1.31/0.55  fof(f36,plain,(
% 1.31/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.31/0.55    inference(equality_resolution,[],[f26])).
% 1.31/0.55  fof(f26,plain,(
% 1.31/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.31/0.55    inference(cnf_transformation,[],[f2])).
% 1.31/0.55  fof(f88,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_relat_1(k6_relat_1(X2),sK1)) | r2_hidden(sK4(X0,X1),sK1) | r1_tarski(X0,X1)) )),
% 1.31/0.55    inference(resolution,[],[f69,f17])).
% 1.31/0.55  fof(f17,plain,(
% 1.31/0.55    v1_relat_1(sK1)),
% 1.31/0.55    inference(cnf_transformation,[],[f10])).
% 1.31/0.55  fof(f69,plain,(
% 1.31/0.55    ( ! [X12,X10,X11,X9] : (~v1_relat_1(X11) | r2_hidden(sK4(X9,X10),X11) | ~r1_tarski(X9,k5_relat_1(k6_relat_1(X12),X11)) | r1_tarski(X9,X10)) )),
% 1.31/0.55    inference(resolution,[],[f46,f24])).
% 1.31/0.55  fof(f24,plain,(
% 1.31/0.55    ( ! [X0,X1] : (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) | ~v1_relat_1(X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f12])).
% 1.31/0.55  fof(f12,plain,(
% 1.31/0.55    ! [X0,X1] : ((r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)) | ~v1_relat_1(X1))),
% 1.31/0.55    inference(ennf_transformation,[],[f6])).
% 1.31/0.55  fof(f6,axiom,(
% 1.31/0.55    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k5_relat_1(k6_relat_1(X0),X1),X1) & r1_tarski(k5_relat_1(X1,k6_relat_1(X0)),X1)))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_relat_1)).
% 1.31/0.55  fof(f46,plain,(
% 1.31/0.55    ( ! [X4,X2,X5,X3] : (~r1_tarski(X3,X5) | r1_tarski(X2,X4) | r2_hidden(sK4(X2,X4),X5) | ~r1_tarski(X2,X3)) )),
% 1.31/0.55    inference(resolution,[],[f44,f28])).
% 1.31/0.55  fof(f28,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f13])).
% 1.31/0.55  fof(f44,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 1.31/0.55    inference(resolution,[],[f28,f29])).
% 1.31/0.55  fof(f29,plain,(
% 1.31/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f13])).
% 1.31/0.55  fof(f148,plain,(
% 1.31/0.55    r1_tarski(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),
% 1.31/0.55    inference(duplicate_literal_removal,[],[f144])).
% 1.31/0.55  fof(f144,plain,(
% 1.31/0.55    r1_tarski(sK1,k5_relat_1(k6_relat_1(sK0),sK1)) | r1_tarski(sK1,k5_relat_1(k6_relat_1(sK0),sK1))),
% 1.31/0.55    inference(resolution,[],[f103,f55])).
% 1.31/0.55  fof(f55,plain,(
% 1.31/0.55    ( ! [X0] : (~r2_hidden(k4_tarski(sK2(sK1,X0),sK3(sK1,X0)),X0) | r1_tarski(sK1,X0)) )),
% 1.31/0.55    inference(resolution,[],[f22,f17])).
% 1.31/0.55  fof(f22,plain,(
% 1.31/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) | r1_tarski(X0,X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f11])).
% 1.31/0.55  % (407)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.31/0.55  fof(f11,plain,(
% 1.31/0.55    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 1.31/0.55    inference(ennf_transformation,[],[f3])).
% 1.31/0.55  fof(f3,axiom,(
% 1.31/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_relat_1)).
% 1.31/0.55  fof(f103,plain,(
% 1.31/0.55    ( ! [X3] : (r2_hidden(k4_tarski(sK2(sK1,X3),sK3(sK1,X3)),k5_relat_1(k6_relat_1(sK0),sK1)) | r1_tarski(sK1,X3)) )),
% 1.31/0.55    inference(duplicate_literal_removal,[],[f102])).
% 1.31/0.55  fof(f102,plain,(
% 1.31/0.55    ( ! [X3] : (r2_hidden(k4_tarski(sK2(sK1,X3),sK3(sK1,X3)),k5_relat_1(k6_relat_1(sK0),sK1)) | r1_tarski(sK1,X3) | r1_tarski(sK1,X3)) )),
% 1.31/0.55    inference(resolution,[],[f99,f64])).
% 1.31/0.55  fof(f64,plain,(
% 1.31/0.55    ( ! [X0] : (r2_hidden(sK2(sK1,X0),sK0) | r1_tarski(sK1,X0)) )),
% 1.31/0.55    inference(resolution,[],[f62,f36])).
% 1.31/0.55  fof(f62,plain,(
% 1.31/0.55    ( ! [X0,X1] : (~r1_tarski(sK0,X1) | r2_hidden(sK2(sK1,X0),X1) | r1_tarski(sK1,X0)) )),
% 1.31/0.55    inference(resolution,[],[f60,f18])).
% 1.31/0.55  fof(f18,plain,(
% 1.31/0.55    r1_tarski(k1_relat_1(sK1),sK0)),
% 1.31/0.55    inference(cnf_transformation,[],[f10])).
% 1.31/0.55  fof(f60,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k1_relat_1(sK1),X1) | r1_tarski(sK1,X0) | r2_hidden(sK2(sK1,X0),X2) | ~r1_tarski(X1,X2)) )),
% 1.31/0.55    inference(resolution,[],[f56,f28])).
% 1.31/0.55  fof(f56,plain,(
% 1.31/0.55    ( ! [X0,X1] : (r2_hidden(sK2(sK1,X0),X1) | r1_tarski(sK1,X0) | ~r1_tarski(k1_relat_1(sK1),X1)) )),
% 1.31/0.55    inference(resolution,[],[f53,f28])).
% 1.31/0.55  fof(f53,plain,(
% 1.31/0.55    ( ! [X3] : (r2_hidden(sK2(sK1,X3),k1_relat_1(sK1)) | r1_tarski(sK1,X3)) )),
% 1.31/0.55    inference(subsumption_resolution,[],[f51,f17])).
% 1.31/0.55  fof(f51,plain,(
% 1.31/0.55    ( ! [X3] : (r1_tarski(sK1,X3) | ~v1_relat_1(sK1) | r2_hidden(sK2(sK1,X3),k1_relat_1(sK1))) )),
% 1.31/0.55    inference(resolution,[],[f48,f31])).
% 1.31/0.55  fof(f31,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X0,k1_relat_1(X2))) )),
% 1.31/0.55    inference(cnf_transformation,[],[f15])).
% 1.31/0.55  fof(f15,plain,(
% 1.31/0.55    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 1.31/0.55    inference(flattening,[],[f14])).
% 1.31/0.55  fof(f14,plain,(
% 1.31/0.55    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 1.31/0.55    inference(ennf_transformation,[],[f4])).
% 1.31/0.55  fof(f4,axiom,(
% 1.31/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 1.31/0.55  fof(f48,plain,(
% 1.31/0.55    ( ! [X0] : (r2_hidden(k4_tarski(sK2(sK1,X0),sK3(sK1,X0)),sK1) | r1_tarski(sK1,X0)) )),
% 1.31/0.55    inference(resolution,[],[f21,f17])).
% 1.31/0.55  fof(f21,plain,(
% 1.31/0.55    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 1.31/0.55    inference(cnf_transformation,[],[f11])).
% 1.31/0.55  fof(f99,plain,(
% 1.31/0.55    ( ! [X0,X1] : (~r2_hidden(sK2(sK1,X0),X1) | r2_hidden(k4_tarski(sK2(sK1,X0),sK3(sK1,X0)),k5_relat_1(k6_relat_1(X1),sK1)) | r1_tarski(sK1,X0)) )),
% 1.31/0.55    inference(resolution,[],[f98,f48])).
% 1.31/0.55  fof(f98,plain,(
% 1.31/0.55    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X2),sK1) | ~r2_hidden(X0,X1) | r2_hidden(k4_tarski(X0,X2),k5_relat_1(k6_relat_1(X1),sK1))) )),
% 1.31/0.55    inference(resolution,[],[f35,f17])).
% 1.31/0.55  fof(f35,plain,(
% 1.31/0.55    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X3) | ~r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),X3) | r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3))) )),
% 1.31/0.55    inference(cnf_transformation,[],[f16])).
% 1.31/0.55  fof(f16,plain,(
% 1.31/0.55    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))) | ~v1_relat_1(X3))),
% 1.31/0.55    inference(ennf_transformation,[],[f5])).
% 1.31/0.55  fof(f5,axiom,(
% 1.31/0.55    ! [X0,X1,X2,X3] : (v1_relat_1(X3) => (r2_hidden(k4_tarski(X0,X1),k5_relat_1(k6_relat_1(X2),X3)) <=> (r2_hidden(k4_tarski(X0,X1),X3) & r2_hidden(X0,X2))))),
% 1.31/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_relat_1)).
% 1.31/0.55  % SZS output end Proof for theBenchmark
% 1.31/0.55  % (401)------------------------------
% 1.31/0.55  % (401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (401)Termination reason: Refutation
% 1.31/0.55  
% 1.31/0.55  % (401)Memory used [KB]: 6268
% 1.31/0.55  % (401)Time elapsed: 0.126 s
% 1.31/0.55  % (401)------------------------------
% 1.31/0.55  % (401)------------------------------
% 1.31/0.55  % (416)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.31/0.55  % (406)Refutation not found, incomplete strategy% (406)------------------------------
% 1.31/0.55  % (406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.31/0.55  % (389)Success in time 0.184 s
%------------------------------------------------------------------------------
