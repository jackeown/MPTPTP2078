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
% DateTime   : Thu Dec  3 12:51:04 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   50 (  95 expanded)
%              Number of leaves         :    8 (  19 expanded)
%              Depth                    :   15
%              Number of atoms          :  118 ( 275 expanded)
%              Number of equality atoms :   34 (  70 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f139,plain,(
    $false ),
    inference(subsumption_resolution,[],[f138,f21])).

fof(f21,plain,(
    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
          & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0))
          & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
             => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))
           => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_relat_1)).

fof(f138,plain,(
    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0)) ),
    inference(superposition,[],[f101,f136])).

fof(f136,plain,(
    sK1 = k8_relat_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f135,f22])).

fof(f22,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f135,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | ~ v1_relat_1(sK1) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,
    ( sK1 = k8_relat_1(sK0,sK1)
    | ~ v1_relat_1(sK1)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f132,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = X1
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r1_tarski(k2_relat_1(X1),X0)
       => k8_relat_1(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

fof(f132,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | sK1 = k8_relat_1(sK0,sK1) ),
    inference(resolution,[],[f119,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f119,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k2_relat_1(sK1),X0),sK0)
      | sK1 = k8_relat_1(X0,sK1) ) ),
    inference(resolution,[],[f76,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1)))
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f19,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k2_relat_1(sK1),X0),k1_relat_1(k7_relat_1(sK2,sK0)))
      | sK1 = k8_relat_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f74,f22])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(sK3(k2_relat_1(sK1),X0),k1_relat_1(k7_relat_1(sK2,sK0)))
      | ~ v1_relat_1(sK1)
      | sK1 = k8_relat_1(X0,sK1) ) ),
    inference(resolution,[],[f63,f27])).

fof(f63,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(sK1),X0)
      | r2_hidden(sK3(k2_relat_1(sK1),X0),k1_relat_1(k7_relat_1(sK2,sK0))) ) ),
    inference(resolution,[],[f45,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_relat_1(sK1))
      | r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,sK0))) ) ),
    inference(resolution,[],[f20,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f20,plain,(
    r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f101,plain,(
    ! [X2] : k5_relat_1(k8_relat_1(X2,sK1),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X2)) ),
    inference(forward_demodulation,[],[f99,f37])).

fof(f37,plain,(
    ! [X6] : k7_relat_1(sK2,X6) = k5_relat_1(k6_relat_1(X6),sK2) ),
    inference(resolution,[],[f19,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f99,plain,(
    ! [X2] : k5_relat_1(sK1,k5_relat_1(k6_relat_1(X2),sK2)) = k5_relat_1(k8_relat_1(X2,sK1),sK2) ),
    inference(resolution,[],[f58,f19])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k5_relat_1(sK1,k5_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k8_relat_1(X0,sK1),X1) ) ),
    inference(subsumption_resolution,[],[f57,f22])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k5_relat_1(sK1,k5_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k8_relat_1(X0,sK1),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(subsumption_resolution,[],[f56,f23])).

fof(f23,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f56,plain,(
    ! [X0,X1] :
      ( k5_relat_1(sK1,k5_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k8_relat_1(X0,sK1),X1)
      | ~ v1_relat_1(k6_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(sK1) ) ),
    inference(superposition,[],[f24,f43])).

fof(f43,plain,(
    ! [X7] : k8_relat_1(X7,sK1) = k5_relat_1(sK1,k6_relat_1(X7)) ),
    inference(resolution,[],[f22,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:57:42 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.50  % (6470)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.51  % (6473)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.19/0.51  % (6479)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.19/0.51  % (6475)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.51  % (6481)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.19/0.51  % (6478)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.19/0.51  % (6467)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (6488)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.51  % (6465)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.19/0.51  % (6467)Refutation not found, incomplete strategy% (6467)------------------------------
% 0.19/0.51  % (6467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (6480)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.52  % (6468)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.19/0.52  % (6467)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (6467)Memory used [KB]: 10746
% 0.19/0.52  % (6467)Time elapsed: 0.115 s
% 0.19/0.52  % (6467)------------------------------
% 0.19/0.52  % (6467)------------------------------
% 0.19/0.52  % (6491)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.19/0.52  % (6493)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.19/0.52  % (6473)Refutation not found, incomplete strategy% (6473)------------------------------
% 0.19/0.52  % (6473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (6486)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.19/0.52  % (6469)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.19/0.52  % (6471)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.19/0.52  % (6475)Refutation not found, incomplete strategy% (6475)------------------------------
% 0.19/0.52  % (6475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (6472)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.19/0.52  % (6473)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.52  
% 0.19/0.52  % (6473)Memory used [KB]: 10746
% 0.19/0.52  % (6473)Time elapsed: 0.129 s
% 0.19/0.52  % (6473)------------------------------
% 0.19/0.52  % (6473)------------------------------
% 0.19/0.52  % (6486)Refutation found. Thanks to Tanya!
% 0.19/0.52  % SZS status Theorem for theBenchmark
% 0.19/0.52  % SZS output start Proof for theBenchmark
% 0.19/0.52  fof(f139,plain,(
% 0.19/0.52    $false),
% 0.19/0.52    inference(subsumption_resolution,[],[f138,f21])).
% 0.19/0.52  fof(f21,plain,(
% 0.19/0.52    k5_relat_1(sK1,sK2) != k5_relat_1(sK1,k7_relat_1(sK2,sK0))),
% 0.19/0.52    inference(cnf_transformation,[],[f11])).
% 0.19/0.52  fof(f11,plain,(
% 0.19/0.52    ? [X0,X1] : (? [X2] : (k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f10])).
% 0.19/0.52  fof(f10,plain,(
% 0.19/0.52    ? [X0,X1] : (? [X2] : ((k5_relat_1(X1,X2) != k5_relat_1(X1,k7_relat_1(X2,X0)) & r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0)))) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f9])).
% 0.19/0.52  fof(f9,negated_conjecture,(
% 0.19/0.52    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)))))),
% 0.19/0.52    inference(negated_conjecture,[],[f8])).
% 0.19/0.52  fof(f8,conjecture,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(k2_relat_1(X1),k1_relat_1(k7_relat_1(X2,X0))) => k5_relat_1(X1,X2) = k5_relat_1(X1,k7_relat_1(X2,X0)))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t200_relat_1)).
% 0.19/0.52  fof(f138,plain,(
% 0.19/0.52    k5_relat_1(sK1,sK2) = k5_relat_1(sK1,k7_relat_1(sK2,sK0))),
% 0.19/0.52    inference(superposition,[],[f101,f136])).
% 0.19/0.52  fof(f136,plain,(
% 0.19/0.52    sK1 = k8_relat_1(sK0,sK1)),
% 0.19/0.52    inference(subsumption_resolution,[],[f135,f22])).
% 0.19/0.52  fof(f22,plain,(
% 0.19/0.52    v1_relat_1(sK1)),
% 0.19/0.52    inference(cnf_transformation,[],[f11])).
% 0.19/0.52  fof(f135,plain,(
% 0.19/0.52    sK1 = k8_relat_1(sK0,sK1) | ~v1_relat_1(sK1)),
% 0.19/0.52    inference(duplicate_literal_removal,[],[f133])).
% 0.19/0.52  fof(f133,plain,(
% 0.19/0.52    sK1 = k8_relat_1(sK0,sK1) | ~v1_relat_1(sK1) | sK1 = k8_relat_1(sK0,sK1)),
% 0.19/0.52    inference(resolution,[],[f132,f27])).
% 0.19/0.52  fof(f27,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1) | k8_relat_1(X0,X1) = X1) )),
% 0.19/0.52    inference(cnf_transformation,[],[f16])).
% 0.19/0.52  fof(f16,plain,(
% 0.19/0.52    ! [X0,X1] : (k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(flattening,[],[f15])).
% 0.19/0.52  fof(f15,plain,(
% 0.19/0.52    ! [X0,X1] : ((k8_relat_1(X0,X1) = X1 | ~r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f4])).
% 0.19/0.52  fof(f4,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => (r1_tarski(k2_relat_1(X1),X0) => k8_relat_1(X0,X1) = X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).
% 0.19/0.52  fof(f132,plain,(
% 0.19/0.52    r1_tarski(k2_relat_1(sK1),sK0) | sK1 = k8_relat_1(sK0,sK1)),
% 0.19/0.52    inference(resolution,[],[f119,f30])).
% 0.19/0.52  fof(f30,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f17])).
% 0.19/0.52  fof(f17,plain,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.19/0.52    inference(ennf_transformation,[],[f1])).
% 0.19/0.52  fof(f1,axiom,(
% 0.19/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.19/0.52  fof(f119,plain,(
% 0.19/0.52    ( ! [X0] : (r2_hidden(sK3(k2_relat_1(sK1),X0),sK0) | sK1 = k8_relat_1(X0,sK1)) )),
% 0.19/0.52    inference(resolution,[],[f76,f34])).
% 0.19/0.52  fof(f34,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,X1))) | r2_hidden(X0,X1)) )),
% 0.19/0.52    inference(resolution,[],[f19,f31])).
% 0.19/0.52  fof(f31,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f18])).
% 0.19/0.52  fof(f18,plain,(
% 0.19/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.19/0.52    inference(ennf_transformation,[],[f6])).
% 0.19/0.52  fof(f6,axiom,(
% 0.19/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.19/0.52  fof(f19,plain,(
% 0.19/0.52    v1_relat_1(sK2)),
% 0.19/0.52    inference(cnf_transformation,[],[f11])).
% 0.19/0.52  fof(f76,plain,(
% 0.19/0.52    ( ! [X0] : (r2_hidden(sK3(k2_relat_1(sK1),X0),k1_relat_1(k7_relat_1(sK2,sK0))) | sK1 = k8_relat_1(X0,sK1)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f74,f22])).
% 0.19/0.52  fof(f74,plain,(
% 0.19/0.52    ( ! [X0] : (r2_hidden(sK3(k2_relat_1(sK1),X0),k1_relat_1(k7_relat_1(sK2,sK0))) | ~v1_relat_1(sK1) | sK1 = k8_relat_1(X0,sK1)) )),
% 0.19/0.52    inference(resolution,[],[f63,f27])).
% 0.19/0.52  fof(f63,plain,(
% 0.19/0.52    ( ! [X0] : (r1_tarski(k2_relat_1(sK1),X0) | r2_hidden(sK3(k2_relat_1(sK1),X0),k1_relat_1(k7_relat_1(sK2,sK0)))) )),
% 0.19/0.52    inference(resolution,[],[f45,f29])).
% 0.19/0.52  fof(f29,plain,(
% 0.19/0.52    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f17])).
% 0.19/0.52  fof(f45,plain,(
% 0.19/0.52    ( ! [X0] : (~r2_hidden(X0,k2_relat_1(sK1)) | r2_hidden(X0,k1_relat_1(k7_relat_1(sK2,sK0)))) )),
% 0.19/0.52    inference(resolution,[],[f20,f28])).
% 0.19/0.52  fof(f28,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f17])).
% 0.19/0.52  fof(f20,plain,(
% 0.19/0.52    r1_tarski(k2_relat_1(sK1),k1_relat_1(k7_relat_1(sK2,sK0)))),
% 0.19/0.52    inference(cnf_transformation,[],[f11])).
% 0.19/0.52  fof(f101,plain,(
% 0.19/0.52    ( ! [X2] : (k5_relat_1(k8_relat_1(X2,sK1),sK2) = k5_relat_1(sK1,k7_relat_1(sK2,X2))) )),
% 0.19/0.52    inference(forward_demodulation,[],[f99,f37])).
% 0.19/0.52  fof(f37,plain,(
% 0.19/0.52    ( ! [X6] : (k7_relat_1(sK2,X6) = k5_relat_1(k6_relat_1(X6),sK2)) )),
% 0.19/0.52    inference(resolution,[],[f19,f26])).
% 0.19/0.52  fof(f26,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f14])).
% 0.19/0.52  fof(f14,plain,(
% 0.19/0.52    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f7])).
% 0.19/0.52  fof(f7,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.19/0.52  fof(f99,plain,(
% 0.19/0.52    ( ! [X2] : (k5_relat_1(sK1,k5_relat_1(k6_relat_1(X2),sK2)) = k5_relat_1(k8_relat_1(X2,sK1),sK2)) )),
% 0.19/0.52    inference(resolution,[],[f58,f19])).
% 0.19/0.52  fof(f58,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k5_relat_1(sK1,k5_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k8_relat_1(X0,sK1),X1)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f57,f22])).
% 0.19/0.52  fof(f57,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k5_relat_1(sK1,k5_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k8_relat_1(X0,sK1),X1) | ~v1_relat_1(X1) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(subsumption_resolution,[],[f56,f23])).
% 0.19/0.52  fof(f23,plain,(
% 0.19/0.52    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f2])).
% 0.19/0.52  fof(f2,axiom,(
% 0.19/0.52    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.19/0.52  fof(f56,plain,(
% 0.19/0.52    ( ! [X0,X1] : (k5_relat_1(sK1,k5_relat_1(k6_relat_1(X0),X1)) = k5_relat_1(k8_relat_1(X0,sK1),X1) | ~v1_relat_1(k6_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(sK1)) )),
% 0.19/0.52    inference(superposition,[],[f24,f43])).
% 0.19/0.52  fof(f43,plain,(
% 0.19/0.52    ( ! [X7] : (k8_relat_1(X7,sK1) = k5_relat_1(sK1,k6_relat_1(X7))) )),
% 0.19/0.52    inference(resolution,[],[f22,f25])).
% 0.19/0.52  fof(f25,plain,(
% 0.19/0.52    ( ! [X0,X1] : (~v1_relat_1(X1) | k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0))) )),
% 0.19/0.52    inference(cnf_transformation,[],[f13])).
% 0.19/0.52  fof(f13,plain,(
% 0.19/0.52    ! [X0,X1] : (k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)) | ~v1_relat_1(X1))),
% 0.19/0.52    inference(ennf_transformation,[],[f3])).
% 0.19/0.52  fof(f3,axiom,(
% 0.19/0.52    ! [X0,X1] : (v1_relat_1(X1) => k8_relat_1(X0,X1) = k5_relat_1(X1,k6_relat_1(X0)))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).
% 0.19/0.52  fof(f24,plain,(
% 0.19/0.52    ( ! [X2,X0,X1] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | ~v1_relat_1(X0)) )),
% 0.19/0.52    inference(cnf_transformation,[],[f12])).
% 0.19/0.52  fof(f12,plain,(
% 0.19/0.52    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.19/0.52    inference(ennf_transformation,[],[f5])).
% 0.19/0.52  fof(f5,axiom,(
% 0.19/0.52    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 0.19/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 0.19/0.52  % SZS output end Proof for theBenchmark
% 0.19/0.52  % (6486)------------------------------
% 0.19/0.52  % (6486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.52  % (6486)Termination reason: Refutation
% 0.19/0.52  
% 0.19/0.52  % (6486)Memory used [KB]: 1791
% 0.19/0.52  % (6486)Time elapsed: 0.135 s
% 0.19/0.52  % (6486)------------------------------
% 0.19/0.52  % (6486)------------------------------
% 0.19/0.53  % (6464)Success in time 0.179 s
%------------------------------------------------------------------------------
