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
% DateTime   : Thu Dec  3 12:49:03 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.30s
% Verified   : 
% Statistics : Number of formulae       :   47 ( 138 expanded)
%              Number of leaves         :    4 (  27 expanded)
%              Depth                    :   17
%              Number of atoms          :  133 ( 437 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f175,plain,(
    $false ),
    inference(subsumption_resolution,[],[f171,f14])).

fof(f14,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

fof(f171,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f170,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | v1_relat_1(k8_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k8_relat_1(X0,X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => v1_relat_1(k8_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).

fof(f170,plain,(
    ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f166,f11])).

fof(f11,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f166,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f151,f18])).

fof(f151,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f115,f121])).

fof(f121,plain,(
    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK2) ),
    inference(resolution,[],[f120,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(k4_tarski(X0,X1),sK2) ) ),
    inference(subsumption_resolution,[],[f54,f14])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(sK1)
      | ~ r2_hidden(k4_tarski(X0,X1),sK1)
      | r2_hidden(k4_tarski(X0,X1),sK2) ) ),
    inference(resolution,[],[f12,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X2,X3),X0)
      | r2_hidden(k4_tarski(X2,X3),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X1)
              | ~ r2_hidden(k4_tarski(X2,X3),X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_tarski(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X2,X3),X0)
             => r2_hidden(k4_tarski(X2,X3),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

fof(f12,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f120,plain,(
    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK1) ),
    inference(subsumption_resolution,[],[f116,f14])).

fof(f116,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK1)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f91,f18])).

fof(f91,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK1) ),
    inference(subsumption_resolution,[],[f80,f14])).

fof(f80,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK1) ),
    inference(resolution,[],[f78,f26])).

fof(f26,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,X4),X1)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

% (1348)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (1355)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% (1348)Refutation not found, incomplete strategy% (1348)------------------------------
% (1348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1348)Termination reason: Refutation not found, incomplete strategy

% (1348)Memory used [KB]: 10490
% (1348)Time elapsed: 0.081 s
% (1348)------------------------------
% (1348)------------------------------
% (1365)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (1347)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% (1358)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% (1354)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% (1353)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% (1356)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( k8_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X1)
                  & r2_hidden(X4,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).

fof(f78,plain,(
    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f74,f14])).

fof(f74,plain,
    ( r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f56,f18])).

fof(f56,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f13,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f13,plain,(
    ~ r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f115,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f114,f96])).

fof(f96,plain,(
    r2_hidden(sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f92,f14])).

fof(f92,plain,
    ( r2_hidden(sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f90,f18])).

fof(f90,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | r2_hidden(sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK0) ),
    inference(subsumption_resolution,[],[f79,f14])).

fof(f79,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | r2_hidden(sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK0) ),
    inference(resolution,[],[f78,f27])).

fof(f27,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f114,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ r2_hidden(sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK0)
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK2) ),
    inference(subsumption_resolution,[],[f104,f11])).

fof(f104,plain,
    ( ~ v1_relat_1(k8_relat_1(sK0,sK1))
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2))
    | ~ r2_hidden(sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK0)
    | ~ r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK2) ),
    inference(resolution,[],[f57,f25])).

fof(f25,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(k8_relat_1(X0,X1))
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | ~ r2_hidden(X4,X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X1)
      | r2_hidden(k4_tarski(X3,X4),X2)
      | k8_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,
    ( ~ r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK2))
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f13,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:13:39 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (1366)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.47  % (1349)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.48  % (1367)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (1352)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (1351)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.49  % (1361)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (1357)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (1350)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (1362)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (1361)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f171,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    v1_relat_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : (~r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) & r1_tarski(X1,X2) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0,X1] : (? [X2] : ((~r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)) & r1_tarski(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k8_relat_1(X0,X1),k8_relat_1(X0,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    ~v1_relat_1(sK1)),
% 0.21/0.49    inference(resolution,[],[f170,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | v1_relat_1(k8_relat_1(X0,X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(k8_relat_1(X0,X1)) | ~v1_relat_1(X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (v1_relat_1(X1) => v1_relat_1(k8_relat_1(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relat_1)).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f166,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    v1_relat_1(sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    ~v1_relat_1(k8_relat_1(sK0,sK1)) | ~v1_relat_1(sK2)),
% 0.21/0.49    inference(resolution,[],[f151,f18])).
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.21/0.49    inference(resolution,[],[f115,f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK2)),
% 0.21/0.49    inference(resolution,[],[f120,f55])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(k4_tarski(X0,X1),sK2)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f54,f14])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_relat_1(sK1) | ~r2_hidden(k4_tarski(X0,X1),sK1) | r2_hidden(k4_tarski(X0,X1),sK2)) )),
% 0.21/0.49    inference(resolution,[],[f12,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X2,X3),X0) | r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X1) | ~r2_hidden(k4_tarski(X2,X3),X0))) | ~v1_relat_1(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_tarski(X0,X1) <=> ! [X2,X3] : (r2_hidden(k4_tarski(X2,X3),X0) => r2_hidden(k4_tarski(X2,X3),X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f7])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f116,f14])).
% 0.21/0.49  fof(f116,plain,(
% 0.21/0.49    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK1) | ~v1_relat_1(sK1)),
% 0.21/0.49    inference(resolution,[],[f91,f18])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ~v1_relat_1(k8_relat_1(sK0,sK1)) | r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f80,f14])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ~v1_relat_1(sK1) | ~v1_relat_1(k8_relat_1(sK0,sK1)) | r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK1)),
% 0.21/0.49    inference(resolution,[],[f78,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1)) | r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) )),
% 0.21/0.49    inference(equality_resolution,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X3,X4),X1) | ~r2_hidden(k4_tarski(X3,X4),X2) | k8_relat_1(X0,X1) != X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  % (1348)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (1355)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (1348)Refutation not found, incomplete strategy% (1348)------------------------------
% 0.21/0.50  % (1348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (1348)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (1348)Memory used [KB]: 10490
% 0.21/0.50  % (1348)Time elapsed: 0.081 s
% 0.21/0.50  % (1348)------------------------------
% 0.21/0.50  % (1348)------------------------------
% 0.21/0.50  % (1365)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (1347)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (1358)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (1354)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (1353)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.30/0.51  % (1356)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.30/0.51  fof(f10,plain,(
% 1.30/0.51    ! [X0,X1] : (! [X2] : ((k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 1.30/0.51    inference(ennf_transformation,[],[f1])).
% 1.30/0.51  fof(f1,axiom,(
% 1.30/0.51    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (k8_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X1) & r2_hidden(X4,X0))))))),
% 1.30/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_relat_1)).
% 1.30/0.51  fof(f78,plain,(
% 1.30/0.51    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK1))),
% 1.30/0.51    inference(subsumption_resolution,[],[f74,f14])).
% 1.30/0.51  fof(f74,plain,(
% 1.30/0.51    r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK1)) | ~v1_relat_1(sK1)),
% 1.30/0.51    inference(resolution,[],[f56,f18])).
% 1.30/0.51  fof(f56,plain,(
% 1.30/0.51    ~v1_relat_1(k8_relat_1(sK0,sK1)) | r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK1))),
% 1.30/0.51    inference(resolution,[],[f13,f16])).
% 1.30/0.51  fof(f16,plain,(
% 1.30/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0) | r1_tarski(X0,X1)) )),
% 1.30/0.51    inference(cnf_transformation,[],[f8])).
% 1.30/0.51  fof(f13,plain,(
% 1.30/0.51    ~r1_tarski(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),
% 1.30/0.51    inference(cnf_transformation,[],[f7])).
% 1.30/0.51  fof(f115,plain,(
% 1.30/0.51    ~r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK2) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 1.30/0.51    inference(subsumption_resolution,[],[f114,f96])).
% 1.30/0.51  fof(f96,plain,(
% 1.30/0.51    r2_hidden(sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK0)),
% 1.30/0.51    inference(subsumption_resolution,[],[f92,f14])).
% 1.30/0.51  fof(f92,plain,(
% 1.30/0.51    r2_hidden(sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK0) | ~v1_relat_1(sK1)),
% 1.30/0.51    inference(resolution,[],[f90,f18])).
% 1.30/0.51  fof(f90,plain,(
% 1.30/0.51    ~v1_relat_1(k8_relat_1(sK0,sK1)) | r2_hidden(sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK0)),
% 1.30/0.51    inference(subsumption_resolution,[],[f79,f14])).
% 1.30/0.51  fof(f79,plain,(
% 1.30/0.51    ~v1_relat_1(sK1) | ~v1_relat_1(k8_relat_1(sK0,sK1)) | r2_hidden(sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK0)),
% 1.30/0.51    inference(resolution,[],[f78,f27])).
% 1.30/0.51  fof(f27,plain,(
% 1.30/0.51    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1)) | r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) )),
% 1.30/0.51    inference(equality_resolution,[],[f22])).
% 1.30/0.51  fof(f22,plain,(
% 1.30/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X2) | k8_relat_1(X0,X1) != X2) )),
% 1.30/0.51    inference(cnf_transformation,[],[f10])).
% 1.30/0.51  fof(f114,plain,(
% 1.30/0.51    ~v1_relat_1(k8_relat_1(sK0,sK1)) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~r2_hidden(sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK0) | ~r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK2)),
% 1.30/0.51    inference(subsumption_resolution,[],[f104,f11])).
% 1.30/0.51  fof(f104,plain,(
% 1.30/0.51    ~v1_relat_1(k8_relat_1(sK0,sK1)) | ~v1_relat_1(sK2) | ~v1_relat_1(k8_relat_1(sK0,sK2)) | ~r2_hidden(sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK0) | ~r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),sK2)),
% 1.30/0.51    inference(resolution,[],[f57,f25])).
% 1.30/0.51  fof(f25,plain,(
% 1.30/0.51    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(k8_relat_1(X0,X1)) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X1) | r2_hidden(k4_tarski(X3,X4),k8_relat_1(X0,X1))) )),
% 1.30/0.51    inference(equality_resolution,[],[f24])).
% 1.30/0.51  fof(f24,plain,(
% 1.30/0.51    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X1) | ~v1_relat_1(X2) | ~r2_hidden(X4,X0) | ~r2_hidden(k4_tarski(X3,X4),X1) | r2_hidden(k4_tarski(X3,X4),X2) | k8_relat_1(X0,X1) != X2) )),
% 1.30/0.51    inference(cnf_transformation,[],[f10])).
% 1.30/0.51  fof(f57,plain,(
% 1.30/0.51    ~r2_hidden(k4_tarski(sK3(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2)),sK4(k8_relat_1(sK0,sK1),k8_relat_1(sK0,sK2))),k8_relat_1(sK0,sK2)) | ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 1.30/0.51    inference(resolution,[],[f13,f17])).
% 1.30/0.51  fof(f17,plain,(
% 1.30/0.51    ( ! [X0,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) | r1_tarski(X0,X1)) )),
% 1.30/0.51    inference(cnf_transformation,[],[f8])).
% 1.30/0.51  % SZS output end Proof for theBenchmark
% 1.30/0.51  % (1361)------------------------------
% 1.30/0.51  % (1361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.30/0.51  % (1361)Termination reason: Refutation
% 1.30/0.51  
% 1.30/0.51  % (1361)Memory used [KB]: 1663
% 1.30/0.51  % (1361)Time elapsed: 0.086 s
% 1.30/0.51  % (1361)------------------------------
% 1.30/0.51  % (1361)------------------------------
% 1.30/0.51  % (1364)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.30/0.51  % (1346)Success in time 0.162 s
%------------------------------------------------------------------------------
