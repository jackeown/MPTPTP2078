%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   25 (  35 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :   10
%              Number of atoms          :   66 (  88 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,plain,(
    $false ),
    inference(resolution,[],[f39,f13])).

fof(f13,plain,(
    ~ r1_tarski(k9_relat_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).

fof(f39,plain,(
    ! [X0] : r1_tarski(k9_relat_1(sK1,X0),k2_relat_1(sK1)) ),
    inference(duplicate_literal_removal,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( r1_tarski(k9_relat_1(sK1,X0),k2_relat_1(sK1))
      | r1_tarski(k9_relat_1(sK1,X0),k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f36,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

% (17013)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f6,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) )
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f36,plain,(
    ! [X4,X3] :
      ( r2_hidden(sK5(k9_relat_1(sK1,X3),X4),k2_relat_1(sK1))
      | r1_tarski(k9_relat_1(sK1,X3),X4) ) ),
    inference(subsumption_resolution,[],[f33,f12])).

fof(f12,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f33,plain,(
    ! [X4,X3] :
      ( r1_tarski(k9_relat_1(sK1,X3),X4)
      | ~ v1_relat_1(sK1)
      | r2_hidden(sK5(k9_relat_1(sK1,X3),X4),k2_relat_1(sK1)) ) ),
    inference(resolution,[],[f30,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2)
      | r2_hidden(X1,k2_relat_1(X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(k4_tarski(sK3(sK1,X0,sK5(k9_relat_1(sK1,X0),X1)),sK5(k9_relat_1(sK1,X0),X1)),sK1)
      | r1_tarski(k9_relat_1(sK1,X0),X1) ) ),
    inference(resolution,[],[f29,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

% (17038)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK1,X0))
      | r2_hidden(k4_tarski(sK3(sK1,X0,X1),X1),sK1) ) ),
    inference(resolution,[],[f26,f12])).

fof(f26,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK3(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

% (17035)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (17035)Refutation not found, incomplete strategy% (17035)------------------------------
% (17035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17031)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (17035)Termination reason: Refutation not found, incomplete strategy

% (17035)Memory used [KB]: 10618
% (17035)Time elapsed: 0.163 s
% (17035)------------------------------
% (17035)------------------------------
% (17017)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% (17018)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (17029)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:01:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.55  % (17023)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (17015)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.58  % (17015)Refutation not found, incomplete strategy% (17015)------------------------------
% 0.21/0.58  % (17015)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (17015)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (17015)Memory used [KB]: 10618
% 0.21/0.58  % (17015)Time elapsed: 0.142 s
% 0.21/0.58  % (17015)------------------------------
% 0.21/0.58  % (17015)------------------------------
% 0.21/0.59  % (17019)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.59  % (17019)Refutation found. Thanks to Tanya!
% 0.21/0.59  % SZS status Theorem for theBenchmark
% 0.21/0.59  % SZS output start Proof for theBenchmark
% 0.21/0.59  fof(f40,plain,(
% 0.21/0.59    $false),
% 0.21/0.59    inference(resolution,[],[f39,f13])).
% 0.21/0.59  fof(f13,plain,(
% 0.21/0.59    ~r1_tarski(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),
% 0.21/0.59    inference(cnf_transformation,[],[f7])).
% 0.21/0.59  fof(f7,plain,(
% 0.21/0.59    ? [X0,X1] : (~r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) & v1_relat_1(X1))),
% 0.21/0.59    inference(ennf_transformation,[],[f5])).
% 0.21/0.59  fof(f5,negated_conjecture,(
% 0.21/0.59    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.21/0.59    inference(negated_conjecture,[],[f4])).
% 0.21/0.59  fof(f4,conjecture,(
% 0.21/0.59    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_relat_1)).
% 0.21/0.59  fof(f39,plain,(
% 0.21/0.59    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,X0),k2_relat_1(sK1))) )),
% 0.21/0.59    inference(duplicate_literal_removal,[],[f38])).
% 0.21/0.59  fof(f38,plain,(
% 0.21/0.59    ( ! [X0] : (r1_tarski(k9_relat_1(sK1,X0),k2_relat_1(sK1)) | r1_tarski(k9_relat_1(sK1,X0),k2_relat_1(sK1))) )),
% 0.21/0.59    inference(resolution,[],[f36,f21])).
% 0.21/0.59  fof(f21,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f9])).
% 0.21/0.59  fof(f9,plain,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 0.21/0.59    inference(ennf_transformation,[],[f6])).
% 0.21/0.59  % (17013)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.59  fof(f6,plain,(
% 0.21/0.59    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 0.21/0.59    inference(unused_predicate_definition_removal,[],[f1])).
% 0.21/0.59  fof(f1,axiom,(
% 0.21/0.59    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.59  fof(f36,plain,(
% 0.21/0.59    ( ! [X4,X3] : (r2_hidden(sK5(k9_relat_1(sK1,X3),X4),k2_relat_1(sK1)) | r1_tarski(k9_relat_1(sK1,X3),X4)) )),
% 0.21/0.59    inference(subsumption_resolution,[],[f33,f12])).
% 0.21/0.59  fof(f12,plain,(
% 0.21/0.59    v1_relat_1(sK1)),
% 0.21/0.59    inference(cnf_transformation,[],[f7])).
% 0.21/0.59  fof(f33,plain,(
% 0.21/0.59    ( ! [X4,X3] : (r1_tarski(k9_relat_1(sK1,X3),X4) | ~v1_relat_1(sK1) | r2_hidden(sK5(k9_relat_1(sK1,X3),X4),k2_relat_1(sK1))) )),
% 0.21/0.59    inference(resolution,[],[f30,f23])).
% 0.21/0.59  fof(f23,plain,(
% 0.21/0.59    ( ! [X2,X0,X1] : (~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2) | r2_hidden(X1,k2_relat_1(X2))) )),
% 0.21/0.59    inference(cnf_transformation,[],[f11])).
% 0.21/0.59  fof(f11,plain,(
% 0.21/0.59    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 0.21/0.59    inference(flattening,[],[f10])).
% 0.21/0.59  fof(f10,plain,(
% 0.21/0.59    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 0.21/0.59    inference(ennf_transformation,[],[f3])).
% 0.21/0.59  fof(f3,axiom,(
% 0.21/0.59    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 0.21/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_relat_1)).
% 0.21/0.59  fof(f30,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r2_hidden(k4_tarski(sK3(sK1,X0,sK5(k9_relat_1(sK1,X0),X1)),sK5(k9_relat_1(sK1,X0),X1)),sK1) | r1_tarski(k9_relat_1(sK1,X0),X1)) )),
% 0.21/0.59    inference(resolution,[],[f29,f20])).
% 0.21/0.59  fof(f20,plain,(
% 0.21/0.59    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.59    inference(cnf_transformation,[],[f9])).
% 0.21/0.59  % (17038)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.59  fof(f29,plain,(
% 0.21/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k9_relat_1(sK1,X0)) | r2_hidden(k4_tarski(sK3(sK1,X0,X1),X1),sK1)) )),
% 0.21/0.59    inference(resolution,[],[f26,f12])).
% 0.21/0.59  fof(f26,plain,(
% 0.21/0.59    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1,X3),X3),X0) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.21/0.59    inference(equality_resolution,[],[f17])).
% 0.21/0.59  fof(f17,plain,(
% 0.21/0.59    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1,X3),X3),X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.59    inference(cnf_transformation,[],[f8])).
% 0.21/0.59  fof(f8,plain,(
% 0.21/0.59    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.59    inference(ennf_transformation,[],[f2])).
% 0.21/0.59  % (17035)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.60  % (17035)Refutation not found, incomplete strategy% (17035)------------------------------
% 0.21/0.60  % (17035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (17031)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.60  % (17035)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.60  
% 0.21/0.60  % (17035)Memory used [KB]: 10618
% 0.21/0.60  % (17035)Time elapsed: 0.163 s
% 0.21/0.60  % (17035)------------------------------
% 0.21/0.60  % (17035)------------------------------
% 0.21/0.60  % (17017)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.60  % (17018)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.76/0.60  % (17029)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.76/0.60  fof(f2,axiom,(
% 1.76/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 1.76/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 1.76/0.60  % SZS output end Proof for theBenchmark
% 1.76/0.60  % (17019)------------------------------
% 1.76/0.60  % (17019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.60  % (17019)Termination reason: Refutation
% 1.76/0.60  
% 1.76/0.60  % (17019)Memory used [KB]: 6140
% 1.76/0.60  % (17019)Time elapsed: 0.161 s
% 1.76/0.60  % (17019)------------------------------
% 1.76/0.60  % (17019)------------------------------
% 1.76/0.60  % (17024)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.76/0.61  % (17012)Success in time 0.241 s
%------------------------------------------------------------------------------
