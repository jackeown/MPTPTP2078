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
% DateTime   : Thu Dec  3 12:48:19 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   31 (  56 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :   13
%              Number of atoms          :   80 ( 133 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(subsumption_resolution,[],[f87,f14])).

fof(f14,plain,(
    ~ r1_tarski(k7_relat_1(sK1,sK0),sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k7_relat_1(X1,X0),X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

fof(f87,plain,(
    r1_tarski(k7_relat_1(sK1,sK0),sK1) ),
    inference(resolution,[],[f86,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f86,plain,(
    r2_hidden(sK7(k7_relat_1(sK1,sK0),sK1),sK1) ),
    inference(subsumption_resolution,[],[f85,f14])).

fof(f85,plain,
    ( r2_hidden(sK7(k7_relat_1(sK1,sK0),sK1),sK1)
    | r1_tarski(k7_relat_1(sK1,sK0),sK1) ),
    inference(subsumption_resolution,[],[f84,f13])).

fof(f13,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f84,plain,
    ( r2_hidden(sK7(k7_relat_1(sK1,sK0),sK1),sK1)
    | ~ v1_relat_1(sK1)
    | r1_tarski(k7_relat_1(sK1,sK0),sK1) ),
    inference(resolution,[],[f82,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(k7_relat_1(sK1,sK0),sK1),k7_relat_1(X0,X1))
      | r2_hidden(sK7(k7_relat_1(sK1,sK0),sK1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f79,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK7(k7_relat_1(sK1,sK0),sK1),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | r2_hidden(sK7(k7_relat_1(sK1,sK0),sK1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f28,f78])).

fof(f78,plain,(
    sK7(k7_relat_1(sK1,sK0),sK1) = k4_tarski(sK5(sK7(k7_relat_1(sK1,sK0),sK1)),sK6(sK7(k7_relat_1(sK1,sK0),sK1))) ),
    inference(resolution,[],[f39,f14])).

fof(f39,plain,(
    ! [X2,X1] :
      ( r1_tarski(k7_relat_1(sK1,X1),X2)
      | sK7(k7_relat_1(sK1,X1),X2) = k4_tarski(sK5(sK7(k7_relat_1(sK1,X1),X2)),sK6(sK7(k7_relat_1(sK1,X1),X2))) ) ),
    inference(resolution,[],[f36,f25])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k7_relat_1(sK1,X1))
      | k4_tarski(sK5(X0),sK6(X0)) = X0 ) ),
    inference(resolution,[],[f33,f13])).

fof(f33,plain,(
    ! [X2,X3,X1] :
      ( ~ v1_relat_1(X2)
      | ~ r2_hidden(X1,k7_relat_1(X2,X3))
      | k4_tarski(sK5(X1),sK6(X1)) = X1 ) ),
    inference(resolution,[],[f21,f24])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k4_tarski(sK5(X1),sK6(X1)) = X1
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

fof(f28,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1))
      | ~ v1_relat_1(k7_relat_1(X0,X1))
      | r2_hidden(k4_tarski(X3,X4),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f19])).

fof(f19,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X2)
      | r2_hidden(k4_tarski(X3,X4),X0)
      | ~ r2_hidden(k4_tarski(X3,X4),X2)
      | k7_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) )
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( v1_relat_1(X2)
         => ( k7_relat_1(X0,X1) = X2
          <=> ! [X3,X4] :
                ( r2_hidden(k4_tarski(X3,X4),X2)
              <=> ( r2_hidden(k4_tarski(X3,X4),X0)
                  & r2_hidden(X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).
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
% 0.14/0.35  % DateTime   : Tue Dec  1 20:48:22 EST 2020
% 0.21/0.35  % CPUTime    : 
% 0.22/0.51  % (3708)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.52  % (3718)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.54  % (3707)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.54  % (3712)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (3703)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (3724)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (3723)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.55  % (3702)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (3728)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (3716)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.56  % (3714)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.56  % (3704)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.56  % (3715)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.56  % (3706)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.56  % (3701)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.38/0.56  % (3720)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.56  % (3706)Refutation found. Thanks to Tanya!
% 1.38/0.56  % SZS status Theorem for theBenchmark
% 1.38/0.56  % (3709)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.57  % (3727)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.53/0.57  % (3702)Refutation not found, incomplete strategy% (3702)------------------------------
% 1.53/0.57  % (3702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (3702)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (3702)Memory used [KB]: 10618
% 1.53/0.57  % (3702)Time elapsed: 0.139 s
% 1.53/0.57  % (3702)------------------------------
% 1.53/0.57  % (3702)------------------------------
% 1.53/0.57  % SZS output start Proof for theBenchmark
% 1.53/0.57  fof(f89,plain,(
% 1.53/0.57    $false),
% 1.53/0.57    inference(subsumption_resolution,[],[f87,f14])).
% 1.53/0.57  fof(f14,plain,(
% 1.53/0.57    ~r1_tarski(k7_relat_1(sK1,sK0),sK1)),
% 1.53/0.57    inference(cnf_transformation,[],[f8])).
% 1.53/0.57  fof(f8,plain,(
% 1.53/0.57    ? [X0,X1] : (~r1_tarski(k7_relat_1(X1,X0),X1) & v1_relat_1(X1))),
% 1.53/0.57    inference(ennf_transformation,[],[f6])).
% 1.53/0.57  fof(f6,negated_conjecture,(
% 1.53/0.57    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.53/0.57    inference(negated_conjecture,[],[f5])).
% 1.53/0.57  fof(f5,conjecture,(
% 1.53/0.57    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).
% 1.53/0.57  fof(f87,plain,(
% 1.53/0.57    r1_tarski(k7_relat_1(sK1,sK0),sK1)),
% 1.53/0.57    inference(resolution,[],[f86,f26])).
% 1.53/0.57  fof(f26,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~r2_hidden(sK7(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f12])).
% 1.53/0.57  fof(f12,plain,(
% 1.53/0.57    ! [X0,X1] : (r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f7])).
% 1.53/0.57  fof(f7,plain,(
% 1.53/0.57    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)) => r1_tarski(X0,X1))),
% 1.53/0.57    inference(unused_predicate_definition_removal,[],[f1])).
% 1.53/0.57  fof(f1,axiom,(
% 1.53/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.53/0.57  fof(f86,plain,(
% 1.53/0.57    r2_hidden(sK7(k7_relat_1(sK1,sK0),sK1),sK1)),
% 1.53/0.57    inference(subsumption_resolution,[],[f85,f14])).
% 1.53/0.57  fof(f85,plain,(
% 1.53/0.57    r2_hidden(sK7(k7_relat_1(sK1,sK0),sK1),sK1) | r1_tarski(k7_relat_1(sK1,sK0),sK1)),
% 1.53/0.57    inference(subsumption_resolution,[],[f84,f13])).
% 1.53/0.57  fof(f13,plain,(
% 1.53/0.57    v1_relat_1(sK1)),
% 1.53/0.57    inference(cnf_transformation,[],[f8])).
% 1.53/0.57  fof(f84,plain,(
% 1.53/0.57    r2_hidden(sK7(k7_relat_1(sK1,sK0),sK1),sK1) | ~v1_relat_1(sK1) | r1_tarski(k7_relat_1(sK1,sK0),sK1)),
% 1.53/0.57    inference(resolution,[],[f82,f25])).
% 1.53/0.57  fof(f25,plain,(
% 1.53/0.57    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f12])).
% 1.53/0.57  fof(f82,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~r2_hidden(sK7(k7_relat_1(sK1,sK0),sK1),k7_relat_1(X0,X1)) | r2_hidden(sK7(k7_relat_1(sK1,sK0),sK1),X0) | ~v1_relat_1(X0)) )),
% 1.53/0.57    inference(subsumption_resolution,[],[f79,f24])).
% 1.53/0.57  fof(f24,plain,(
% 1.53/0.57    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f11])).
% 1.53/0.57  fof(f11,plain,(
% 1.53/0.57    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f4])).
% 1.53/0.57  fof(f4,axiom,(
% 1.53/0.57    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 1.53/0.57  fof(f79,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~r2_hidden(sK7(k7_relat_1(sK1,sK0),sK1),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | r2_hidden(sK7(k7_relat_1(sK1,sK0),sK1),X0) | ~v1_relat_1(X0)) )),
% 1.53/0.57    inference(superposition,[],[f28,f78])).
% 1.53/0.57  fof(f78,plain,(
% 1.53/0.57    sK7(k7_relat_1(sK1,sK0),sK1) = k4_tarski(sK5(sK7(k7_relat_1(sK1,sK0),sK1)),sK6(sK7(k7_relat_1(sK1,sK0),sK1)))),
% 1.53/0.57    inference(resolution,[],[f39,f14])).
% 1.53/0.57  fof(f39,plain,(
% 1.53/0.57    ( ! [X2,X1] : (r1_tarski(k7_relat_1(sK1,X1),X2) | sK7(k7_relat_1(sK1,X1),X2) = k4_tarski(sK5(sK7(k7_relat_1(sK1,X1),X2)),sK6(sK7(k7_relat_1(sK1,X1),X2)))) )),
% 1.53/0.57    inference(resolution,[],[f36,f25])).
% 1.53/0.57  fof(f36,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k7_relat_1(sK1,X1)) | k4_tarski(sK5(X0),sK6(X0)) = X0) )),
% 1.53/0.57    inference(resolution,[],[f33,f13])).
% 1.53/0.57  fof(f33,plain,(
% 1.53/0.57    ( ! [X2,X3,X1] : (~v1_relat_1(X2) | ~r2_hidden(X1,k7_relat_1(X2,X3)) | k4_tarski(sK5(X1),sK6(X1)) = X1) )),
% 1.53/0.57    inference(resolution,[],[f21,f24])).
% 1.53/0.57  fof(f21,plain,(
% 1.53/0.57    ( ! [X0,X1] : (~v1_relat_1(X0) | k4_tarski(sK5(X1),sK6(X1)) = X1 | ~r2_hidden(X1,X0)) )),
% 1.53/0.57    inference(cnf_transformation,[],[f10])).
% 1.53/0.57  fof(f10,plain,(
% 1.53/0.57    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 1.53/0.57    inference(ennf_transformation,[],[f3])).
% 1.53/0.57  fof(f3,axiom,(
% 1.53/0.57    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).
% 1.53/0.57  fof(f28,plain,(
% 1.53/0.57    ( ! [X4,X0,X3,X1] : (~r2_hidden(k4_tarski(X3,X4),k7_relat_1(X0,X1)) | ~v1_relat_1(k7_relat_1(X0,X1)) | r2_hidden(k4_tarski(X3,X4),X0) | ~v1_relat_1(X0)) )),
% 1.53/0.57    inference(equality_resolution,[],[f19])).
% 1.53/0.57  fof(f19,plain,(
% 1.53/0.57    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X2) | r2_hidden(k4_tarski(X3,X4),X0) | ~r2_hidden(k4_tarski(X3,X4),X2) | k7_relat_1(X0,X1) != X2) )),
% 1.53/0.57    inference(cnf_transformation,[],[f9])).
% 1.53/0.57  fof(f9,plain,(
% 1.53/0.57    ! [X0] : (! [X1,X2] : ((k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1)))) | ~v1_relat_1(X2)) | ~v1_relat_1(X0))),
% 1.53/0.57    inference(ennf_transformation,[],[f2])).
% 1.53/0.57  fof(f2,axiom,(
% 1.53/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (v1_relat_1(X2) => (k7_relat_1(X0,X1) = X2 <=> ! [X3,X4] : (r2_hidden(k4_tarski(X3,X4),X2) <=> (r2_hidden(k4_tarski(X3,X4),X0) & r2_hidden(X3,X1))))))),
% 1.53/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_relat_1)).
% 1.53/0.57  % SZS output end Proof for theBenchmark
% 1.53/0.57  % (3706)------------------------------
% 1.53/0.57  % (3706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (3706)Termination reason: Refutation
% 1.53/0.57  
% 1.53/0.57  % (3706)Memory used [KB]: 6268
% 1.53/0.57  % (3706)Time elapsed: 0.146 s
% 1.53/0.57  % (3706)------------------------------
% 1.53/0.57  % (3706)------------------------------
% 1.53/0.57  % (3699)Success in time 0.202 s
%------------------------------------------------------------------------------
