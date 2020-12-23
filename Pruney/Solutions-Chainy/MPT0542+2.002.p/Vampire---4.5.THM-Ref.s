%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   28 (  43 expanded)
%              Number of leaves         :    5 (  10 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 (  92 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f103,plain,(
    $false ),
    inference(subsumption_resolution,[],[f100,f12])).

fof(f12,plain,(
    ~ r1_tarski(k9_relat_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

fof(f100,plain,(
    r1_tarski(k9_relat_1(sK1,sK0),k2_relat_1(sK1)) ),
    inference(resolution,[],[f97,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f97,plain,(
    r2_hidden(sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1)) ),
    inference(resolution,[],[f82,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f82,plain,(
    r2_hidden(k4_tarski(sK3(sK1,sK0,sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f63,f29])).

fof(f29,plain,(
    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1))) ),
    inference(resolution,[],[f11,f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

fof(f11,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X3] :
      ( ~ r1_tarski(sK1,X3)
      | r2_hidden(k4_tarski(sK3(sK1,sK0,sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),X3) ) ),
    inference(resolution,[],[f42,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    r2_hidden(k4_tarski(sK3(sK1,sK0,sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),sK1) ),
    inference(resolution,[],[f35,f36])).

fof(f36,plain,(
    r2_hidden(sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1)),k9_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f12,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK5(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f35,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(X13,k9_relat_1(sK1,X12))
      | r2_hidden(k4_tarski(sK3(sK1,X12,X13),X13),sK1) ) ),
    inference(resolution,[],[f11,f28])).

fof(f28,plain,(
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
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:23:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (26956)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (26948)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (26948)Refutation not found, incomplete strategy% (26948)------------------------------
% 0.21/0.51  % (26948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (26961)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (26969)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (26948)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (26948)Memory used [KB]: 1663
% 0.21/0.52  % (26948)Time elapsed: 0.103 s
% 0.21/0.52  % (26948)------------------------------
% 0.21/0.52  % (26948)------------------------------
% 0.21/0.52  % (26959)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (26963)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (26969)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (26962)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (26971)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f103,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f100,f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ~r1_tarski(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,plain,(
% 0.21/0.53    ? [X0,X1] : (~r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) & v1_relat_1(X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.21/0.53    inference(negated_conjecture,[],[f5])).
% 0.21/0.53  fof(f5,conjecture,(
% 0.21/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    r1_tarski(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),
% 0.21/0.53    inference(resolution,[],[f97,f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    r2_hidden(sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1)),k2_relat_1(sK1))),
% 0.21/0.53    inference(resolution,[],[f82,f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK3(sK1,sK0,sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 0.21/0.53    inference(resolution,[],[f63,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    r1_tarski(sK1,k2_zfmisc_1(k1_relat_1(sK1),k2_relat_1(sK1)))),
% 0.21/0.53    inference(resolution,[],[f11,f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,plain,(
% 0.21/0.53    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    v1_relat_1(sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X3] : (~r1_tarski(sK1,X3) | r2_hidden(k4_tarski(sK3(sK1,sK0,sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),X3)) )),
% 0.21/0.53    inference(resolution,[],[f42,f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    r2_hidden(k4_tarski(sK3(sK1,sK0,sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1))),sK1)),
% 0.21/0.53    inference(resolution,[],[f35,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    r2_hidden(sK5(k9_relat_1(sK1,sK0),k2_relat_1(sK1)),k9_relat_1(sK1,sK0))),
% 0.21/0.53    inference(resolution,[],[f12,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK5(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f10])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X12,X13] : (~r2_hidden(X13,k9_relat_1(sK1,X12)) | r2_hidden(k4_tarski(sK3(sK1,X12,X13),X13),sK1)) )),
% 0.21/0.53    inference(resolution,[],[f11,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1,X3),X3),X0) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.21/0.53    inference(equality_resolution,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK3(X0,X1,X3),X3),X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_relat_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (26969)------------------------------
% 0.21/0.53  % (26969)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (26969)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (26969)Memory used [KB]: 1791
% 0.21/0.53  % (26969)Time elapsed: 0.121 s
% 0.21/0.53  % (26969)------------------------------
% 0.21/0.53  % (26969)------------------------------
% 0.21/0.53  % (26949)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (26947)Success in time 0.162 s
%------------------------------------------------------------------------------
