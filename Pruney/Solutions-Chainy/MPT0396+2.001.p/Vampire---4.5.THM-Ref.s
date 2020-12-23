%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   30 (  69 expanded)
%              Number of leaves         :    4 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   68 ( 158 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30798)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
fof(f124,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f38,f30,f39,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(sK4(k3_tarski(sK0),k3_tarski(sK1)),X1)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f34,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f34,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK4(k3_tarski(sK0),k3_tarski(sK1)),X0)
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f28,f24])).

fof(f24,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X2,k3_tarski(X0))
      | ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f28,plain,(
    ~ r2_hidden(sK4(k3_tarski(sK0),k3_tarski(sK1)),k3_tarski(sK1)) ),
    inference(unit_resulting_resolution,[],[f10,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f10,plain,(
    ~ r1_tarski(k3_tarski(sK0),k3_tarski(sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),k3_tarski(X1))
      & r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X0,X1)
       => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => r1_tarski(k3_tarski(X0),k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).

fof(f39,plain,(
    r1_tarski(sK6(sK0,sK4(k3_tarski(sK0),k3_tarski(sK1))),sK3(sK1,sK6(sK0,sK4(k3_tarski(sK0),k3_tarski(sK1))))) ),
    inference(unit_resulting_resolution,[],[f9,f31,f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X2,sK3(X1,X2))
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f31,plain,(
    r2_hidden(sK6(sK0,sK4(k3_tarski(sK0),k3_tarski(sK1))),sK0) ),
    inference(unit_resulting_resolution,[],[f27,f25])).

fof(f25,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK6(X0,X2),X0)
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f27,plain,(
    r2_hidden(sK4(k3_tarski(sK0),k3_tarski(sK1)),k3_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f10,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,plain,(
    r1_setfam_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f30,plain,(
    r2_hidden(sK4(k3_tarski(sK0),k3_tarski(sK1)),sK6(sK0,sK4(k3_tarski(sK0),k3_tarski(sK1)))) ),
    inference(unit_resulting_resolution,[],[f27,f26])).

fof(f26,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK6(X0,X2))
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK6(X0,X2))
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f38,plain,(
    r2_hidden(sK3(sK1,sK6(sK0,sK4(k3_tarski(sK0),k3_tarski(sK1)))),sK1) ),
    inference(unit_resulting_resolution,[],[f9,f31,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X1,X2),X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:30:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.51  % (30772)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (30780)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (30793)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (30782)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (30785)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.54  % (30791)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (30773)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (30774)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (30776)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (30770)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (30771)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (30774)Refutation found. Thanks to Tanya!
% 0.20/0.54  % SZS status Theorem for theBenchmark
% 0.20/0.54  % SZS output start Proof for theBenchmark
% 0.20/0.54  % (30798)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  fof(f124,plain,(
% 0.20/0.54    $false),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f38,f30,f39,f41])).
% 0.20/0.54  fof(f41,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(sK4(k3_tarski(sK0),k3_tarski(sK1)),X1) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.54    inference(resolution,[],[f34,f15])).
% 0.20/0.54  fof(f15,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f8,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f1])).
% 0.20/0.54  fof(f1,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.54  fof(f34,plain,(
% 0.20/0.54    ( ! [X0] : (~r2_hidden(sK4(k3_tarski(sK0),k3_tarski(sK1)),X0) | ~r2_hidden(X0,sK1)) )),
% 0.20/0.54    inference(resolution,[],[f28,f24])).
% 0.20/0.54  fof(f24,plain,(
% 0.20/0.54    ( ! [X2,X0,X3] : (r2_hidden(X2,k3_tarski(X0)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) )),
% 0.20/0.54    inference(equality_resolution,[],[f23])).
% 0.20/0.54  fof(f23,plain,(
% 0.20/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f2,axiom,(
% 0.20/0.54    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.20/0.54  fof(f28,plain,(
% 0.20/0.54    ~r2_hidden(sK4(k3_tarski(sK0),k3_tarski(sK1)),k3_tarski(sK1))),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f10,f17])).
% 0.20/0.54  fof(f17,plain,(
% 0.20/0.54    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f10,plain,(
% 0.20/0.54    ~r1_tarski(k3_tarski(sK0),k3_tarski(sK1))),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f6,plain,(
% 0.20/0.54    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),k3_tarski(X1)) & r1_setfam_1(X0,X1))),
% 0.20/0.54    inference(ennf_transformation,[],[f5])).
% 0.20/0.54  fof(f5,negated_conjecture,(
% 0.20/0.54    ~! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.20/0.54    inference(negated_conjecture,[],[f4])).
% 0.20/0.54  fof(f4,conjecture,(
% 0.20/0.54    ! [X0,X1] : (r1_setfam_1(X0,X1) => r1_tarski(k3_tarski(X0),k3_tarski(X1)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_setfam_1)).
% 0.20/0.54  fof(f39,plain,(
% 0.20/0.54    r1_tarski(sK6(sK0,sK4(k3_tarski(sK0),k3_tarski(sK1))),sK3(sK1,sK6(sK0,sK4(k3_tarski(sK0),k3_tarski(sK1)))))),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f9,f31,f13])).
% 0.20/0.54  fof(f13,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r1_tarski(X2,sK3(X1,X2)) | ~r2_hidden(X2,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  fof(f7,plain,(
% 0.20/0.54    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)))),
% 0.20/0.54    inference(ennf_transformation,[],[f3])).
% 0.20/0.54  fof(f3,axiom,(
% 0.20/0.54    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.20/0.54  fof(f31,plain,(
% 0.20/0.54    r2_hidden(sK6(sK0,sK4(k3_tarski(sK0),k3_tarski(sK1))),sK0)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f27,f25])).
% 0.20/0.54  fof(f25,plain,(
% 0.20/0.54    ( ! [X2,X0] : (r2_hidden(sK6(X0,X2),X0) | ~r2_hidden(X2,k3_tarski(X0))) )),
% 0.20/0.54    inference(equality_resolution,[],[f22])).
% 0.20/0.54  fof(f22,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X2),X0) | ~r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f27,plain,(
% 0.20/0.54    r2_hidden(sK4(k3_tarski(sK0),k3_tarski(sK1)),k3_tarski(sK0))),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f10,f16])).
% 0.20/0.54  fof(f16,plain,(
% 0.20/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK4(X0,X1),X0)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f8])).
% 0.20/0.54  fof(f9,plain,(
% 0.20/0.54    r1_setfam_1(sK0,sK1)),
% 0.20/0.54    inference(cnf_transformation,[],[f6])).
% 0.20/0.54  fof(f30,plain,(
% 0.20/0.54    r2_hidden(sK4(k3_tarski(sK0),k3_tarski(sK1)),sK6(sK0,sK4(k3_tarski(sK0),k3_tarski(sK1))))),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f27,f26])).
% 0.20/0.54  fof(f26,plain,(
% 0.20/0.54    ( ! [X2,X0] : (r2_hidden(X2,sK6(X0,X2)) | ~r2_hidden(X2,k3_tarski(X0))) )),
% 0.20/0.54    inference(equality_resolution,[],[f21])).
% 0.20/0.54  fof(f21,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,sK6(X0,X2)) | ~r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 0.20/0.54    inference(cnf_transformation,[],[f2])).
% 0.20/0.54  fof(f38,plain,(
% 0.20/0.54    r2_hidden(sK3(sK1,sK6(sK0,sK4(k3_tarski(sK0),k3_tarski(sK1)))),sK1)),
% 0.20/0.54    inference(unit_resulting_resolution,[],[f9,f31,f12])).
% 0.20/0.54  fof(f12,plain,(
% 0.20/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK3(X1,X2),X1) | ~r2_hidden(X2,X0) | ~r1_setfam_1(X0,X1)) )),
% 0.20/0.54    inference(cnf_transformation,[],[f7])).
% 0.20/0.54  % SZS output end Proof for theBenchmark
% 0.20/0.54  % (30774)------------------------------
% 0.20/0.54  % (30774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (30774)Termination reason: Refutation
% 0.20/0.54  
% 0.20/0.54  % (30774)Memory used [KB]: 6268
% 0.20/0.54  % (30774)Time elapsed: 0.129 s
% 0.20/0.54  % (30774)------------------------------
% 0.20/0.54  % (30774)------------------------------
% 0.20/0.54  % (30777)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (30769)Success in time 0.179 s
%------------------------------------------------------------------------------
