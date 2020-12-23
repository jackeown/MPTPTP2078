%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  68 expanded)
%              Number of leaves         :    3 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   74 ( 191 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f31,f39,f30,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k9_relat_1(sK2,X0))
      | r2_hidden(X1,k9_relat_1(sK2,X2))
      | ~ r2_hidden(sK4(sK2,X0,X1),X2) ) ),
    inference(resolution,[],[f29,f27])).

fof(f27,plain,(
    ! [X8,X7] :
      ( r2_hidden(k4_tarski(sK4(sK2,X7,X8),X8),sK2)
      | ~ r2_hidden(X8,k9_relat_1(sK2,X7)) ) ),
    inference(resolution,[],[f9,f23])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(sK4(X0,X1,X3),X3),X0)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
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

fof(f9,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))
      & r1_tarski(X0,X1)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( r1_tarski(X0,X1)
         => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).

fof(f29,plain,(
    ! [X12,X13,X11] :
      ( ~ r2_hidden(k4_tarski(X11,X12),sK2)
      | ~ r2_hidden(X11,X13)
      | r2_hidden(X12,k9_relat_1(sK2,X13)) ) ),
    inference(resolution,[],[f9,f21])).

fof(f21,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | ~ r2_hidden(k4_tarski(X4,X3),X0)
      | ~ r2_hidden(X4,X1)
      | r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f30,plain,(
    r2_hidden(sK6(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,sK0)) ),
    inference(unit_resulting_resolution,[],[f11,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK6(X0,X1),X0) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f11,plain,(
    ~ r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f39,plain,(
    r2_hidden(sK4(sK2,sK0,sK6(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK1) ),
    inference(unit_resulting_resolution,[],[f10,f35,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    r2_hidden(sK4(sK2,sK0,sK6(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK0) ),
    inference(unit_resulting_resolution,[],[f9,f30,f22])).

fof(f22,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k9_relat_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k9_relat_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f10,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f31,plain,(
    ~ r2_hidden(sK6(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,sK1)) ),
    inference(unit_resulting_resolution,[],[f11,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK6(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:06:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (1540)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (1556)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.51  % (1548)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.52  % (1537)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (1539)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (1538)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.54  % (1533)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.54  % (1528)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (1530)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (1532)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (1530)Refutation not found, incomplete strategy% (1530)------------------------------
% 0.22/0.54  % (1530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1530)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1530)Memory used [KB]: 10618
% 0.22/0.54  % (1530)Time elapsed: 0.126 s
% 0.22/0.54  % (1530)------------------------------
% 0.22/0.54  % (1530)------------------------------
% 0.22/0.54  % (1531)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (1532)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f60,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f31,f39,f30,f46])).
% 0.22/0.54  fof(f46,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X1,k9_relat_1(sK2,X0)) | r2_hidden(X1,k9_relat_1(sK2,X2)) | ~r2_hidden(sK4(sK2,X0,X1),X2)) )),
% 0.22/0.54    inference(resolution,[],[f29,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ( ! [X8,X7] : (r2_hidden(k4_tarski(sK4(sK2,X7,X8),X8),sK2) | ~r2_hidden(X8,k9_relat_1(sK2,X7))) )),
% 0.22/0.54    inference(resolution,[],[f9,f23])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,X1,X3),X3),X0) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(k4_tarski(sK4(X0,X1,X3),X3),X0) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,plain,(
% 0.22/0.54    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 0.22/0.54    inference(ennf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    v1_relat_1(sK2)),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,plain,(
% 0.22/0.54    ? [X0,X1,X2] : (~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1) & v1_relat_1(X2))),
% 0.22/0.54    inference(flattening,[],[f5])).
% 0.22/0.54  fof(f5,plain,(
% 0.22/0.54    ? [X0,X1,X2] : ((~r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1)) & r1_tarski(X0,X1)) & v1_relat_1(X2))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,negated_conjecture,(
% 0.22/0.54    ~! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.54    inference(negated_conjecture,[],[f3])).
% 0.22/0.54  fof(f3,conjecture,(
% 0.22/0.54    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k9_relat_1(X2,X0),k9_relat_1(X2,X1))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t156_relat_1)).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X12,X13,X11] : (~r2_hidden(k4_tarski(X11,X12),sK2) | ~r2_hidden(X11,X13) | r2_hidden(X12,k9_relat_1(sK2,X13))) )),
% 0.22/0.54    inference(resolution,[],[f9,f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ( ! [X4,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ( ! [X4,X2,X0,X3,X1] : (~v1_relat_1(X0) | ~r2_hidden(k4_tarski(X4,X3),X0) | ~r2_hidden(X4,X1) | r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    r2_hidden(sK6(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,sK0))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f11,f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK6(X0,X1),X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f8,plain,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ~r1_tarski(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f39,plain,(
% 0.22/0.54    r2_hidden(sK4(sK2,sK0,sK6(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK1)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f10,f35,f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    r2_hidden(sK4(sK2,sK0,sK6(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1))),sK0)),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f9,f30,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(sK4(X0,X1,X3),X1) | ~r2_hidden(X3,k9_relat_1(X0,X1))) )),
% 0.22/0.54    inference(equality_resolution,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ( ! [X2,X0,X3,X1] : (~v1_relat_1(X0) | r2_hidden(sK4(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k9_relat_1(X0,X1) != X2) )),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    r1_tarski(sK0,sK1)),
% 0.22/0.54    inference(cnf_transformation,[],[f6])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ~r2_hidden(sK6(k9_relat_1(sK2,sK0),k9_relat_1(sK2,sK1)),k9_relat_1(sK2,sK1))),
% 0.22/0.54    inference(unit_resulting_resolution,[],[f11,f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r2_hidden(sK6(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f8])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (1532)------------------------------
% 0.22/0.54  % (1532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1532)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (1532)Memory used [KB]: 6268
% 0.22/0.54  % (1532)Time elapsed: 0.127 s
% 0.22/0.54  % (1532)------------------------------
% 0.22/0.54  % (1532)------------------------------
% 0.22/0.54  % (1525)Success in time 0.174 s
%------------------------------------------------------------------------------
