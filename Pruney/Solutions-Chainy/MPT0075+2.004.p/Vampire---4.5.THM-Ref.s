%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:38 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   26 (  67 expanded)
%              Number of leaves         :    5 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   66 ( 198 expanded)
%              Number of equality atoms :    2 (   3 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f56,f88,f30])).

fof(f30,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f88,plain,(
    ~ r2_hidden(sK3(sK2),k2_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f40,f41,f14,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r2_hidden(X2,X0)
        & r2_hidden(X2,X1) )
      | ( ~ r2_hidden(X2,X1)
        & r2_hidden(X2,X0) )
      | ~ r2_hidden(X2,k2_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,X1) )
        & ~ ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) )
        & r2_hidden(X2,k2_xboole_0(X0,X1))
        & r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

fof(f14,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X2,X0)
      & ~ v1_xboole_0(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ v1_xboole_0(X2)
       => ~ ( r1_xboole_0(X0,X1)
            & r1_tarski(X2,X1)
            & r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
     => ~ ( r1_xboole_0(X0,X1)
          & r1_tarski(X2,X1)
          & r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

fof(f41,plain,(
    r2_hidden(sK3(sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f31,f13,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f13,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    r2_hidden(sK3(sK2),sK2) ),
    inference(unit_resulting_resolution,[],[f11,f15])).

fof(f15,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f11,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    r2_hidden(sK3(sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f31,f12,f17])).

fof(f12,plain,(
    r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f56,plain,(
    ! [X0] : sP6(sK3(sK2),sK1,X0) ),
    inference(unit_resulting_resolution,[],[f41,f21])).

fof(f21,plain,(
    ! [X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f3])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:10:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.54  % (20971)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.34/0.55  % (20954)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.34/0.55  % (20953)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.56  % (20954)Refutation not found, incomplete strategy% (20954)------------------------------
% 1.34/0.56  % (20954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.56  % (20970)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.34/0.57  % (20970)Refutation found. Thanks to Tanya!
% 1.34/0.57  % SZS status Theorem for theBenchmark
% 1.34/0.57  % (20972)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.57  % (20961)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.34/0.57  % (20962)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.57  % SZS output start Proof for theBenchmark
% 1.34/0.57  fof(f192,plain,(
% 1.34/0.57    $false),
% 1.34/0.57    inference(unit_resulting_resolution,[],[f56,f88,f30])).
% 1.59/0.57  fof(f30,plain,(
% 1.59/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_xboole_0(X0,X1)) | ~sP6(X3,X1,X0)) )),
% 1.59/0.57    inference(equality_resolution,[],[f23])).
% 1.59/0.57  fof(f23,plain,(
% 1.59/0.57    ( ! [X2,X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.59/0.57    inference(cnf_transformation,[],[f3])).
% 1.59/0.57  fof(f3,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.59/0.57  fof(f88,plain,(
% 1.59/0.57    ~r2_hidden(sK3(sK2),k2_xboole_0(sK0,sK1))),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f40,f41,f14,f27])).
% 1.59/0.57  fof(f27,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f10])).
% 1.59/0.57  fof(f10,plain,(
% 1.59/0.57    ! [X0,X1,X2] : ((~r2_hidden(X2,X0) & r2_hidden(X2,X1)) | (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) | ~r2_hidden(X2,k2_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1))),
% 1.59/0.57    inference(ennf_transformation,[],[f4])).
% 1.59/0.57  fof(f4,axiom,(
% 1.59/0.57    ! [X0,X1,X2] : ~(~(~r2_hidden(X2,X0) & r2_hidden(X2,X1)) & ~(~r2_hidden(X2,X1) & r2_hidden(X2,X0)) & r2_hidden(X2,k2_xboole_0(X0,X1)) & r1_xboole_0(X0,X1))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).
% 1.59/0.57  fof(f14,plain,(
% 1.59/0.57    r1_xboole_0(sK0,sK1)),
% 1.59/0.57    inference(cnf_transformation,[],[f8])).
% 1.59/0.57  fof(f8,plain,(
% 1.59/0.57    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0) & ~v1_xboole_0(X2))),
% 1.59/0.57    inference(flattening,[],[f7])).
% 1.59/0.57  fof(f7,plain,(
% 1.59/0.57    ? [X0,X1,X2] : ((r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)) & ~v1_xboole_0(X2))),
% 1.59/0.57    inference(ennf_transformation,[],[f6])).
% 1.59/0.57  fof(f6,negated_conjecture,(
% 1.59/0.57    ~! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 1.59/0.57    inference(negated_conjecture,[],[f5])).
% 1.59/0.57  fof(f5,conjecture,(
% 1.59/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) => ~(r1_xboole_0(X0,X1) & r1_tarski(X2,X1) & r1_tarski(X2,X0)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).
% 1.59/0.57  fof(f41,plain,(
% 1.59/0.57    r2_hidden(sK3(sK2),sK1)),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f31,f13,f17])).
% 1.59/0.57  fof(f17,plain,(
% 1.59/0.57    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f9])).
% 1.59/0.57  fof(f9,plain,(
% 1.59/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.59/0.57    inference(ennf_transformation,[],[f2])).
% 1.59/0.57  fof(f2,axiom,(
% 1.59/0.57    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.59/0.57  fof(f13,plain,(
% 1.59/0.57    r1_tarski(sK2,sK1)),
% 1.59/0.57    inference(cnf_transformation,[],[f8])).
% 1.59/0.57  fof(f31,plain,(
% 1.59/0.57    r2_hidden(sK3(sK2),sK2)),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f11,f15])).
% 1.59/0.57  fof(f15,plain,(
% 1.59/0.57    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f1])).
% 1.59/0.57  fof(f1,axiom,(
% 1.59/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.59/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.59/0.57  fof(f11,plain,(
% 1.59/0.57    ~v1_xboole_0(sK2)),
% 1.59/0.57    inference(cnf_transformation,[],[f8])).
% 1.59/0.57  fof(f40,plain,(
% 1.59/0.57    r2_hidden(sK3(sK2),sK0)),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f31,f12,f17])).
% 1.59/0.57  fof(f12,plain,(
% 1.59/0.57    r1_tarski(sK2,sK0)),
% 1.59/0.57    inference(cnf_transformation,[],[f8])).
% 1.59/0.57  fof(f56,plain,(
% 1.59/0.57    ( ! [X0] : (sP6(sK3(sK2),sK1,X0)) )),
% 1.59/0.57    inference(unit_resulting_resolution,[],[f41,f21])).
% 1.59/0.57  fof(f21,plain,(
% 1.59/0.57    ( ! [X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 1.59/0.57    inference(cnf_transformation,[],[f3])).
% 1.59/0.57  % SZS output end Proof for theBenchmark
% 1.59/0.57  % (20970)------------------------------
% 1.59/0.57  % (20970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (20970)Termination reason: Refutation
% 1.59/0.57  
% 1.59/0.57  % (20970)Memory used [KB]: 6396
% 1.59/0.57  % (20970)Time elapsed: 0.146 s
% 1.59/0.57  % (20970)------------------------------
% 1.59/0.57  % (20970)------------------------------
% 1.59/0.57  % (20955)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.59/0.58  % (20943)Success in time 0.212 s
%------------------------------------------------------------------------------
