%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:43 EST 2020

% Result     : Theorem 1.39s
% Output     : Refutation 1.39s
% Verified   : 
% Statistics : Number of formulae       :   22 (  42 expanded)
%              Number of leaves         :    3 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 ( 102 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f49,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f29,f28,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(k3_tarski(sK0),sK1),X0)
      | ~ r2_hidden(X0,sK0) ) ),
    inference(resolution,[],[f27,f7])).

fof(f7,plain,(
    ! [X2] :
      ( r1_tarski(X2,sK1)
      | ~ r2_hidden(X2,sK0) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),X1)
      & ! [X2] :
          ( r1_tarski(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r1_tarski(X2,X1) )
       => r1_tarski(k3_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f27,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r2_hidden(sK5(k3_tarski(sK0),sK1),X0) ) ),
    inference(resolution,[],[f22,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
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

fof(f22,plain,(
    ~ r2_hidden(sK5(k3_tarski(sK0),sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f8,f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK5(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f8,plain,(
    ~ r1_tarski(k3_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f28,plain,(
    r2_hidden(sK5(k3_tarski(sK0),sK1),sK3(sK0,sK5(k3_tarski(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f21,f20])).

fof(f20,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK3(X0,X2))
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK3(X0,X2))
      | ~ r2_hidden(X2,X1)
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

fof(f21,plain,(
    r2_hidden(sK5(k3_tarski(sK0),sK1),k3_tarski(sK0)) ),
    inference(unit_resulting_resolution,[],[f8,f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f29,plain,(
    r2_hidden(sK3(sK0,sK5(k3_tarski(sK0),sK1)),sK0) ),
    inference(unit_resulting_resolution,[],[f21,f19])).

fof(f19,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK3(X0,X2),X0)
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:56:26 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (24064)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (24070)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (24062)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (24054)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.53  % (24072)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (24057)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.53  % (24075)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (24052)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.39/0.54  % (24052)Refutation found. Thanks to Tanya!
% 1.39/0.54  % SZS status Theorem for theBenchmark
% 1.39/0.54  % SZS output start Proof for theBenchmark
% 1.39/0.54  fof(f49,plain,(
% 1.39/0.54    $false),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f29,f28,f34])).
% 1.39/0.54  fof(f34,plain,(
% 1.39/0.54    ( ! [X0] : (~r2_hidden(sK5(k3_tarski(sK0),sK1),X0) | ~r2_hidden(X0,sK0)) )),
% 1.39/0.54    inference(resolution,[],[f27,f7])).
% 1.39/0.54  fof(f7,plain,(
% 1.39/0.54    ( ! [X2] : (r1_tarski(X2,sK1) | ~r2_hidden(X2,sK0)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f5])).
% 1.39/0.54  fof(f5,plain,(
% 1.39/0.54    ? [X0,X1] : (~r1_tarski(k3_tarski(X0),X1) & ! [X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f4])).
% 1.39/0.54  fof(f4,negated_conjecture,(
% 1.39/0.54    ~! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 1.39/0.54    inference(negated_conjecture,[],[f3])).
% 1.39/0.54  fof(f3,conjecture,(
% 1.39/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 1.39/0.54  fof(f27,plain,(
% 1.39/0.54    ( ! [X0] : (~r1_tarski(X0,sK1) | ~r2_hidden(sK5(k3_tarski(sK0),sK1),X0)) )),
% 1.39/0.54    inference(resolution,[],[f22,f15])).
% 1.39/0.54  fof(f15,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f6])).
% 1.39/0.54  fof(f6,plain,(
% 1.39/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.39/0.54    inference(ennf_transformation,[],[f1])).
% 1.39/0.54  fof(f1,axiom,(
% 1.39/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.39/0.54  fof(f22,plain,(
% 1.39/0.54    ~r2_hidden(sK5(k3_tarski(sK0),sK1),sK1)),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f8,f17])).
% 1.39/0.54  fof(f17,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK5(X0,X1),X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f6])).
% 1.39/0.54  fof(f8,plain,(
% 1.39/0.54    ~r1_tarski(k3_tarski(sK0),sK1)),
% 1.39/0.54    inference(cnf_transformation,[],[f5])).
% 1.39/0.54  fof(f28,plain,(
% 1.39/0.54    r2_hidden(sK5(k3_tarski(sK0),sK1),sK3(sK0,sK5(k3_tarski(sK0),sK1)))),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f21,f20])).
% 1.39/0.54  fof(f20,plain,(
% 1.39/0.54    ( ! [X2,X0] : (r2_hidden(X2,sK3(X0,X2)) | ~r2_hidden(X2,k3_tarski(X0))) )),
% 1.39/0.54    inference(equality_resolution,[],[f12])).
% 1.39/0.54  fof(f12,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (r2_hidden(X2,sK3(X0,X2)) | ~r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 1.39/0.54    inference(cnf_transformation,[],[f2])).
% 1.39/0.54  fof(f2,axiom,(
% 1.39/0.54    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 1.39/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 1.39/0.54  fof(f21,plain,(
% 1.39/0.54    r2_hidden(sK5(k3_tarski(sK0),sK1),k3_tarski(sK0))),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f8,f16])).
% 1.39/0.54  fof(f16,plain,(
% 1.39/0.54    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.39/0.54    inference(cnf_transformation,[],[f6])).
% 1.39/0.54  fof(f29,plain,(
% 1.39/0.54    r2_hidden(sK3(sK0,sK5(k3_tarski(sK0),sK1)),sK0)),
% 1.39/0.54    inference(unit_resulting_resolution,[],[f21,f19])).
% 1.39/0.54  fof(f19,plain,(
% 1.39/0.54    ( ! [X2,X0] : (r2_hidden(sK3(X0,X2),X0) | ~r2_hidden(X2,k3_tarski(X0))) )),
% 1.39/0.54    inference(equality_resolution,[],[f13])).
% 1.39/0.54  fof(f13,plain,(
% 1.39/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X2),X0) | ~r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 1.39/0.54    inference(cnf_transformation,[],[f2])).
% 1.39/0.54  % SZS output end Proof for theBenchmark
% 1.39/0.54  % (24052)------------------------------
% 1.39/0.54  % (24052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.54  % (24052)Termination reason: Refutation
% 1.39/0.54  
% 1.39/0.54  % (24052)Memory used [KB]: 6140
% 1.39/0.54  % (24052)Time elapsed: 0.115 s
% 1.39/0.54  % (24052)------------------------------
% 1.39/0.54  % (24052)------------------------------
% 1.39/0.54  % (24047)Success in time 0.176 s
%------------------------------------------------------------------------------
