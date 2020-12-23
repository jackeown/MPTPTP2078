%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:14 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   21 (  38 expanded)
%              Number of leaves         :    3 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  97 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f9])).

fof(f9,plain,(
    ~ r1_tarski(sK2,sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(X2,X0)
          & r2_hidden(X2,X1) )
      & r1_setfam_1(X1,k1_tarski(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_setfam_1(X1,k1_tarski(X0))
       => ! [X2] :
            ( r2_hidden(X2,X1)
           => r1_tarski(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r1_setfam_1(X1,k1_tarski(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

fof(f28,plain,(
    r1_tarski(sK2,sK0) ),
    inference(backward_demodulation,[],[f23,f26])).

fof(f26,plain,(
    sK0 = sK3(k1_tarski(sK0),sK2) ),
    inference(resolution,[],[f25,f17])).

fof(f17,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f14])).

fof(f14,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f25,plain,(
    r2_hidden(sK3(k1_tarski(sK0),sK2),k1_tarski(sK0)) ),
    inference(resolution,[],[f20,f8])).

fof(f8,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f20,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(sK3(k1_tarski(sK0),X0),k1_tarski(sK0)) ) ),
    inference(resolution,[],[f10,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(sK3(X1,X2),X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ? [X3] :
              ( r1_tarski(X2,X3)
              & r2_hidden(X3,X1) )
          | ~ r2_hidden(X2,X0) )
      | ~ r1_setfam_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,plain,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
     => ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_setfam_1(X0,X1)
    <=> ! [X2] :
          ~ ( ! [X3] :
                ~ ( r1_tarski(X2,X3)
                  & r2_hidden(X3,X1) )
            & r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

fof(f10,plain,(
    r1_setfam_1(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f23,plain,(
    r1_tarski(sK2,sK3(k1_tarski(sK0),sK2)) ),
    inference(resolution,[],[f21,f8])).

fof(f21,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | r1_tarski(X1,sK3(k1_tarski(sK0),X1)) ) ),
    inference(resolution,[],[f10,f12])).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_setfam_1(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r1_tarski(X2,sK3(X1,X2)) ) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:52:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.46  % (12284)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.46  % (12284)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f28,f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ~r1_tarski(sK2,sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f6,plain,(
% 0.20/0.46    ? [X0,X1] : (? [X2] : (~r1_tarski(X2,X0) & r2_hidden(X2,X1)) & r1_setfam_1(X1,k1_tarski(X0)))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.20/0.46    inference(negated_conjecture,[],[f3])).
% 0.20/0.46  fof(f3,conjecture,(
% 0.20/0.46    ! [X0,X1] : (r1_setfam_1(X1,k1_tarski(X0)) => ! [X2] : (r2_hidden(X2,X1) => r1_tarski(X2,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    r1_tarski(sK2,sK0)),
% 0.20/0.46    inference(backward_demodulation,[],[f23,f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    sK0 = sK3(k1_tarski(sK0),sK2)),
% 0.20/0.46    inference(resolution,[],[f25,f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X2,X0] : (~r2_hidden(X2,k1_tarski(X0)) | X0 = X2) )),
% 0.20/0.46    inference(equality_resolution,[],[f14])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.46  fof(f25,plain,(
% 0.20/0.46    r2_hidden(sK3(k1_tarski(sK0),sK2),k1_tarski(sK0))),
% 0.20/0.46    inference(resolution,[],[f20,f8])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    r2_hidden(sK2,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(sK3(k1_tarski(sK0),X0),k1_tarski(sK0))) )),
% 0.20/0.46    inference(resolution,[],[f10,f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(sK3(X1,X2),X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,plain,(
% 0.20/0.46    ! [X0,X1] : (! [X2] : (? [X3] : (r1_tarski(X2,X3) & r2_hidden(X3,X1)) | ~r2_hidden(X2,X0)) | ~r1_setfam_1(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_setfam_1(X0,X1) => ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.46    inference(unused_predicate_definition_removal,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_setfam_1(X0,X1) <=> ! [X2] : ~(! [X3] : ~(r1_tarski(X2,X3) & r2_hidden(X3,X1)) & r2_hidden(X2,X0)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    r1_setfam_1(sK1,k1_tarski(sK0))),
% 0.20/0.46    inference(cnf_transformation,[],[f6])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    r1_tarski(sK2,sK3(k1_tarski(sK0),sK2))),
% 0.20/0.46    inference(resolution,[],[f21,f8])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ( ! [X1] : (~r2_hidden(X1,sK1) | r1_tarski(X1,sK3(k1_tarski(sK0),X1))) )),
% 0.20/0.46    inference(resolution,[],[f10,f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_setfam_1(X0,X1) | ~r2_hidden(X2,X0) | r1_tarski(X2,sK3(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f7])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (12284)------------------------------
% 0.20/0.46  % (12284)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (12284)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (12284)Memory used [KB]: 6140
% 0.20/0.46  % (12284)Time elapsed: 0.069 s
% 0.20/0.46  % (12284)------------------------------
% 0.20/0.46  % (12284)------------------------------
% 0.20/0.46  % (12278)Success in time 0.107 s
%------------------------------------------------------------------------------
