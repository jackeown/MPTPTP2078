%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:51:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   27 (  48 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :    9
%              Number of atoms          :   88 ( 184 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f36,plain,(
    $false ),
    inference(subsumption_resolution,[],[f34,f20])).

fof(f20,plain,(
    ~ r2_hidden(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( ~ r2_hidden(sK2,sK0)
    & r2_hidden(sK2,k2_relat_1(sK1))
    & v5_relat_1(sK1,sK0)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f10,f9])).

fof(f9,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_hidden(X2,X0)
            & r2_hidden(X2,k2_relat_1(X1)) )
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r2_hidden(X2,sK0)
          & r2_hidden(X2,k2_relat_1(sK1)) )
      & v5_relat_1(sK1,sK0)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,
    ( ? [X2] :
        ( ~ r2_hidden(X2,sK0)
        & r2_hidden(X2,k2_relat_1(sK1)) )
   => ( ~ r2_hidden(sK2,sK0)
      & r2_hidden(sK2,k2_relat_1(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X0)
          & r2_hidden(X2,k2_relat_1(X1)) )
      & v5_relat_1(X1,X0)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( v5_relat_1(X1,X0)
          & v1_relat_1(X1) )
       => ! [X2] :
            ( r2_hidden(X2,k2_relat_1(X1))
           => r2_hidden(X2,X0) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).

fof(f34,plain,(
    r2_hidden(sK2,sK0) ),
    inference(resolution,[],[f31,f29])).

fof(f29,plain,(
    r1_tarski(k2_relat_1(sK1),sK0) ),
    inference(subsumption_resolution,[],[f28,f17])).

fof(f17,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f28,plain,
    ( r1_tarski(k2_relat_1(sK1),sK0)
    | ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f21,f18])).

fof(f18,plain,(
    v5_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

fof(f31,plain,(
    ! [X0] :
      ( ~ r1_tarski(k2_relat_1(sK1),X0)
      | r2_hidden(sK2,X0) ) ),
    inference(resolution,[],[f23,f19])).

fof(f19,plain,(
    r2_hidden(sK2,k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f23,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:11:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (25257)WARNING: option uwaf not known.
% 0.22/0.44  % (25249)lrs+1_3_awrs=decay:awrsf=4:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fsr=off:fde=unused:gs=on:lwlo=on:nm=16:nwc=1:sas=z3:stl=30:ss=axioms:s2a=on:st=1.2:sos=theory:sp=frequency_3 on theBenchmark
% 0.22/0.45  % (25257)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.22/0.45  % (25257)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f36,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(subsumption_resolution,[],[f34,f20])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    ~r2_hidden(sK2,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    (~r2_hidden(sK2,sK0) & r2_hidden(sK2,k2_relat_1(sK1))) & v5_relat_1(sK1,sK0) & v1_relat_1(sK1)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f10,f9])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ? [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,k2_relat_1(X1))) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => (? [X2] : (~r2_hidden(X2,sK0) & r2_hidden(X2,k2_relat_1(sK1))) & v5_relat_1(sK1,sK0) & v1_relat_1(sK1))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ? [X2] : (~r2_hidden(X2,sK0) & r2_hidden(X2,k2_relat_1(sK1))) => (~r2_hidden(sK2,sK0) & r2_hidden(sK2,k2_relat_1(sK1)))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f6,plain,(
% 0.22/0.45    ? [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,k2_relat_1(X1))) & v5_relat_1(X1,X0) & v1_relat_1(X1))),
% 0.22/0.45    inference(flattening,[],[f5])).
% 0.22/0.45  fof(f5,plain,(
% 0.22/0.45    ? [X0,X1] : (? [X2] : (~r2_hidden(X2,X0) & r2_hidden(X2,k2_relat_1(X1))) & (v5_relat_1(X1,X0) & v1_relat_1(X1)))),
% 0.22/0.45    inference(ennf_transformation,[],[f4])).
% 0.22/0.45  fof(f4,negated_conjecture,(
% 0.22/0.45    ~! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 0.22/0.45    inference(negated_conjecture,[],[f3])).
% 0.22/0.45  fof(f3,conjecture,(
% 0.22/0.45    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t202_relat_1)).
% 0.22/0.45  fof(f34,plain,(
% 0.22/0.45    r2_hidden(sK2,sK0)),
% 0.22/0.45    inference(resolution,[],[f31,f29])).
% 0.22/0.45  fof(f29,plain,(
% 0.22/0.45    r1_tarski(k2_relat_1(sK1),sK0)),
% 0.22/0.45    inference(subsumption_resolution,[],[f28,f17])).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    v1_relat_1(sK1)),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    r1_tarski(k2_relat_1(sK1),sK0) | ~v1_relat_1(sK1)),
% 0.22/0.45    inference(resolution,[],[f21,f18])).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    v5_relat_1(sK1,sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ( ! [X0,X1] : (~v5_relat_1(X1,X0) | r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(nnf_transformation,[],[f7])).
% 0.22/0.45  fof(f7,plain,(
% 0.22/0.45    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).
% 0.22/0.45  fof(f31,plain,(
% 0.22/0.45    ( ! [X0] : (~r1_tarski(k2_relat_1(sK1),X0) | r2_hidden(sK2,X0)) )),
% 0.22/0.45    inference(resolution,[],[f23,f19])).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    r2_hidden(sK2,k2_relat_1(sK1))),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X0,X3,X1] : (~r2_hidden(X3,X0) | r2_hidden(X3,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f14,f15])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.45    inference(rectify,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.45    inference(nnf_transformation,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (25257)------------------------------
% 0.22/0.45  % (25257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (25257)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (25257)Memory used [KB]: 895
% 0.22/0.45  % (25257)Time elapsed: 0.051 s
% 0.22/0.45  % (25257)------------------------------
% 0.22/0.45  % (25257)------------------------------
% 0.22/0.45  % (25246)Success in time 0.091 s
%------------------------------------------------------------------------------
