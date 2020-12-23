%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:49:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   36 (  95 expanded)
%              Number of leaves         :    7 (  30 expanded)
%              Depth                    :   15
%              Number of atoms          :  110 ( 364 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(global_subsumption,[],[f18,f47])).

fof(f47,plain,(
    ~ v1_relat_1(sK1) ),
    inference(resolution,[],[f46,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f46,plain,(
    ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(global_subsumption,[],[f19,f45])).

fof(f45,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f44,f24])).

fof(f44,plain,
    ( ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(global_subsumption,[],[f20,f19,f18,f43])).

fof(f43,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f26,f42])).

fof(f42,plain,
    ( ~ r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK2,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0)) ),
    inference(resolution,[],[f35,f21])).

fof(f21,plain,(
    ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))
    & r1_tarski(sK1,sK2)
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f16,f15])).

% (10697)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
fof(f15,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
            & r1_tarski(X1,X2)
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0))
          & r1_tarski(sK1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0))
        & r1_tarski(sK1,X2)
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))
      & r1_tarski(sK1,sK2)
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0))
          & r1_tarski(X1,X2)
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => ( r1_tarski(X1,X2)
             => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).

fof(f35,plain,(
    ! [X2,X3] :
      ( r1_tarski(k9_relat_1(sK1,X3),k9_relat_1(sK2,X2))
      | ~ r1_tarski(k7_relat_1(sK1,X3),k7_relat_1(sK2,X2))
      | ~ v1_relat_1(k7_relat_1(sK2,X2))
      | ~ v1_relat_1(k7_relat_1(sK1,X3)) ) ),
    inference(superposition,[],[f30,f28])).

fof(f28,plain,(
    ! [X1] : k2_relat_1(k7_relat_1(sK2,X1)) = k9_relat_1(sK2,X1) ),
    inference(resolution,[],[f25,f19])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(sK1,X0),k2_relat_1(X1))
      | ~ r1_tarski(k7_relat_1(sK1,X0),X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(k7_relat_1(sK1,X0)) ) ),
    inference(superposition,[],[f23,f27])).

fof(f27,plain,(
    ! [X0] : k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0) ),
    inference(resolution,[],[f25,f18])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(X0,X1)
           => ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
              & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
      | ~ r1_tarski(X1,X2)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0))
          | ~ r1_tarski(X1,X2)
          | ~ v1_relat_1(X2) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => ( r1_tarski(X1,X2)
           => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

fof(f20,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f19,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f18,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.20/0.35  % CPULimit   : 60
% 0.20/0.35  % WCLimit    : 600
% 0.20/0.35  % DateTime   : Tue Dec  1 14:40:56 EST 2020
% 0.20/0.35  % CPUTime    : 
% 0.22/0.43  % (10696)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.44  % (10695)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.44  % (10698)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.44  % (10695)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(global_subsumption,[],[f18,f47])).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    ~v1_relat_1(sK1)),
% 0.22/0.44    inference(resolution,[],[f46,f24])).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.22/0.44  fof(f46,plain,(
% 0.22/0.44    ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.44    inference(global_subsumption,[],[f19,f45])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(sK2)),
% 0.22/0.44    inference(resolution,[],[f44,f24])).
% 0.22/0.44  fof(f44,plain,(
% 0.22/0.44    ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.44    inference(global_subsumption,[],[f20,f19,f18,f43])).
% 0.22/0.44  fof(f43,plain,(
% 0.22/0.44    ~r1_tarski(sK1,sK2) | ~v1_relat_1(sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.44    inference(resolution,[],[f26,f42])).
% 0.22/0.44  fof(f42,plain,(
% 0.22/0.44    ~r1_tarski(k7_relat_1(sK1,sK0),k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK2,sK0)) | ~v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.22/0.44    inference(resolution,[],[f35,f21])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0))),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f16,f15])).
% 0.22/0.44  % (10697)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : (~r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) & r1_tarski(X1,X2) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0)) & r1_tarski(sK1,X2) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ? [X2] : (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(X2,sK0)) & r1_tarski(sK1,X2) & v1_relat_1(X2)) => (~r1_tarski(k9_relat_1(sK1,sK0),k9_relat_1(sK2,sK0)) & r1_tarski(sK1,sK2) & v1_relat_1(sK2))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : (~r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) & r1_tarski(X1,X2) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f7])).
% 0.22/0.44  fof(f7,plain,(
% 0.22/0.44    ? [X0,X1] : (? [X2] : ((~r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)) & r1_tarski(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 0.22/0.44    inference(negated_conjecture,[],[f5])).
% 0.22/0.44  fof(f5,conjecture,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k9_relat_1(X1,X0),k9_relat_1(X2,X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t157_relat_1)).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X2,X3] : (r1_tarski(k9_relat_1(sK1,X3),k9_relat_1(sK2,X2)) | ~r1_tarski(k7_relat_1(sK1,X3),k7_relat_1(sK2,X2)) | ~v1_relat_1(k7_relat_1(sK2,X2)) | ~v1_relat_1(k7_relat_1(sK1,X3))) )),
% 0.22/0.44    inference(superposition,[],[f30,f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X1] : (k2_relat_1(k7_relat_1(sK2,X1)) = k9_relat_1(sK2,X1)) )),
% 0.22/0.44    inference(resolution,[],[f25,f19])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k9_relat_1(sK1,X0),k2_relat_1(X1)) | ~r1_tarski(k7_relat_1(sK1,X0),X1) | ~v1_relat_1(X1) | ~v1_relat_1(k7_relat_1(sK1,X0))) )),
% 0.22/0.44    inference(superposition,[],[f23,f27])).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X0] : (k2_relat_1(k7_relat_1(sK1,X0)) = k9_relat_1(sK1,X0)) )),
% 0.22/0.44    inference(resolution,[],[f25,f18])).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(flattening,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.44    inference(ennf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2) | ~v1_relat_1(X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : (r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(flattening,[],[f13])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)) | ~r1_tarski(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X1,X2) => r1_tarski(k7_relat_1(X1,X0),k7_relat_1(X2,X0)))))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    r1_tarski(sK1,sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    v1_relat_1(sK2)),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    v1_relat_1(sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f17])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (10695)------------------------------
% 0.22/0.44  % (10695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (10695)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (10695)Memory used [KB]: 6140
% 0.22/0.44  % (10695)Time elapsed: 0.005 s
% 0.22/0.44  % (10695)------------------------------
% 0.22/0.44  % (10695)------------------------------
% 0.22/0.44  % (10690)Success in time 0.077 s
%------------------------------------------------------------------------------
