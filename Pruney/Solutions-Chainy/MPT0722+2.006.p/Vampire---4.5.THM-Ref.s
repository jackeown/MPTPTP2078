%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:07 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   26 (  78 expanded)
%              Number of leaves         :    5 (  26 expanded)
%              Depth                    :    9
%              Number of atoms          :   93 ( 383 expanded)
%              Number of equality atoms :   23 (  86 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    $false ),
    inference(global_subsumption,[],[f24,f25])).

fof(f25,plain,(
    sK1 != k10_relat_1(sK0,k9_relat_1(sK0,sK1)) ),
    inference(superposition,[],[f18,f22])).

fof(f22,plain,(
    ! [X0] : k10_relat_1(sK0,X0) = k9_relat_1(k2_funct_1(sK0),X0) ),
    inference(global_subsumption,[],[f15,f14,f21])).

fof(f21,plain,(
    ! [X0] :
      ( k10_relat_1(sK0,X0) = k9_relat_1(k2_funct_1(sK0),X0)
      | ~ v1_funct_1(sK0)
      | ~ v1_relat_1(sK0) ) ),
    inference(resolution,[],[f19,f16])).

fof(f16,plain,(
    v2_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))
    & r1_tarski(sK1,k1_relat_1(sK0))
    & v2_funct_1(sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f12,f11])).

fof(f11,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
            & r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ? [X1] :
          ( k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(sK0))
          & v2_funct_1(sK0) )
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,
    ( ? [X1] :
        ( k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1
        & r1_tarski(X1,k1_relat_1(sK0))
        & v2_funct_1(sK0) )
   => ( sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))
      & r1_tarski(sK1,k1_relat_1(sK0))
      & v2_funct_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1
          & r1_tarski(X1,k1_relat_1(X0))
          & v2_funct_1(X0) )
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => ! [X1] :
            ( ( r1_tarski(X1,k1_relat_1(X0))
              & v2_funct_1(X0) )
           => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f14,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f15,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f24,plain,(
    sK1 = k10_relat_1(sK0,k9_relat_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f16,f15,f14,f23])).

fof(f23,plain,
    ( ~ v2_funct_1(sK0)
    | sK1 = k10_relat_1(sK0,k9_relat_1(sK0,sK1))
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f20,f17])).

fof(f17,plain,(
    r1_tarski(sK1,k1_relat_1(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:59:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (23032)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.41  % (23032)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(global_subsumption,[],[f24,f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    sK1 != k10_relat_1(sK0,k9_relat_1(sK0,sK1))),
% 0.21/0.41    inference(superposition,[],[f18,f22])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    ( ! [X0] : (k10_relat_1(sK0,X0) = k9_relat_1(k2_funct_1(sK0),X0)) )),
% 0.21/0.41    inference(global_subsumption,[],[f15,f14,f21])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ( ! [X0] : (k10_relat_1(sK0,X0) = k9_relat_1(k2_funct_1(sK0),X0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)) )),
% 0.21/0.41    inference(resolution,[],[f19,f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    v2_funct_1(sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    (sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) & r1_tarski(sK1,k1_relat_1(sK0)) & v2_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f6,f12,f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ? [X0] : (? [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1 & r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1 & r1_tarski(X1,k1_relat_1(sK0)) & v2_funct_1(sK0)) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ? [X1] : (k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,X1)) != X1 & r1_tarski(X1,k1_relat_1(sK0)) & v2_funct_1(sK0)) => (sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1)) & r1_tarski(sK1,k1_relat_1(sK0)) & v2_funct_1(sK0))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f6,plain,(
% 0.21/0.41    ? [X0] : (? [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1 & r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) & v1_funct_1(X0) & v1_relat_1(X0))),
% 0.21/0.41    inference(flattening,[],[f5])).
% 0.21/0.41  fof(f5,plain,(
% 0.21/0.41    ? [X0] : (? [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) != X1 & (r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0))) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,negated_conjecture,(
% 0.21/0.41    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.21/0.41    inference(negated_conjecture,[],[f3])).
% 0.21/0.41  fof(f3,conjecture,(
% 0.21/0.41    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f8])).
% 0.21/0.41  fof(f8,plain,(
% 0.21/0.41    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(flattening,[],[f7])).
% 0.21/0.41  fof(f7,plain,(
% 0.21/0.41    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.41    inference(ennf_transformation,[],[f1])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    v1_relat_1(sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    v1_funct_1(sK0)),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    sK1 != k9_relat_1(k2_funct_1(sK0),k9_relat_1(sK0,sK1))),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    sK1 = k10_relat_1(sK0,k9_relat_1(sK0,sK1))),
% 0.21/0.41    inference(global_subsumption,[],[f16,f15,f14,f23])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ~v2_funct_1(sK0) | sK1 = k10_relat_1(sK0,k9_relat_1(sK0,sK1)) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 0.21/0.41    inference(resolution,[],[f20,f17])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    r1_tarski(sK1,k1_relat_1(sK0))),
% 0.21/0.41    inference(cnf_transformation,[],[f13])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~r1_tarski(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f10])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.41    inference(flattening,[],[f9])).
% 0.21/0.41  fof(f9,plain,(
% 0.21/0.41    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.41    inference(ennf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).
% 0.21/0.41  % SZS output end Proof for theBenchmark
% 0.21/0.41  % (23032)------------------------------
% 0.21/0.41  % (23032)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.41  % (23032)Termination reason: Refutation
% 0.21/0.41  
% 0.21/0.41  % (23032)Memory used [KB]: 10490
% 0.21/0.41  % (23032)Time elapsed: 0.005 s
% 0.21/0.41  % (23032)------------------------------
% 0.21/0.41  % (23032)------------------------------
% 0.21/0.41  % (23020)Success in time 0.058 s
%------------------------------------------------------------------------------
