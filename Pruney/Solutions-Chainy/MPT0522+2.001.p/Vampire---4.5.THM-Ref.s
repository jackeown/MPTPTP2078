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
% DateTime   : Thu Dec  3 12:48:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   31 (  68 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :    9
%              Number of atoms          :   85 ( 205 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f61,plain,(
    $false ),
    inference(resolution,[],[f57,f45])).

fof(f45,plain,(
    ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f44,f17])).

fof(f17,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2))
    & v1_relat_1(sK2)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))
            & v1_relat_1(X2) )
        & v1_relat_1(X1) )
   => ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,X2)),k5_relat_1(sK1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,X2)),k5_relat_1(sK1,X2))
        & v1_relat_1(X2) )
   => ( ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2))
      & v1_relat_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))
          & v1_relat_1(X2) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ! [X2] :
            ( v1_relat_1(X2)
           => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ! [X2] :
          ( v1_relat_1(X2)
         => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_relat_1)).

fof(f44,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f43,f16])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,
    ( ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f41,f29])).

fof(f29,plain,(
    ! [X0] : r1_tarski(k8_relat_1(X0,sK2),sK2) ),
    inference(resolution,[],[f17,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k8_relat_1(X0,X1),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k8_relat_1(X0,X1),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

fof(f41,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK2),sK2)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ v1_relat_1(k8_relat_1(sK0,sK2)) ),
    inference(resolution,[],[f18,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))
              | ~ r1_tarski(X0,X1)
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => ( r1_tarski(X0,X1)
               => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).

fof(f18,plain,(
    ~ r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X0] : v1_relat_1(k8_relat_1(X0,sK2)) ),
    inference(resolution,[],[f56,f29])).

fof(f56,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f30,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f30,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK2))
      | v1_relat_1(X1) ) ),
    inference(resolution,[],[f17,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:55:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (7435)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.22/0.47  % (7448)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.47  % (7437)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.47  % (7445)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.22/0.48  % (7445)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(resolution,[],[f57,f45])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.22/0.48    inference(subsumption_resolution,[],[f44,f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    v1_relat_1(sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    (~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2)) & v1_relat_1(sK2)) & v1_relat_1(sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f13,f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1)) => (? [X2] : (~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,X2)),k5_relat_1(sK1,X2)) & v1_relat_1(X2)) & v1_relat_1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ? [X2] : (~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,X2)),k5_relat_1(sK1,X2)) & v1_relat_1(X2)) => (~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2)) & v1_relat_1(sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0,X1] : (? [X2] : (~r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2)) & v1_relat_1(X2)) & v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))))),
% 0.22/0.48    inference(negated_conjecture,[],[f5])).
% 0.22/0.48  fof(f5,conjecture,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => r1_tarski(k5_relat_1(X1,k8_relat_1(X0,X2)),k5_relat_1(X1,X2))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_relat_1)).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    ~v1_relat_1(sK2) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.22/0.48    inference(subsumption_resolution,[],[f43,f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.22/0.48    inference(subsumption_resolution,[],[f41,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK2),sK2)) )),
% 0.22/0.48    inference(resolution,[],[f17,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ~r1_tarski(k8_relat_1(sK0,sK2),sK2) | ~v1_relat_1(sK1) | ~v1_relat_1(sK2) | ~v1_relat_1(k8_relat_1(sK0,sK2))),
% 0.22/0.48    inference(resolution,[],[f18,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(flattening,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1)) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => r1_tarski(k5_relat_1(X2,X0),k5_relat_1(X2,X1))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_relat_1)).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ~r1_tarski(k5_relat_1(sK1,k8_relat_1(sK0,sK2)),k5_relat_1(sK1,sK2))),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X0] : (v1_relat_1(k8_relat_1(X0,sK2))) )),
% 0.22/0.48    inference(resolution,[],[f56,f29])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(X0,sK2) | v1_relat_1(X0)) )),
% 0.22/0.48    inference(resolution,[],[f30,f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.22/0.48    inference(nnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK2)) | v1_relat_1(X1)) )),
% 0.22/0.48    inference(resolution,[],[f17,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (7445)------------------------------
% 0.22/0.48  % (7445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7445)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (7445)Memory used [KB]: 5373
% 0.22/0.48  % (7445)Time elapsed: 0.054 s
% 0.22/0.48  % (7445)------------------------------
% 0.22/0.48  % (7445)------------------------------
% 0.22/0.48  % (7433)Success in time 0.111 s
%------------------------------------------------------------------------------
