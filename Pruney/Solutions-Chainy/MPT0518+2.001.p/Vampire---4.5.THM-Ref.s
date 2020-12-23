%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   28 (  55 expanded)
%              Number of leaves         :    6 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 127 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(subsumption_resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X1] : v1_relat_1(k8_relat_1(X1,sK1)) ),
    inference(resolution,[],[f37,f23])).

fof(f23,plain,(
    ! [X0] : r1_tarski(k8_relat_1(X0,sK1),sK1) ),
    inference(resolution,[],[f15,f20])).

fof(f20,plain,(
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

fof(f15,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(sK1))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12])).

fof(f12,plain,
    ( ? [X0,X1] :
        ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
        & v1_relat_1(X1) )
   => ( ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(sK1))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1] :
      ( ~ r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_relat_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f24,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f24,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK1))
      | v1_relat_1(X1) ) ),
    inference(resolution,[],[f15,f19])).

fof(f19,plain,(
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

fof(f52,plain,(
    ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f31,f23])).

fof(f31,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f29,f15])).

fof(f29,plain,
    ( ~ r1_tarski(k8_relat_1(sK0,sK1),sK1)
    | ~ v1_relat_1(sK1)
    | ~ v1_relat_1(k8_relat_1(sK0,sK1)) ),
    inference(resolution,[],[f16,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tarski(k2_relat_1(X0),k2_relat_1(X1))
            & r1_tarski(k1_relat_1(X0),k1_relat_1(X1)) )
          | ~ r1_tarski(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
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

fof(f16,plain,(
    ~ r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(sK1)) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:26:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (13816)dis+11_3_awrs=decay:awrsf=256:av=off:gs=on:gsem=on:lcm=reverse:nm=0:nwc=1:sos=all:sp=frequency:updr=off_4 on theBenchmark
% 0.20/0.45  % (13816)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f52,f39])).
% 0.20/0.45  fof(f39,plain,(
% 0.20/0.45    ( ! [X1] : (v1_relat_1(k8_relat_1(X1,sK1))) )),
% 0.20/0.45    inference(resolution,[],[f37,f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ( ! [X0] : (r1_tarski(k8_relat_1(X0,sK1),sK1)) )),
% 0.20/0.45    inference(resolution,[],[f15,f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(k8_relat_1(X0,X1),X1) | ~v1_relat_1(X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k8_relat_1(X0,X1),X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    v1_relat_1(sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(sK1)) & v1_relat_1(sK1)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ? [X0,X1] : (~r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) & v1_relat_1(X1)) => (~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(sK1)) & v1_relat_1(sK1))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  fof(f7,plain,(
% 0.20/0.45    ? [X0,X1] : (~r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)) & v1_relat_1(X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)))),
% 0.20/0.45    inference(negated_conjecture,[],[f5])).
% 0.20/0.45  fof(f5,conjecture,(
% 0.20/0.45    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k8_relat_1(X0,X1)),k2_relat_1(X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_relat_1)).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_tarski(X0,sK1) | v1_relat_1(X0)) )),
% 0.20/0.45    inference(resolution,[],[f24,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.20/0.45    inference(nnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK1)) | v1_relat_1(X1)) )),
% 0.20/0.45    inference(resolution,[],[f15,f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.20/0.45    inference(subsumption_resolution,[],[f31,f23])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ~r1_tarski(k8_relat_1(sK0,sK1),sK1) | ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.20/0.45    inference(subsumption_resolution,[],[f29,f15])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ~r1_tarski(k8_relat_1(sK0,sK1),sK1) | ~v1_relat_1(sK1) | ~v1_relat_1(k8_relat_1(sK0,sK1))),
% 0.20/0.45    inference(resolution,[],[f16,f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(flattening,[],[f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (((r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_tarski(X0,X1) => (r1_tarski(k2_relat_1(X0),k2_relat_1(X1)) & r1_tarski(k1_relat_1(X0),k1_relat_1(X1))))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ~r1_tarski(k2_relat_1(k8_relat_1(sK0,sK1)),k2_relat_1(sK1))),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (13816)------------------------------
% 0.20/0.45  % (13816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (13816)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (13816)Memory used [KB]: 5373
% 0.20/0.45  % (13816)Time elapsed: 0.043 s
% 0.20/0.45  % (13816)------------------------------
% 0.20/0.45  % (13816)------------------------------
% 0.20/0.45  % (13804)Success in time 0.099 s
%------------------------------------------------------------------------------
