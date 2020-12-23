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
% DateTime   : Thu Dec  3 12:56:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   20 (  32 expanded)
%              Number of leaves         :    4 (   8 expanded)
%              Depth                    :   10
%              Number of atoms          :   46 (  79 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f26,plain,(
    $false ),
    inference(resolution,[],[f25,f9])).

fof(f9,plain,(
    ~ r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] : ~ r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relset_1)).

fof(f25,plain,(
    ! [X12] : r1_tarski(k6_relat_1(X12),k2_zfmisc_1(X12,X12)) ),
    inference(subsumption_resolution,[],[f24,f10])).

fof(f10,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f24,plain,(
    ! [X12] :
      ( r1_tarski(k6_relat_1(X12),k2_zfmisc_1(X12,X12))
      | ~ v1_relat_1(k2_zfmisc_1(X12,X12)) ) ),
    inference(duplicate_literal_removal,[],[f21])).

fof(f21,plain,(
    ! [X12] :
      ( r1_tarski(k6_relat_1(X12),k2_zfmisc_1(X12,X12))
      | r1_tarski(k6_relat_1(X12),k2_zfmisc_1(X12,X12))
      | ~ v1_relat_1(k2_zfmisc_1(X12,X12))
      | r1_tarski(k6_relat_1(X12),k2_zfmisc_1(X12,X12)) ) ),
    inference(resolution,[],[f18,f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1)
      | ~ v1_relat_1(X1)
      | r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_relat_1(X0),X1)
      | ? [X2] :
          ( ~ r2_hidden(k4_tarski(X2,X2),X1)
          & r2_hidden(X2,X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( ! [X2] :
            ( r2_hidden(X2,X0)
           => r2_hidden(k4_tarski(X2,X2),X1) )
       => r1_tarski(k6_relat_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).

fof(f18,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,k2_zfmisc_1(X1,X2)),sK1(X3,k2_zfmisc_1(X4,X5))),k2_zfmisc_1(X0,X3))
      | r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X1,X2))
      | r1_tarski(k6_relat_1(X3),k2_zfmisc_1(X4,X5)) ) ),
    inference(resolution,[],[f17,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X0)
      | r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f11,f10])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r2_hidden(sK1(X0,X1),X0)
      | r1_tarski(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X4)
      | r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X1,X2))
      | r2_hidden(k4_tarski(sK1(X0,k2_zfmisc_1(X1,X2)),X3),k2_zfmisc_1(X0,X4)) ) ),
    inference(resolution,[],[f16,f15])).

fof(f15,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n009.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:03:56 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.45  % (26968)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.22/0.47  % (26976)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.22/0.47  % (26968)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(resolution,[],[f25,f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ~r1_tarski(k6_relat_1(sK0),k2_zfmisc_1(sK0,sK0))),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,plain,(
% 0.22/0.47    ? [X0] : ~r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,negated_conjecture,(
% 0.22/0.47    ~! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.47    inference(negated_conjecture,[],[f4])).
% 0.22/0.47  fof(f4,conjecture,(
% 0.22/0.47    ! [X0] : r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X0,X0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relset_1)).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X12] : (r1_tarski(k6_relat_1(X12),k2_zfmisc_1(X12,X12))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f24,f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X12] : (r1_tarski(k6_relat_1(X12),k2_zfmisc_1(X12,X12)) | ~v1_relat_1(k2_zfmisc_1(X12,X12))) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X12] : (r1_tarski(k6_relat_1(X12),k2_zfmisc_1(X12,X12)) | r1_tarski(k6_relat_1(X12),k2_zfmisc_1(X12,X12)) | ~v1_relat_1(k2_zfmisc_1(X12,X12)) | r1_tarski(k6_relat_1(X12),k2_zfmisc_1(X12,X12))) )),
% 0.22/0.47    inference(resolution,[],[f18,f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(k4_tarski(sK1(X0,X1),sK1(X0,X1)),X1) | ~v1_relat_1(X1) | r1_tarski(k6_relat_1(X0),X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,plain,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0)) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f7])).
% 0.22/0.47  fof(f7,plain,(
% 0.22/0.47    ! [X0,X1] : ((r1_tarski(k6_relat_1(X0),X1) | ? [X2] : (~r2_hidden(k4_tarski(X2,X2),X1) & r2_hidden(X2,X0))) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : (v1_relat_1(X1) => (! [X2] : (r2_hidden(X2,X0) => r2_hidden(k4_tarski(X2,X2),X1)) => r1_tarski(k6_relat_1(X0),X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (r2_hidden(k4_tarski(sK1(X0,k2_zfmisc_1(X1,X2)),sK1(X3,k2_zfmisc_1(X4,X5))),k2_zfmisc_1(X0,X3)) | r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X1,X2)) | r1_tarski(k6_relat_1(X3),k2_zfmisc_1(X4,X5))) )),
% 0.22/0.47    inference(resolution,[],[f17,f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,k2_zfmisc_1(X1,X2)),X0) | r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X1,X2))) )),
% 0.22/0.47    inference(resolution,[],[f11,f10])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | r2_hidden(sK1(X0,X1),X0) | r1_tarski(k6_relat_1(X0),X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f8])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ( ! [X4,X2,X0,X3,X1] : (~r2_hidden(X3,X4) | r1_tarski(k6_relat_1(X0),k2_zfmisc_1(X1,X2)) | r2_hidden(k4_tarski(sK1(X0,k2_zfmisc_1(X1,X2)),X3),k2_zfmisc_1(X0,X4))) )),
% 0.22/0.47    inference(resolution,[],[f16,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (26968)------------------------------
% 0.22/0.47  % (26968)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (26968)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (26968)Memory used [KB]: 5373
% 0.22/0.47  % (26968)Time elapsed: 0.067 s
% 0.22/0.47  % (26968)------------------------------
% 0.22/0.47  % (26968)------------------------------
% 0.22/0.47  % (26961)Success in time 0.108 s
%------------------------------------------------------------------------------
