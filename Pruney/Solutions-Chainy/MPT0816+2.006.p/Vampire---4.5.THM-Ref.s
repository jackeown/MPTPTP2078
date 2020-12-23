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
% DateTime   : Thu Dec  3 12:56:14 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   33 (  54 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :   11
%              Number of atoms          :   67 ( 139 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f161,plain,(
    $false ),
    inference(subsumption_resolution,[],[f160,f16])).

fof(f16,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & r1_tarski(k2_relat_1(X2),X1)
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & r1_tarski(k2_relat_1(X2),X1)
      & r1_tarski(k1_relat_1(X2),X0)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( v1_relat_1(X2)
       => ( ( r1_tarski(k2_relat_1(X2),X1)
            & r1_tarski(k1_relat_1(X2),X0) )
         => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( ( r1_tarski(k2_relat_1(X2),X1)
          & r1_tarski(k1_relat_1(X2),X0) )
       => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

fof(f160,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(resolution,[],[f76,f100])).

fof(f100,plain,(
    r1_tarski(sK2,k2_zfmisc_1(sK0,k2_relat_1(sK2))) ),
    inference(resolution,[],[f98,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f98,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2)))) ),
    inference(resolution,[],[f73,f27])).

fof(f27,plain,(
    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) ),
    inference(resolution,[],[f17,f13])).

fof(f13,plain,(
    v1_relat_1(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(k1_relat_1(sK2),X1))
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1))) ) ),
    inference(resolution,[],[f22,f33])).

fof(f33,plain,(
    ! [X2] : m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),X2),k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) ),
    inference(resolution,[],[f29,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f29,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),X0),k2_zfmisc_1(sK0,X0)) ),
    inference(resolution,[],[f20,f14])).

fof(f14,plain,(
    r1_tarski(k1_relat_1(sK2),sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r1_tarski(X0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
     => ( r1_tarski(X0,X3)
       => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

fof(f76,plain,(
    ! [X6,X7] :
      ( ~ r1_tarski(X6,k2_zfmisc_1(X7,k2_relat_1(sK2)))
      | m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,sK1))) ) ),
    inference(resolution,[],[f22,f58])).

fof(f58,plain,(
    ! [X4] : m1_subset_1(k2_zfmisc_1(X4,k2_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) ),
    inference(resolution,[],[f51,f18])).

fof(f51,plain,(
    ! [X13] : r1_tarski(k2_zfmisc_1(X13,k2_relat_1(sK2)),k2_zfmisc_1(X13,sK1)) ),
    inference(resolution,[],[f21,f15])).

fof(f15,plain,(
    r1_tarski(k2_relat_1(sK2),sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:05:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.42  % (6148)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.23/0.42  % (6148)Refutation not found, incomplete strategy% (6148)------------------------------
% 0.23/0.42  % (6148)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.42  % (6148)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.42  
% 0.23/0.42  % (6148)Memory used [KB]: 9722
% 0.23/0.42  % (6148)Time elapsed: 0.003 s
% 0.23/0.42  % (6148)------------------------------
% 0.23/0.42  % (6148)------------------------------
% 0.23/0.46  % (6157)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.23/0.49  % (6151)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 0.23/0.49  % (6145)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.23/0.49  % (6145)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  fof(f161,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(subsumption_resolution,[],[f160,f16])).
% 0.23/0.49  fof(f16,plain,(
% 0.23/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.49    inference(cnf_transformation,[],[f8])).
% 0.23/0.49  fof(f8,plain,(
% 0.23/0.49    ? [X0,X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0) & v1_relat_1(X2))),
% 0.23/0.49    inference(flattening,[],[f7])).
% 0.23/0.49  fof(f7,plain,(
% 0.23/0.49    ? [X0,X1,X2] : ((~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & (r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0))) & v1_relat_1(X2))),
% 0.23/0.49    inference(ennf_transformation,[],[f6])).
% 0.23/0.49  fof(f6,negated_conjecture,(
% 0.23/0.49    ~! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.23/0.49    inference(negated_conjecture,[],[f5])).
% 0.23/0.49  fof(f5,conjecture,(
% 0.23/0.49    ! [X0,X1,X2] : (v1_relat_1(X2) => ((r1_tarski(k2_relat_1(X2),X1) & r1_tarski(k1_relat_1(X2),X0)) => m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).
% 0.23/0.49  fof(f160,plain,(
% 0.23/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.23/0.49    inference(resolution,[],[f76,f100])).
% 0.23/0.49  fof(f100,plain,(
% 0.23/0.49    r1_tarski(sK2,k2_zfmisc_1(sK0,k2_relat_1(sK2)))),
% 0.23/0.49    inference(resolution,[],[f98,f19])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.23/0.49  fof(f98,plain,(
% 0.23/0.49    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,k2_relat_1(sK2))))),
% 0.23/0.49    inference(resolution,[],[f73,f27])).
% 0.23/0.49  fof(f27,plain,(
% 0.23/0.49    r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.23/0.49    inference(resolution,[],[f17,f13])).
% 0.23/0.49  fof(f13,plain,(
% 0.23/0.49    v1_relat_1(sK2)),
% 0.23/0.49    inference(cnf_transformation,[],[f8])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ( ! [X0] : (~v1_relat_1(X0) | r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f9])).
% 0.23/0.49  fof(f9,plain,(
% 0.23/0.49    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.23/0.49    inference(ennf_transformation,[],[f3])).
% 0.23/0.49  fof(f3,axiom,(
% 0.23/0.49    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.23/0.49  fof(f73,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(k1_relat_1(sK2),X1)) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,X1)))) )),
% 0.23/0.49    inference(resolution,[],[f22,f33])).
% 0.23/0.49  fof(f33,plain,(
% 0.23/0.49    ( ! [X2] : (m1_subset_1(k2_zfmisc_1(k1_relat_1(sK2),X2),k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))) )),
% 0.23/0.49    inference(resolution,[],[f29,f18])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f2])).
% 0.23/0.49  fof(f29,plain,(
% 0.23/0.49    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),X0),k2_zfmisc_1(sK0,X0))) )),
% 0.23/0.49    inference(resolution,[],[f20,f14])).
% 0.23/0.49  fof(f14,plain,(
% 0.23/0.49    r1_tarski(k1_relat_1(sK2),sK0)),
% 0.23/0.49    inference(cnf_transformation,[],[f8])).
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f10])).
% 0.23/0.49  fof(f10,plain,(
% 0.23/0.49    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f12])).
% 0.23/0.49  fof(f12,plain,(
% 0.23/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.23/0.49    inference(flattening,[],[f11])).
% 0.23/0.49  fof(f11,plain,(
% 0.23/0.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))))),
% 0.23/0.49    inference(ennf_transformation,[],[f4])).
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) => (r1_tarski(X0,X3) => m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).
% 0.23/0.49  fof(f76,plain,(
% 0.23/0.49    ( ! [X6,X7] : (~r1_tarski(X6,k2_zfmisc_1(X7,k2_relat_1(sK2))) | m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,sK1)))) )),
% 0.23/0.49    inference(resolution,[],[f22,f58])).
% 0.23/0.49  fof(f58,plain,(
% 0.23/0.49    ( ! [X4] : (m1_subset_1(k2_zfmisc_1(X4,k2_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))) )),
% 0.23/0.49    inference(resolution,[],[f51,f18])).
% 0.23/0.49  fof(f51,plain,(
% 0.23/0.49    ( ! [X13] : (r1_tarski(k2_zfmisc_1(X13,k2_relat_1(sK2)),k2_zfmisc_1(X13,sK1))) )),
% 0.23/0.49    inference(resolution,[],[f21,f15])).
% 0.23/0.49  fof(f15,plain,(
% 0.23/0.49    r1_tarski(k2_relat_1(sK2),sK1)),
% 0.23/0.49    inference(cnf_transformation,[],[f8])).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f10])).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (6145)------------------------------
% 0.23/0.49  % (6145)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (6145)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (6145)Memory used [KB]: 5373
% 0.23/0.49  % (6145)Time elapsed: 0.060 s
% 0.23/0.49  % (6145)------------------------------
% 0.23/0.49  % (6145)------------------------------
% 0.23/0.49  % (6138)Success in time 0.125 s
%------------------------------------------------------------------------------
