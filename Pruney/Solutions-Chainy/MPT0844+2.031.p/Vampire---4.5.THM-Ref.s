%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:05 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   47 (  83 expanded)
%              Number of leaves         :    8 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :  112 ( 225 expanded)
%              Number of equality atoms :   23 (  43 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f62,plain,(
    $false ),
    inference(subsumption_resolution,[],[f61,f58])).

fof(f58,plain,(
    k1_xboole_0 = k7_relat_1(sK3,sK1) ),
    inference(forward_demodulation,[],[f57,f41])).

fof(f41,plain,(
    sK3 = k7_relat_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f40,f35])).

fof(f35,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f34,f25])).

fof(f25,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f34,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK2,sK0))
    | v1_relat_1(sK3) ),
    inference(resolution,[],[f24,f21])).

fof(f21,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( k1_xboole_0 != k5_relset_1(X2,X0,X3,X1)
      & r1_xboole_0(X1,X2)
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
       => ( r1_xboole_0(X1,X2)
         => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
     => ( r1_xboole_0(X1,X2)
       => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f40,plain,
    ( ~ v1_relat_1(sK3)
    | sK3 = k7_relat_1(sK3,sK2) ),
    inference(resolution,[],[f29,f38])).

fof(f38,plain,(
    v4_relat_1(sK3,sK2) ),
    inference(resolution,[],[f31,f21])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f57,plain,(
    k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1) ),
    inference(resolution,[],[f53,f35])).

fof(f53,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X1,sK2),sK1) ) ),
    inference(resolution,[],[f30,f46])).

fof(f46,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f44,f22])).

fof(f22,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f44,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f43])).

fof(f43,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X2)
      | ~ r1_xboole_0(X2,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2)
      | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

fof(f61,plain,(
    k1_xboole_0 != k7_relat_1(sK3,sK1) ),
    inference(superposition,[],[f23,f60])).

fof(f60,plain,(
    ! [X0] : k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0) ),
    inference(resolution,[],[f33,f21])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

fof(f23,plain,(
    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:21:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (22629)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.47  % (22621)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.47  % (22621)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f61,f58])).
% 0.22/0.47  fof(f58,plain,(
% 0.22/0.47    k1_xboole_0 = k7_relat_1(sK3,sK1)),
% 0.22/0.47    inference(forward_demodulation,[],[f57,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    sK3 = k7_relat_1(sK3,sK2)),
% 0.22/0.47    inference(subsumption_resolution,[],[f40,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    v1_relat_1(sK3)),
% 0.22/0.47    inference(subsumption_resolution,[],[f34,f25])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ~v1_relat_1(k2_zfmisc_1(sK2,sK0)) | v1_relat_1(sK3)),
% 0.22/0.47    inference(resolution,[],[f24,f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : (k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.47    inference(flattening,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ? [X0,X1,X2,X3] : ((k1_xboole_0 != k5_relset_1(X2,X0,X3,X1) & r1_xboole_0(X1,X2)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.22/0.47    inference(negated_conjecture,[],[f8])).
% 0.22/0.47  fof(f8,conjecture,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => (r1_xboole_0(X1,X2) => k1_xboole_0 = k5_relset_1(X2,X0,X3,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relset_1)).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0) | v1_relat_1(X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.22/0.47  fof(f40,plain,(
% 0.22/0.47    ~v1_relat_1(sK3) | sK3 = k7_relat_1(sK3,sK2)),
% 0.22/0.47    inference(resolution,[],[f29,f38])).
% 0.22/0.47  fof(f38,plain,(
% 0.22/0.47    v4_relat_1(sK3,sK2)),
% 0.22/0.47    inference(resolution,[],[f31,f21])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_relat_1(X1) | k7_relat_1(X1,X0) = X1) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.22/0.47    inference(flattening,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    k1_xboole_0 = k7_relat_1(k7_relat_1(sK3,sK2),sK1)),
% 0.22/0.47    inference(resolution,[],[f53,f35])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    ( ! [X1] : (~v1_relat_1(X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(X1,sK2),sK1)) )),
% 0.22/0.47    inference(resolution,[],[f30,f46])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    r1_xboole_0(sK2,sK1)),
% 0.22/0.47    inference(resolution,[],[f44,f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    r1_xboole_0(sK1,sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 0.22/0.47    inference(resolution,[],[f36,f28])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.47    inference(rectify,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1),X2) | ~r1_xboole_0(X2,X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(resolution,[],[f26,f27])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~v1_relat_1(X2) | k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(flattening,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k7_relat_1(k7_relat_1(X2,X0),X1) = k1_xboole_0))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).
% 0.22/0.47  fof(f61,plain,(
% 0.22/0.47    k1_xboole_0 != k7_relat_1(sK3,sK1)),
% 0.22/0.47    inference(superposition,[],[f23,f60])).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    ( ! [X0] : (k5_relset_1(sK2,sK0,sK3,X0) = k7_relat_1(sK3,X0)) )),
% 0.22/0.47    inference(resolution,[],[f33,f21])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k5_relset_1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    k1_xboole_0 != k5_relset_1(sK2,sK0,sK3,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f12])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (22621)------------------------------
% 0.22/0.47  % (22621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (22621)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (22621)Memory used [KB]: 6140
% 0.22/0.47  % (22621)Time elapsed: 0.058 s
% 0.22/0.47  % (22621)------------------------------
% 0.22/0.47  % (22621)------------------------------
% 0.22/0.48  % (22607)Success in time 0.11 s
%------------------------------------------------------------------------------
