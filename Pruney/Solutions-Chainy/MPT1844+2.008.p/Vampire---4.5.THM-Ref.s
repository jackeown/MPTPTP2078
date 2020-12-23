%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:33 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  64 expanded)
%              Number of leaves         :    6 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   88 ( 284 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28,plain,(
    $false ),
    inference(subsumption_resolution,[],[f27,f26])).

fof(f26,plain,(
    ~ v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f18,f19,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f19,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_struct_0(sK0)
    & ~ v7_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_struct_0(sK0)
      & ~ v7_struct_0(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

fof(f18,plain,(
    ~ v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f27,plain,(
    v1_zfmisc_1(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f25,f20,f21,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_subset_1(k6_domain_1(X0,X1),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(f21,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f20,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f16])).

fof(f25,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f17,f19,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f17,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:42:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (2260)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.22/0.45  % (2260)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.45  % SZS output start Proof for theBenchmark
% 0.22/0.45  fof(f28,plain,(
% 0.22/0.45    $false),
% 0.22/0.45    inference(subsumption_resolution,[],[f27,f26])).
% 0.22/0.45  fof(f26,plain,(
% 0.22/0.45    ~v1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f18,f19,f24])).
% 0.22/0.45  fof(f24,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f13])).
% 0.22/0.45  fof(f13,plain,(
% 0.22/0.45    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f12])).
% 0.22/0.45  fof(f12,plain,(
% 0.22/0.45    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f2])).
% 0.22/0.45  fof(f2,axiom,(
% 0.22/0.45    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.22/0.45  fof(f19,plain,(
% 0.22/0.45    l1_struct_0(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f16,plain,(
% 0.22/0.45    (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v7_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f15,f14])).
% 0.22/0.45  fof(f14,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v7_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f15,plain,(
% 0.22/0.45    ? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.45    introduced(choice_axiom,[])).
% 0.22/0.45  fof(f7,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f6])).
% 0.22/0.45  fof(f6,plain,(
% 0.22/0.45    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f5])).
% 0.22/0.45  fof(f5,negated_conjecture,(
% 0.22/0.45    ~! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 0.22/0.45    inference(negated_conjecture,[],[f4])).
% 0.22/0.45  fof(f4,conjecture,(
% 0.22/0.45    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).
% 0.22/0.45  fof(f18,plain,(
% 0.22/0.45    ~v7_struct_0(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f27,plain,(
% 0.22/0.45    v1_zfmisc_1(u1_struct_0(sK0))),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f25,f20,f21,f22])).
% 0.22/0.45  fof(f22,plain,(
% 0.22/0.45    ( ! [X0,X1] : (v1_zfmisc_1(X0) | ~m1_subset_1(X1,X0) | v1_subset_1(k6_domain_1(X0,X1),X0) | v1_xboole_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f9])).
% 0.22/0.45  fof(f9,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.22/0.45    inference(flattening,[],[f8])).
% 0.22/0.45  fof(f8,plain,(
% 0.22/0.45    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f3])).
% 0.22/0.45  fof(f3,axiom,(
% 0.22/0.45    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 0.22/0.45  fof(f21,plain,(
% 0.22/0.45    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f20,plain,(
% 0.22/0.45    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  fof(f25,plain,(
% 0.22/0.45    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.45    inference(unit_resulting_resolution,[],[f17,f19,f23])).
% 0.22/0.45  fof(f23,plain,(
% 0.22/0.45    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.45    inference(cnf_transformation,[],[f11])).
% 0.22/0.45  fof(f11,plain,(
% 0.22/0.45    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.45    inference(flattening,[],[f10])).
% 0.22/0.45  fof(f10,plain,(
% 0.22/0.45    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.45    inference(ennf_transformation,[],[f1])).
% 0.22/0.45  fof(f1,axiom,(
% 0.22/0.45    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.45  fof(f17,plain,(
% 0.22/0.45    ~v2_struct_0(sK0)),
% 0.22/0.45    inference(cnf_transformation,[],[f16])).
% 0.22/0.45  % SZS output end Proof for theBenchmark
% 0.22/0.45  % (2260)------------------------------
% 0.22/0.45  % (2260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.45  % (2260)Termination reason: Refutation
% 0.22/0.45  
% 0.22/0.45  % (2260)Memory used [KB]: 9850
% 0.22/0.45  % (2260)Time elapsed: 0.058 s
% 0.22/0.45  % (2260)------------------------------
% 0.22/0.45  % (2260)------------------------------
% 0.22/0.45  % (2256)Success in time 0.086 s
%------------------------------------------------------------------------------
