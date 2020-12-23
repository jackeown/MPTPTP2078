%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:32 EST 2020

% Result     : Theorem 0.12s
% Output     : Refutation 0.12s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 105 expanded)
%              Number of leaves         :    7 (  33 expanded)
%              Depth                    :   12
%              Number of atoms          :  110 ( 440 expanded)
%              Number of equality atoms :    4 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(global_subsumption,[],[f30,f36])).

fof(f36,plain,(
    ~ m1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f35,f29])).

fof(f29,plain,(
    ~ v1_subset_1(k6_domain_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0)) ),
    inference(superposition,[],[f23,f28])).

fof(f28,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f24,f21])).

fof(f21,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_struct_0(sK0)
    & ~ v7_struct_0(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f17,f16])).

fof(f16,plain,
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

fof(f17,plain,
    ( ? [X1] :
        ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_struct_0(X0)
      & ~ v7_struct_0(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_struct_0(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).

fof(f24,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f23,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f35,plain,(
    ! [X0] :
      ( v1_subset_1(k6_domain_1(k2_struct_0(sK0),X0),k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k2_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f21,f19,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k2_struct_0(sK0))
      | v1_subset_1(k6_domain_1(k2_struct_0(sK0),X0),k2_struct_0(sK0))
      | ~ l1_struct_0(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f33,f32])).

fof(f32,plain,(
    ~ v1_zfmisc_1(k2_struct_0(sK0)) ),
    inference(global_subsumption,[],[f21,f20,f31])).

fof(f31,plain,
    ( ~ v1_zfmisc_1(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v7_struct_0(sK0) ),
    inference(superposition,[],[f27,f28])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f20,plain,(
    ~ v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_zfmisc_1(k2_struct_0(X1))
      | ~ m1_subset_1(X0,k2_struct_0(X1))
      | v1_subset_1(k6_domain_1(k2_struct_0(X1),X0),k2_struct_0(X1))
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f25,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f25,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_zfmisc_1(X0)
      | v1_subset_1(k6_domain_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_subset_1(k6_domain_1(X0,X1),X0)
          | ~ m1_subset_1(X1,X0) )
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( ~ v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,X0)
         => v1_subset_1(k6_domain_1(X0,X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f30,plain,(
    m1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(superposition,[],[f22,f28])).

fof(f22,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:09:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.39  % (9573)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.12/0.39  % (9573)Refutation found. Thanks to Tanya!
% 0.12/0.39  % SZS status Theorem for theBenchmark
% 0.12/0.39  % SZS output start Proof for theBenchmark
% 0.12/0.39  fof(f37,plain,(
% 0.12/0.39    $false),
% 0.12/0.39    inference(global_subsumption,[],[f30,f36])).
% 0.12/0.39  fof(f36,plain,(
% 0.12/0.39    ~m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.12/0.39    inference(resolution,[],[f35,f29])).
% 0.12/0.39  fof(f29,plain,(
% 0.12/0.39    ~v1_subset_1(k6_domain_1(k2_struct_0(sK0),sK1),k2_struct_0(sK0))),
% 0.12/0.39    inference(superposition,[],[f23,f28])).
% 0.12/0.39  fof(f28,plain,(
% 0.12/0.39    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.12/0.39    inference(resolution,[],[f24,f21])).
% 0.12/0.39  fof(f21,plain,(
% 0.12/0.39    l1_struct_0(sK0)),
% 0.12/0.39    inference(cnf_transformation,[],[f18])).
% 0.12/0.39  fof(f18,plain,(
% 0.12/0.39    (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v7_struct_0(sK0) & ~v2_struct_0(sK0)),
% 0.12/0.39    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f17,f16])).
% 0.12/0.39  fof(f16,plain,(
% 0.12/0.39    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_struct_0(sK0) & ~v7_struct_0(sK0) & ~v2_struct_0(sK0))),
% 0.12/0.39    introduced(choice_axiom,[])).
% 0.12/0.39  fof(f17,plain,(
% 0.12/0.39    ? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),X1),u1_struct_0(sK0)) & m1_subset_1(X1,u1_struct_0(sK0))) => (~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.12/0.39    introduced(choice_axiom,[])).
% 0.12/0.39  fof(f8,plain,(
% 0.12/0.39    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0))),
% 0.12/0.39    inference(flattening,[],[f7])).
% 0.12/0.39  fof(f7,plain,(
% 0.12/0.39    ? [X0] : (? [X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)))),
% 0.12/0.39    inference(ennf_transformation,[],[f6])).
% 0.12/0.39  fof(f6,negated_conjecture,(
% 0.12/0.39    ~! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 0.12/0.39    inference(negated_conjecture,[],[f5])).
% 0.12/0.39  fof(f5,conjecture,(
% 0.12/0.39    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_tex_2)).
% 0.12/0.39  fof(f24,plain,(
% 0.12/0.39    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.12/0.39    inference(cnf_transformation,[],[f9])).
% 0.12/0.39  fof(f9,plain,(
% 0.12/0.39    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.12/0.39    inference(ennf_transformation,[],[f1])).
% 0.12/0.39  fof(f1,axiom,(
% 0.12/0.39    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.12/0.39  fof(f23,plain,(
% 0.12/0.39    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 0.12/0.39    inference(cnf_transformation,[],[f18])).
% 0.12/0.39  fof(f35,plain,(
% 0.12/0.39    ( ! [X0] : (v1_subset_1(k6_domain_1(k2_struct_0(sK0),X0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k2_struct_0(sK0))) )),
% 0.12/0.39    inference(global_subsumption,[],[f21,f19,f34])).
% 0.12/0.39  fof(f34,plain,(
% 0.12/0.39    ( ! [X0] : (~m1_subset_1(X0,k2_struct_0(sK0)) | v1_subset_1(k6_domain_1(k2_struct_0(sK0),X0),k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)) )),
% 0.12/0.39    inference(resolution,[],[f33,f32])).
% 0.12/0.39  fof(f32,plain,(
% 0.12/0.39    ~v1_zfmisc_1(k2_struct_0(sK0))),
% 0.12/0.39    inference(global_subsumption,[],[f21,f20,f31])).
% 0.12/0.39  fof(f31,plain,(
% 0.12/0.39    ~v1_zfmisc_1(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v7_struct_0(sK0)),
% 0.12/0.39    inference(superposition,[],[f27,f28])).
% 0.12/0.39  fof(f27,plain,(
% 0.12/0.39    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.12/0.39    inference(cnf_transformation,[],[f15])).
% 0.12/0.39  fof(f15,plain,(
% 0.12/0.39    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.12/0.39    inference(flattening,[],[f14])).
% 0.12/0.39  fof(f14,plain,(
% 0.12/0.39    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.12/0.39    inference(ennf_transformation,[],[f3])).
% 0.12/0.39  fof(f3,axiom,(
% 0.12/0.39    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.12/0.39  fof(f20,plain,(
% 0.12/0.39    ~v7_struct_0(sK0)),
% 0.12/0.39    inference(cnf_transformation,[],[f18])).
% 0.12/0.39  fof(f33,plain,(
% 0.12/0.39    ( ! [X0,X1] : (v1_zfmisc_1(k2_struct_0(X1)) | ~m1_subset_1(X0,k2_struct_0(X1)) | v1_subset_1(k6_domain_1(k2_struct_0(X1),X0),k2_struct_0(X1)) | ~l1_struct_0(X1) | v2_struct_0(X1)) )),
% 0.12/0.39    inference(resolution,[],[f25,f26])).
% 0.12/0.39  fof(f26,plain,(
% 0.12/0.39    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.12/0.39    inference(cnf_transformation,[],[f13])).
% 0.12/0.39  fof(f13,plain,(
% 0.12/0.39    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.12/0.39    inference(flattening,[],[f12])).
% 0.12/0.39  fof(f12,plain,(
% 0.12/0.39    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.12/0.39    inference(ennf_transformation,[],[f2])).
% 0.12/0.39  fof(f2,axiom,(
% 0.12/0.39    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.12/0.39  fof(f25,plain,(
% 0.12/0.39    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | v1_zfmisc_1(X0) | v1_subset_1(k6_domain_1(X0,X1),X0)) )),
% 0.12/0.39    inference(cnf_transformation,[],[f11])).
% 0.12/0.39  fof(f11,plain,(
% 0.12/0.39    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.12/0.39    inference(flattening,[],[f10])).
% 0.12/0.39  fof(f10,plain,(
% 0.12/0.39    ! [X0] : (! [X1] : (v1_subset_1(k6_domain_1(X0,X1),X0) | ~m1_subset_1(X1,X0)) | (v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.12/0.39    inference(ennf_transformation,[],[f4])).
% 0.12/0.39  fof(f4,axiom,(
% 0.12/0.39    ! [X0] : ((~v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,X0) => v1_subset_1(k6_domain_1(X0,X1),X0)))),
% 0.12/0.39    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tex_2)).
% 0.12/0.39  fof(f19,plain,(
% 0.12/0.39    ~v2_struct_0(sK0)),
% 0.12/0.39    inference(cnf_transformation,[],[f18])).
% 0.12/0.39  fof(f30,plain,(
% 0.12/0.39    m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.12/0.39    inference(superposition,[],[f22,f28])).
% 0.12/0.39  fof(f22,plain,(
% 0.12/0.39    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.12/0.39    inference(cnf_transformation,[],[f18])).
% 0.12/0.39  % SZS output end Proof for theBenchmark
% 0.12/0.39  % (9573)------------------------------
% 0.12/0.39  % (9573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.12/0.39  % (9573)Termination reason: Refutation
% 0.12/0.39  
% 0.12/0.39  % (9573)Memory used [KB]: 6012
% 0.12/0.39  % (9573)Time elapsed: 0.002 s
% 0.12/0.39  % (9573)------------------------------
% 0.12/0.39  % (9573)------------------------------
% 0.12/0.39  % (9568)Success in time 0.047 s
%------------------------------------------------------------------------------
