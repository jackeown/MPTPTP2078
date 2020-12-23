%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:49 EST 2020

% Result     : Theorem 1.07s
% Output     : Refutation 1.07s
% Verified   : 
% Statistics : Number of formulae       :   28 (  80 expanded)
%              Number of leaves         :    6 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :  103 ( 393 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f27])).

fof(f27,plain,(
    ~ v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f17,f26,f21,f19,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ v7_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v7_struct_0(X0)
          | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).

fof(f19,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( v7_struct_0(sK0)
    & v1_tex_2(k1_tex_2(sK0,sK1),sK0)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( v7_struct_0(X0)
            & v1_tex_2(k1_tex_2(X0,X1),X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( v7_struct_0(sK0)
          & v1_tex_2(k1_tex_2(sK0,X1),sK0)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,
    ( ? [X1] :
        ( v7_struct_0(sK0)
        & v1_tex_2(k1_tex_2(sK0,X1),sK0)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( v7_struct_0(sK0)
      & v1_tex_2(k1_tex_2(sK0,sK1),sK0)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v7_struct_0(X0)
          & v1_tex_2(k1_tex_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v7_struct_0(X0)
          & v1_tex_2(k1_tex_2(X0,X1),X0)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ ( v7_struct_0(X0)
                & v1_tex_2(k1_tex_2(X0,X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ ( v7_struct_0(X0)
              & v1_tex_2(k1_tex_2(X0,X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tex_2)).

fof(f21,plain,(
    v7_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f26,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f18,f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f28,plain,(
    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f17,f18,f19,f20,f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
      | ~ v1_tex_2(k1_tex_2(X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
              | ~ v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
            & ( v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))
              | ~ v1_tex_2(k1_tex_2(X0,X1),X0) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v1_tex_2(k1_tex_2(X0,X1),X0)
          <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).

% (13406)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
fof(f20,plain,(
    v1_tex_2(k1_tex_2(sK0,sK1),sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:54:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (798752768)
% 0.14/0.38  ipcrm: permission denied for id (798851082)
% 0.14/0.38  ipcrm: permission denied for id (798916621)
% 0.14/0.39  ipcrm: permission denied for id (799014932)
% 0.14/0.39  ipcrm: permission denied for id (799047701)
% 0.14/0.40  ipcrm: permission denied for id (799113243)
% 0.14/0.40  ipcrm: permission denied for id (799146012)
% 0.21/0.41  ipcrm: permission denied for id (799277095)
% 0.21/0.42  ipcrm: permission denied for id (799375402)
% 0.21/0.42  ipcrm: permission denied for id (799440940)
% 0.21/0.42  ipcrm: permission denied for id (799473710)
% 0.21/0.43  ipcrm: permission denied for id (799539249)
% 0.21/0.43  ipcrm: permission denied for id (799572018)
% 0.21/0.44  ipcrm: permission denied for id (799637562)
% 0.21/0.44  ipcrm: permission denied for id (799670333)
% 0.21/0.44  ipcrm: permission denied for id (799703102)
% 0.21/0.45  ipcrm: permission denied for id (799735872)
% 0.21/0.47  ipcrm: permission denied for id (799866962)
% 0.21/0.48  ipcrm: permission denied for id (799965275)
% 0.21/0.48  ipcrm: permission denied for id (800030815)
% 0.21/0.49  ipcrm: permission denied for id (800096354)
% 0.21/0.50  ipcrm: permission denied for id (800227435)
% 0.21/0.52  ipcrm: permission denied for id (800391294)
% 0.82/0.62  % (13404)lrs-11_4:1_afp=4000:afq=2.0:anc=none:br=off:gs=on:lwlo=on:nm=64:nwc=3:stl=30:urr=on_3 on theBenchmark
% 0.82/0.63  % (13413)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
% 1.07/0.63  % (13404)Refutation found. Thanks to Tanya!
% 1.07/0.63  % SZS status Theorem for theBenchmark
% 1.07/0.63  % SZS output start Proof for theBenchmark
% 1.07/0.63  fof(f29,plain,(
% 1.07/0.63    $false),
% 1.07/0.63    inference(subsumption_resolution,[],[f28,f27])).
% 1.07/0.63  fof(f27,plain,(
% 1.07/0.63    ~v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.07/0.63    inference(unit_resulting_resolution,[],[f17,f26,f21,f19,f23])).
% 1.07/0.63  fof(f23,plain,(
% 1.07/0.63    ( ! [X0,X1] : (~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v7_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.07/0.63    inference(cnf_transformation,[],[f10])).
% 1.07/0.63  fof(f10,plain,(
% 1.07/0.63    ! [X0] : (! [X1] : (~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.07/0.63    inference(flattening,[],[f9])).
% 1.07/0.63  fof(f9,plain,(
% 1.07/0.63    ! [X0] : (! [X1] : ((~v7_struct_0(X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.07/0.63    inference(ennf_transformation,[],[f3])).
% 1.07/0.63  fof(f3,axiom,(
% 1.07/0.63    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_tex_2)).
% 1.07/0.63  fof(f19,plain,(
% 1.07/0.63    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.07/0.63    inference(cnf_transformation,[],[f15])).
% 1.07/0.63  fof(f15,plain,(
% 1.07/0.63    (v7_struct_0(sK0) & v1_tex_2(k1_tex_2(sK0,sK1),sK0) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.07/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f14,f13])).
% 1.07/0.63  fof(f13,plain,(
% 1.07/0.63    ? [X0] : (? [X1] : (v7_struct_0(X0) & v1_tex_2(k1_tex_2(X0,X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (v7_struct_0(sK0) & v1_tex_2(k1_tex_2(sK0,X1),sK0) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.07/0.63    introduced(choice_axiom,[])).
% 1.07/0.63  fof(f14,plain,(
% 1.07/0.63    ? [X1] : (v7_struct_0(sK0) & v1_tex_2(k1_tex_2(sK0,X1),sK0) & m1_subset_1(X1,u1_struct_0(sK0))) => (v7_struct_0(sK0) & v1_tex_2(k1_tex_2(sK0,sK1),sK0) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.07/0.63    introduced(choice_axiom,[])).
% 1.07/0.63  fof(f7,plain,(
% 1.07/0.63    ? [X0] : (? [X1] : (v7_struct_0(X0) & v1_tex_2(k1_tex_2(X0,X1),X0) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.07/0.63    inference(flattening,[],[f6])).
% 1.07/0.63  fof(f6,plain,(
% 1.07/0.63    ? [X0] : (? [X1] : ((v7_struct_0(X0) & v1_tex_2(k1_tex_2(X0,X1),X0)) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.07/0.63    inference(ennf_transformation,[],[f5])).
% 1.07/0.63  fof(f5,negated_conjecture,(
% 1.07/0.63    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_tex_2(k1_tex_2(X0,X1),X0))))),
% 1.07/0.63    inference(negated_conjecture,[],[f4])).
% 1.07/0.63  fof(f4,conjecture,(
% 1.07/0.63    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~(v7_struct_0(X0) & v1_tex_2(k1_tex_2(X0,X1),X0))))),
% 1.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_tex_2)).
% 1.07/0.63  fof(f21,plain,(
% 1.07/0.63    v7_struct_0(sK0)),
% 1.07/0.63    inference(cnf_transformation,[],[f15])).
% 1.07/0.63  fof(f26,plain,(
% 1.07/0.63    l1_struct_0(sK0)),
% 1.07/0.63    inference(unit_resulting_resolution,[],[f18,f22])).
% 1.07/0.63  fof(f22,plain,(
% 1.07/0.63    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.07/0.63    inference(cnf_transformation,[],[f8])).
% 1.07/0.63  fof(f8,plain,(
% 1.07/0.63    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.07/0.63    inference(ennf_transformation,[],[f1])).
% 1.07/0.63  fof(f1,axiom,(
% 1.07/0.63    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.07/0.63  fof(f18,plain,(
% 1.07/0.63    l1_pre_topc(sK0)),
% 1.07/0.63    inference(cnf_transformation,[],[f15])).
% 1.07/0.63  fof(f17,plain,(
% 1.07/0.63    ~v2_struct_0(sK0)),
% 1.07/0.63    inference(cnf_transformation,[],[f15])).
% 1.07/0.63  fof(f28,plain,(
% 1.07/0.63    v1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),u1_struct_0(sK0))),
% 1.07/0.63    inference(unit_resulting_resolution,[],[f17,f18,f19,f20,f24])).
% 1.07/0.63  fof(f24,plain,(
% 1.07/0.63    ( ! [X0,X1] : (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.07/0.63    inference(cnf_transformation,[],[f16])).
% 1.07/0.63  fof(f16,plain,(
% 1.07/0.63    ! [X0] : (! [X1] : (((v1_tex_2(k1_tex_2(X0,X1),X0) | ~v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) & (v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)) | ~v1_tex_2(k1_tex_2(X0,X1),X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.07/0.63    inference(nnf_transformation,[],[f12])).
% 1.07/0.63  fof(f12,plain,(
% 1.07/0.63    ! [X0] : (! [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.07/0.63    inference(flattening,[],[f11])).
% 1.07/0.63  fof(f11,plain,(
% 1.07/0.63    ! [X0] : (! [X1] : ((v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.07/0.63    inference(ennf_transformation,[],[f2])).
% 1.07/0.63  fof(f2,axiom,(
% 1.07/0.63    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v1_tex_2(k1_tex_2(X0,X1),X0) <=> v1_subset_1(k6_domain_1(u1_struct_0(X0),X1),u1_struct_0(X0)))))),
% 1.07/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_tex_2)).
% 1.07/0.63  % (13406)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 1.07/0.63  fof(f20,plain,(
% 1.07/0.63    v1_tex_2(k1_tex_2(sK0,sK1),sK0)),
% 1.07/0.63    inference(cnf_transformation,[],[f15])).
% 1.07/0.63  % SZS output end Proof for theBenchmark
% 1.07/0.63  % (13404)------------------------------
% 1.07/0.63  % (13404)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.07/0.63  % (13404)Termination reason: Refutation
% 1.07/0.63  
% 1.07/0.63  % (13404)Memory used [KB]: 9850
% 1.07/0.63  % (13404)Time elapsed: 0.067 s
% 1.07/0.63  % (13404)------------------------------
% 1.07/0.63  % (13404)------------------------------
% 1.07/0.63  % (13245)Success in time 0.272 s
%------------------------------------------------------------------------------
