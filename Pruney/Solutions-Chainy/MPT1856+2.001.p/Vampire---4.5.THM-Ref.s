%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   37 ( 234 expanded)
%              Number of leaves         :    7 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  155 (1394 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f43,plain,(
    $false ),
    inference(subsumption_resolution,[],[f40,f42])).

fof(f42,plain,(
    ~ v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f23,f41])).

fof(f41,plain,(
    v2_tdlat_3(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f35,f36,f39,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | v2_tdlat_3(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_pre_topc(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_1)).

fof(f39,plain,(
    l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f20,f38,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f38,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f19,f20,f21,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f21,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( ( ~ v2_tdlat_3(k1_tex_2(sK0,sK1))
      | ~ v1_tdlat_3(k1_tex_2(sK0,sK1)) )
    & v2_pre_topc(k1_tex_2(sK0,sK1))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f17,f16])).

fof(f16,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v2_tdlat_3(k1_tex_2(X0,X1))
              | ~ v1_tdlat_3(k1_tex_2(X0,X1)) )
            & v2_pre_topc(k1_tex_2(X0,X1))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v2_tdlat_3(k1_tex_2(sK0,X1))
            | ~ v1_tdlat_3(k1_tex_2(sK0,X1)) )
          & v2_pre_topc(k1_tex_2(sK0,X1))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,
    ( ? [X1] :
        ( ( ~ v2_tdlat_3(k1_tex_2(sK0,X1))
          | ~ v1_tdlat_3(k1_tex_2(sK0,X1)) )
        & v2_pre_topc(k1_tex_2(sK0,X1))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( ~ v2_tdlat_3(k1_tex_2(sK0,sK1))
        | ~ v1_tdlat_3(k1_tex_2(sK0,sK1)) )
      & v2_pre_topc(k1_tex_2(sK0,sK1))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_tdlat_3(k1_tex_2(X0,X1))
            | ~ v1_tdlat_3(k1_tex_2(X0,X1)) )
          & v2_pre_topc(k1_tex_2(X0,X1))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_tdlat_3(k1_tex_2(X0,X1))
            | ~ v1_tdlat_3(k1_tex_2(X0,X1)) )
          & v2_pre_topc(k1_tex_2(X0,X1))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v2_pre_topc(k1_tex_2(X0,X1))
             => ( v2_tdlat_3(k1_tex_2(X0,X1))
                & v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_pre_topc(k1_tex_2(X0,X1))
           => ( v2_tdlat_3(k1_tex_2(X0,X1))
              & v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tex_2)).

fof(f19,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f19,f20,f21,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v7_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f35,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f19,f20,f21,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f22,plain,(
    v2_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f23,plain,
    ( ~ v2_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f35,f36,f39,f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | v1_tdlat_3(X0)
      | ~ v7_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:31:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (2356)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (2362)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.48  % (2362)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f40,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ~v1_tdlat_3(k1_tex_2(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f23,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    v2_tdlat_3(k1_tex_2(sK0,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f22,f35,f36,f39,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(X0) | v2_tdlat_3(X0) | ~v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0] : ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) | ~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) | (~v2_pre_topc(X0) | ~v7_struct_0(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) => (v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tex_1)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f20,f38,f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f19,f20,f21,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ((~v2_tdlat_3(k1_tex_2(sK0,sK1)) | ~v1_tdlat_3(k1_tex_2(sK0,sK1))) & v2_pre_topc(k1_tex_2(sK0,sK1)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f8,f17,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v2_tdlat_3(k1_tex_2(X0,X1)) | ~v1_tdlat_3(k1_tex_2(X0,X1))) & v2_pre_topc(k1_tex_2(X0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v2_tdlat_3(k1_tex_2(sK0,X1)) | ~v1_tdlat_3(k1_tex_2(sK0,X1))) & v2_pre_topc(k1_tex_2(sK0,X1)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X1] : ((~v2_tdlat_3(k1_tex_2(sK0,X1)) | ~v1_tdlat_3(k1_tex_2(sK0,X1))) & v2_pre_topc(k1_tex_2(sK0,X1)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v2_tdlat_3(k1_tex_2(sK0,sK1)) | ~v1_tdlat_3(k1_tex_2(sK0,sK1))) & v2_pre_topc(k1_tex_2(sK0,sK1)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((~v2_tdlat_3(k1_tex_2(X0,X1)) | ~v1_tdlat_3(k1_tex_2(X0,X1))) & v2_pre_topc(k1_tex_2(X0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (((~v2_tdlat_3(k1_tex_2(X0,X1)) | ~v1_tdlat_3(k1_tex_2(X0,X1))) & v2_pre_topc(k1_tex_2(X0,X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v2_pre_topc(k1_tex_2(X0,X1)) => (v2_tdlat_3(k1_tex_2(X0,X1)) & v1_tdlat_3(k1_tex_2(X0,X1))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f5])).
% 0.21/0.48  fof(f5,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v2_pre_topc(k1_tex_2(X0,X1)) => (v2_tdlat_3(k1_tex_2(X0,X1)) & v1_tdlat_3(k1_tex_2(X0,X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tex_2)).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f19,f20,f21,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f19,f20,f21,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    v2_pre_topc(k1_tex_2(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ~v2_tdlat_3(k1_tex_2(sK0,sK1)) | ~v1_tdlat_3(k1_tex_2(sK0,sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v1_tdlat_3(k1_tex_2(sK0,sK1))),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f22,f35,f36,f39,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(X0) | v1_tdlat_3(X0) | ~v7_struct_0(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (2362)------------------------------
% 0.21/0.48  % (2362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (2362)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (2362)Memory used [KB]: 5373
% 0.21/0.48  % (2362)Time elapsed: 0.008 s
% 0.21/0.48  % (2362)------------------------------
% 0.21/0.48  % (2362)------------------------------
% 0.21/0.48  % (2354)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.48  % (2345)Success in time 0.116 s
%------------------------------------------------------------------------------
