%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   40 ( 234 expanded)
%              Number of leaves         :    8 (  79 expanded)
%              Depth                    :   10
%              Number of atoms          :  173 (1388 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f48,plain,(
    $false ),
    inference(subsumption_resolution,[],[f45,f47])).

fof(f47,plain,(
    ~ v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f26,f46])).

fof(f46,plain,(
    v2_tdlat_3(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f40,f25,f44,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( ~ v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_tex_1)).

fof(f44,plain,(
    l1_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f23,f43,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f43,plain,(
    m1_pre_topc(k1_tex_2(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f22,f23,f24,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_pre_topc(k1_tex_2(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
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
     => ( m1_pre_topc(k1_tex_2(X0,X1),X0)
        & v1_pre_topc(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).

fof(f24,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( ~ v2_tdlat_3(k1_tex_2(sK0,sK1))
      | ~ v1_tdlat_3(k1_tex_2(sK0,sK1)) )
    & v2_pre_topc(k1_tex_2(sK0,sK1))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f20,f19])).

fof(f19,plain,
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

fof(f20,plain,
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

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_tdlat_3(k1_tex_2(X0,X1))
            | ~ v1_tdlat_3(k1_tex_2(X0,X1)) )
          & v2_pre_topc(k1_tex_2(X0,X1))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v2_tdlat_3(k1_tex_2(X0,X1))
            | ~ v1_tdlat_3(k1_tex_2(X0,X1)) )
          & v2_pre_topc(k1_tex_2(X0,X1))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( v2_pre_topc(k1_tex_2(X0,X1))
             => ( v2_tdlat_3(k1_tex_2(X0,X1))
                & v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( v2_pre_topc(k1_tex_2(X0,X1))
           => ( v2_tdlat_3(k1_tex_2(X0,X1))
              & v1_tdlat_3(k1_tex_2(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tex_2)).

fof(f22,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f25,plain,(
    v2_pre_topc(k1_tex_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f40,plain,(
    ~ v2_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f23,f24,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_pre_topc(k1_tex_2(X0,X1))
        & v7_struct_0(k1_tex_2(X0,X1))
        & ~ v2_struct_0(k1_tex_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).

fof(f41,plain,(
    v7_struct_0(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f22,f23,f24,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | v7_struct_0(k1_tex_2(X0,X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f26,plain,
    ( ~ v2_tdlat_3(k1_tex_2(sK0,sK1))
    | ~ v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f45,plain,(
    v1_tdlat_3(k1_tex_2(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f41,f40,f25,f44,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

% (29540)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
fof(f10,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & ~ v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( ~ v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & ~ v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tex_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:29:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.45  % (29552)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (29547)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.47  % (29548)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.47  % (29548)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f45,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ~v1_tdlat_3(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f26,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v2_tdlat_3(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f41,f40,f25,f44,f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0] : (~v7_struct_0(X0) | v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : ((v2_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) | v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (((v2_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) | (v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ((~v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_tex_1)).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    l1_pre_topc(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f23,f43,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    m1_pre_topc(k1_tex_2(sK0,sK1),sK0)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f22,f23,f24,f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_pre_topc(k1_tex_2(X0,X1),X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0,X1] : ((m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tex_2(X0,X1),X0) & v1_pre_topc(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tex_2)).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ((~v2_tdlat_3(k1_tex_2(sK0,sK1)) | ~v1_tdlat_3(k1_tex_2(sK0,sK1))) & v2_pre_topc(k1_tex_2(sK0,sK1)) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f20,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((~v2_tdlat_3(k1_tex_2(X0,X1)) | ~v1_tdlat_3(k1_tex_2(X0,X1))) & v2_pre_topc(k1_tex_2(X0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v2_tdlat_3(k1_tex_2(sK0,X1)) | ~v1_tdlat_3(k1_tex_2(sK0,X1))) & v2_pre_topc(k1_tex_2(sK0,X1)) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ? [X1] : ((~v2_tdlat_3(k1_tex_2(sK0,X1)) | ~v1_tdlat_3(k1_tex_2(sK0,X1))) & v2_pre_topc(k1_tex_2(sK0,X1)) & m1_subset_1(X1,u1_struct_0(sK0))) => ((~v2_tdlat_3(k1_tex_2(sK0,sK1)) | ~v1_tdlat_3(k1_tex_2(sK0,sK1))) & v2_pre_topc(k1_tex_2(sK0,sK1)) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((~v2_tdlat_3(k1_tex_2(X0,X1)) | ~v1_tdlat_3(k1_tex_2(X0,X1))) & v2_pre_topc(k1_tex_2(X0,X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (((~v2_tdlat_3(k1_tex_2(X0,X1)) | ~v1_tdlat_3(k1_tex_2(X0,X1))) & v2_pre_topc(k1_tex_2(X0,X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v2_pre_topc(k1_tex_2(X0,X1)) => (v2_tdlat_3(k1_tex_2(X0,X1)) & v1_tdlat_3(k1_tex_2(X0,X1))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f6])).
% 0.21/0.47  fof(f6,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (v2_pre_topc(k1_tex_2(X0,X1)) => (v2_tdlat_3(k1_tex_2(X0,X1)) & v1_tdlat_3(k1_tex_2(X0,X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tex_2)).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    v2_pre_topc(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ~v2_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f22,f23,f24,f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (v1_pre_topc(k1_tex_2(X0,X1)) & v7_struct_0(k1_tex_2(X0,X1)) & ~v2_struct_0(k1_tex_2(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_tex_2)).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    v7_struct_0(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f22,f23,f24,f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | v7_struct_0(k1_tex_2(X0,X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ~v2_tdlat_3(k1_tex_2(sK0,sK1)) | ~v1_tdlat_3(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    v1_tdlat_3(k1_tex_2(sK0,sK1))),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f41,f40,f25,f44,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0] : (~v7_struct_0(X0) | v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : ((v2_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) | v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  % (29540)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (((v2_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0)) | (v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ((~v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & ~v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_tex_1)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (29548)------------------------------
% 0.21/0.47  % (29548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (29548)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (29548)Memory used [KB]: 5373
% 0.21/0.47  % (29548)Time elapsed: 0.005 s
% 0.21/0.47  % (29548)------------------------------
% 0.21/0.47  % (29548)------------------------------
% 0.21/0.48  % (29533)Success in time 0.121 s
%------------------------------------------------------------------------------
