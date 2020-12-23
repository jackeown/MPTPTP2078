%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:23 EST 2020

% Result     : Theorem 0.16s
% Output     : Refutation 0.16s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 115 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :   13
%              Number of atoms          :  176 ( 464 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(subsumption_resolution,[],[f60,f53])).

fof(f53,plain,(
    v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f52,f23])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

fof(f52,plain,
    ( v2_struct_0(sK0)
    | v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f51,f26])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f50,f24])).

fof(f24,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(resolution,[],[f49,f25])).

fof(f25,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_tex_2(sK1(X0,k1_xboole_0),X0) ) ),
    inference(subsumption_resolution,[],[f48,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f42,f41])).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f39,f38])).

fof(f38,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f35,f28])).

fof(f28,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f39,plain,(
    ! [X0] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ r1_xboole_0(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f34,f27])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f42,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(k1_xboole_0)
      | v2_struct_0(X0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f33,f29])).

fof(f29,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f48,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(k1_xboole_0,X0)
      | v3_tex_2(sK1(X0,k1_xboole_0),X0) ) ),
    inference(resolution,[],[f32,f29])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( v3_tex_2(X2,X0)
              & r1_tarski(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ~ ( v3_tex_2(X2,X0)
                      & r1_tarski(X1,X2) ) )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).

fof(f60,plain,(
    ~ v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(resolution,[],[f59,f22])).

fof(f22,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(X1,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f59,plain,(
    m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f58,f23])).

fof(f58,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f57,f26])).

fof(f57,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f56,f24])).

fof(f56,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f55,f25])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(sK1(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f54,f43])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(k1_xboole_0,X0)
      | m1_subset_1(sK1(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f30,f29])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : run_vampire %s %d
% 0.10/0.30  % Computer   : n004.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 18:03:08 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.16/0.41  % (2020)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.16/0.42  % (2028)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.16/0.42  % (2018)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.16/0.42  % (2020)Refutation found. Thanks to Tanya!
% 0.16/0.42  % SZS status Theorem for theBenchmark
% 0.16/0.42  % SZS output start Proof for theBenchmark
% 0.16/0.42  fof(f65,plain,(
% 0.16/0.42    $false),
% 0.16/0.42    inference(subsumption_resolution,[],[f60,f53])).
% 0.16/0.42  fof(f53,plain,(
% 0.16/0.42    v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.16/0.42    inference(subsumption_resolution,[],[f52,f23])).
% 0.16/0.42  fof(f23,plain,(
% 0.16/0.42    ~v2_struct_0(sK0)),
% 0.16/0.42    inference(cnf_transformation,[],[f12])).
% 0.16/0.42  fof(f12,plain,(
% 0.16/0.42    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.16/0.42    inference(flattening,[],[f11])).
% 0.16/0.42  fof(f11,plain,(
% 0.16/0.42    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.16/0.42    inference(ennf_transformation,[],[f10])).
% 0.16/0.42  fof(f10,negated_conjecture,(
% 0.16/0.42    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.16/0.42    inference(negated_conjecture,[],[f9])).
% 0.16/0.42  fof(f9,conjecture,(
% 0.16/0.42    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.16/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).
% 0.16/0.42  fof(f52,plain,(
% 0.16/0.42    v2_struct_0(sK0) | v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.16/0.42    inference(subsumption_resolution,[],[f51,f26])).
% 0.16/0.42  fof(f26,plain,(
% 0.16/0.42    l1_pre_topc(sK0)),
% 0.16/0.42    inference(cnf_transformation,[],[f12])).
% 0.16/0.42  fof(f51,plain,(
% 0.16/0.42    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.16/0.42    inference(subsumption_resolution,[],[f50,f24])).
% 0.16/0.42  fof(f24,plain,(
% 0.16/0.42    v2_pre_topc(sK0)),
% 0.16/0.42    inference(cnf_transformation,[],[f12])).
% 0.16/0.42  fof(f50,plain,(
% 0.16/0.42    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.16/0.42    inference(resolution,[],[f49,f25])).
% 0.16/0.42  fof(f25,plain,(
% 0.16/0.42    v3_tdlat_3(sK0)),
% 0.16/0.42    inference(cnf_transformation,[],[f12])).
% 0.16/0.42  fof(f49,plain,(
% 0.16/0.42    ( ! [X0] : (~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v3_tex_2(sK1(X0,k1_xboole_0),X0)) )),
% 0.16/0.42    inference(subsumption_resolution,[],[f48,f43])).
% 0.16/0.42  fof(f43,plain,(
% 0.16/0.42    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.16/0.42    inference(subsumption_resolution,[],[f42,f41])).
% 0.16/0.42  fof(f41,plain,(
% 0.16/0.42    v1_xboole_0(k1_xboole_0)),
% 0.16/0.42    inference(subsumption_resolution,[],[f39,f38])).
% 0.16/0.42  fof(f38,plain,(
% 0.16/0.42    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 0.16/0.42    inference(resolution,[],[f35,f28])).
% 0.16/0.42  fof(f28,plain,(
% 0.16/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.16/0.42    inference(cnf_transformation,[],[f3])).
% 0.16/0.42  fof(f3,axiom,(
% 0.16/0.42    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.16/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.16/0.42  fof(f35,plain,(
% 0.16/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 0.16/0.42    inference(cnf_transformation,[],[f19])).
% 0.16/0.42  fof(f19,plain,(
% 0.16/0.42    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.16/0.42    inference(ennf_transformation,[],[f1])).
% 0.16/0.42  fof(f1,axiom,(
% 0.16/0.42    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.16/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.16/0.42  fof(f39,plain,(
% 0.16/0.42    ( ! [X0] : (v1_xboole_0(k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,X0)) )),
% 0.16/0.42    inference(resolution,[],[f34,f27])).
% 0.16/0.42  fof(f27,plain,(
% 0.16/0.42    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.16/0.42    inference(cnf_transformation,[],[f2])).
% 0.16/0.42  fof(f2,axiom,(
% 0.16/0.42    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.16/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.16/0.42  fof(f34,plain,(
% 0.16/0.42    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_xboole_0(X1) | ~r1_xboole_0(X1,X0)) )),
% 0.16/0.42    inference(cnf_transformation,[],[f18])).
% 0.16/0.42  fof(f18,plain,(
% 0.16/0.42    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.16/0.42    inference(flattening,[],[f17])).
% 0.16/0.42  fof(f17,plain,(
% 0.16/0.42    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.16/0.42    inference(ennf_transformation,[],[f4])).
% 0.16/0.42  fof(f4,axiom,(
% 0.16/0.42    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.16/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.16/0.42  fof(f42,plain,(
% 0.16/0.42    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(k1_xboole_0) | v2_struct_0(X0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.16/0.42    inference(resolution,[],[f33,f29])).
% 0.16/0.42  fof(f29,plain,(
% 0.16/0.42    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.16/0.42    inference(cnf_transformation,[],[f5])).
% 0.16/0.42  fof(f5,axiom,(
% 0.16/0.42    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.16/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.16/0.42  fof(f33,plain,(
% 0.16/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | v2_struct_0(X0) | v2_tex_2(X1,X0)) )),
% 0.16/0.42    inference(cnf_transformation,[],[f16])).
% 0.16/0.42  fof(f16,plain,(
% 0.16/0.42    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.16/0.42    inference(flattening,[],[f15])).
% 0.16/0.42  fof(f15,plain,(
% 0.16/0.42    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.16/0.42    inference(ennf_transformation,[],[f7])).
% 0.16/0.42  fof(f7,axiom,(
% 0.16/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.16/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.16/0.42  fof(f48,plain,(
% 0.16/0.42    ( ! [X0] : (~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(k1_xboole_0,X0) | v3_tex_2(sK1(X0,k1_xboole_0),X0)) )),
% 0.16/0.42    inference(resolution,[],[f32,f29])).
% 0.16/0.42  fof(f32,plain,(
% 0.16/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | v3_tex_2(sK1(X0,X1),X0)) )),
% 0.16/0.42    inference(cnf_transformation,[],[f14])).
% 0.16/0.42  fof(f14,plain,(
% 0.16/0.42    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.16/0.42    inference(flattening,[],[f13])).
% 0.16/0.42  fof(f13,plain,(
% 0.16/0.42    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.16/0.42    inference(ennf_transformation,[],[f8])).
% 0.16/0.42  fof(f8,axiom,(
% 0.16/0.42    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.16/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).
% 0.16/0.42  fof(f60,plain,(
% 0.16/0.42    ~v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.16/0.42    inference(resolution,[],[f59,f22])).
% 0.16/0.42  fof(f22,plain,(
% 0.16/0.42    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X1,sK0)) )),
% 0.16/0.42    inference(cnf_transformation,[],[f12])).
% 0.16/0.42  fof(f59,plain,(
% 0.16/0.42    m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.16/0.42    inference(subsumption_resolution,[],[f58,f23])).
% 0.16/0.42  fof(f58,plain,(
% 0.16/0.42    v2_struct_0(sK0) | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.16/0.42    inference(subsumption_resolution,[],[f57,f26])).
% 0.16/0.42  fof(f57,plain,(
% 0.16/0.42    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.16/0.42    inference(subsumption_resolution,[],[f56,f24])).
% 0.16/0.42  fof(f56,plain,(
% 0.16/0.42    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.16/0.42    inference(resolution,[],[f55,f25])).
% 0.16/0.42  fof(f55,plain,(
% 0.16/0.42    ( ! [X0] : (~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(sK1(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.16/0.42    inference(subsumption_resolution,[],[f54,f43])).
% 0.16/0.42  fof(f54,plain,(
% 0.16/0.42    ( ! [X0] : (~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(k1_xboole_0,X0) | m1_subset_1(sK1(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.16/0.42    inference(resolution,[],[f30,f29])).
% 0.16/0.42  fof(f30,plain,(
% 0.16/0.42    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.16/0.42    inference(cnf_transformation,[],[f14])).
% 0.16/0.42  % SZS output end Proof for theBenchmark
% 0.16/0.42  % (2020)------------------------------
% 0.16/0.42  % (2020)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.16/0.42  % (2020)Termination reason: Refutation
% 0.16/0.42  
% 0.16/0.42  % (2020)Memory used [KB]: 5373
% 0.16/0.42  % (2020)Time elapsed: 0.053 s
% 0.16/0.42  % (2020)------------------------------
% 0.16/0.42  % (2020)------------------------------
% 0.16/0.43  % (2013)Success in time 0.114 s
%------------------------------------------------------------------------------
