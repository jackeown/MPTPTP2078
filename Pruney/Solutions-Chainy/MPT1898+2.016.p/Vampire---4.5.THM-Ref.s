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
% DateTime   : Thu Dec  3 13:22:20 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   45 ( 105 expanded)
%              Number of leaves         :    7 (  23 expanded)
%              Depth                    :   12
%              Number of atoms          :  164 ( 440 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,plain,(
    $false ),
    inference(subsumption_resolution,[],[f58,f51])).

fof(f51,plain,(
    v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f50,f20])).

fof(f20,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ? [X1] :
            ( v3_tex_2(X1,X0)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v3_tex_2(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).

fof(f50,plain,
    ( v2_struct_0(sK0)
    | v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f49,f23])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f49,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f48,f21])).

fof(f21,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f48,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(resolution,[],[f47,f22])).

fof(f22,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v3_tex_2(sK1(X0,k1_xboole_0),X0) ) ),
    inference(subsumption_resolution,[],[f46,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f40,f37])).

fof(f37,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f36,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f36,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[],[f32,f24])).

fof(f24,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(k1_xboole_0)
      | v2_struct_0(X0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f29,f25])).

fof(f25,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(k1_xboole_0,X0)
      | v3_tex_2(sK1(X0,k1_xboole_0),X0) ) ),
    inference(resolution,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f58,plain,(
    ~ v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(resolution,[],[f57,f19])).

fof(f19,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(X1,sK0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f57,plain,(
    m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f56,f20])).

fof(f56,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f55,f23])).

fof(f55,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f54,f21])).

fof(f54,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f53,f22])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(sK1(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f52,f41])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(k1_xboole_0,X0)
      | m1_subset_1(sK1(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f26,f25])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:35:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (1209)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.48  % (1204)dis+1002_8:1_awrs=converge:awrsf=256:anc=all_dependent:br=off:fsr=off:fde=none:gs=on:gsaa=from_current:gsem=on:irw=on:nm=64:nwc=1:sas=z3:s2a=on:sp=frequency:thf=on:uwa=interpreted_only:urr=on_7 on theBenchmark
% 0.21/0.48  % (1209)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f58,f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f50,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tex_2)).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    v2_struct_0(sK0) | v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f49,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f48,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.21/0.48    inference(resolution,[],[f47,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    v3_tdlat_3(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0] : (~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v3_tex_2(sK1(X0,k1_xboole_0),X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f46,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f40,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(resolution,[],[f36,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(resolution,[],[f32,f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(k1_xboole_0) | v2_struct_0(X0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.21/0.48    inference(resolution,[],[f29,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | v2_struct_0(X0) | v2_tex_2(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(k1_xboole_0,X0) | v3_tex_2(sK1(X0,k1_xboole_0),X0)) )),
% 0.21/0.48    inference(resolution,[],[f28,f25])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | v3_tex_2(sK1(X0,X1),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tex_2)).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ~v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.21/0.49    inference(resolution,[],[f57,f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X1,sK0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f56,f20])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    v2_struct_0(sK0) | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f55,f23])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f54,f21])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(resolution,[],[f53,f22])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0] : (~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(sK1(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f52,f41])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X0] : (~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(k1_xboole_0,X0) | m1_subset_1(sK1(X0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(resolution,[],[f26,f25])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (1209)------------------------------
% 0.21/0.49  % (1209)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1209)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (1209)Memory used [KB]: 5373
% 0.21/0.49  % (1209)Time elapsed: 0.061 s
% 0.21/0.49  % (1209)------------------------------
% 0.21/0.49  % (1209)------------------------------
% 0.21/0.49  % (1212)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.21/0.49  % (1202)Success in time 0.125 s
%------------------------------------------------------------------------------
