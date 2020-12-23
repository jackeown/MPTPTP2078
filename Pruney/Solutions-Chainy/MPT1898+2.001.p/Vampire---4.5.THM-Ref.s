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
% DateTime   : Thu Dec  3 13:22:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 163 expanded)
%              Number of leaves         :    9 (  39 expanded)
%              Depth                    :   16
%              Number of atoms          :  188 ( 568 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109,plain,(
    $false ),
    inference(subsumption_resolution,[],[f102,f97])).

fof(f97,plain,(
    v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f96,f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).

fof(f96,plain,
    ( v2_struct_0(sK0)
    | v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f95,f24])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f95,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(subsumption_resolution,[],[f94,f22])).

fof(f22,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f94,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(resolution,[],[f88,f23])).

fof(f23,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f88,plain,(
    ! [X6] :
      ( ~ v3_tdlat_3(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6)
      | v3_tex_2(sK1(X6,k1_xboole_0),X6) ) ),
    inference(subsumption_resolution,[],[f87,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(subsumption_resolution,[],[f55,f25])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f55,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(k1_xboole_0)
      | v2_struct_0(X0)
      | v2_tex_2(k1_xboole_0,X0) ) ),
    inference(resolution,[],[f53,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f53,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f52,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f52,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f49,f25])).

fof(f49,plain,(
    ! [X2,X1] :
      ( ~ v1_xboole_0(X1)
      | r1_tarski(X1,X2) ) ),
    inference(subsumption_resolution,[],[f47,f26])).

fof(f26,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f47,plain,(
    ! [X2,X1] :
      ( r1_tarski(X1,X2)
      | ~ v1_xboole_0(X1)
      | v1_xboole_0(k1_tarski(sK2(X1,X2))) ) ),
    inference(resolution,[],[f38,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(sK2(X0,X1)),k1_zfmisc_1(X0))
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f34,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f87,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ v3_tdlat_3(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ v2_tex_2(k1_xboole_0,X6)
      | v3_tex_2(sK1(X6,k1_xboole_0),X6) ) ),
    inference(resolution,[],[f30,f53])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).

fof(f102,plain,(
    ~ v3_tex_2(sK1(sK0,k1_xboole_0),sK0) ),
    inference(resolution,[],[f101,f20])).

fof(f20,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_tex_2(X1,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f101,plain,(
    m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f100,f21])).

fof(f100,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f99,f24])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f98,f22])).

fof(f98,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f93,f23])).

fof(f93,plain,(
    ! [X6] :
      ( ~ v3_tdlat_3(X6)
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6)
      | m1_subset_1(sK1(X6,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(subsumption_resolution,[],[f92,f58])).

fof(f92,plain,(
    ! [X6] :
      ( ~ v2_pre_topc(X6)
      | ~ v3_tdlat_3(X6)
      | ~ l1_pre_topc(X6)
      | v2_struct_0(X6)
      | ~ v2_tex_2(k1_xboole_0,X6)
      | m1_subset_1(sK1(X6,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(resolution,[],[f28,f53])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:19:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (22295)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.45  % (22298)WARNING: option uwaf not known.
% 0.20/0.45  % (22298)lrs+10_4:1_av=off:bd=off:bsr=on:cond=on:fde=unused:inw=on:lcm=reverse:lma=on:lwlo=on:nm=64:nwc=5:stl=90:sp=reverse_arity:thi=strong:uwa=ground:updr=off:uwaf=on_73 on theBenchmark
% 0.20/0.45  % (22294)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.20/0.45  % (22294)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f109,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(subsumption_resolution,[],[f102,f97])).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f96,f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ~v2_struct_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ? [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,negated_conjecture,(
% 0.20/0.45    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.45    inference(negated_conjecture,[],[f9])).
% 0.20/0.45  fof(f9,conjecture,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v3_tex_2(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_tex_2)).
% 0.20/0.45  fof(f96,plain,(
% 0.20/0.45    v2_struct_0(sK0) | v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f95,f24])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    l1_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f95,plain,(
% 0.20/0.45    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f94,f22])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    v2_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f94,plain,(
% 0.20/0.45    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.20/0.45    inference(resolution,[],[f88,f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    v3_tdlat_3(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f88,plain,(
% 0.20/0.45    ( ! [X6] : (~v3_tdlat_3(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X6) | v3_tex_2(sK1(X6,k1_xboole_0),X6)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f87,f58])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f55,f25])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    inference(cnf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    v1_xboole_0(k1_xboole_0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(k1_xboole_0) | v2_struct_0(X0) | v2_tex_2(k1_xboole_0,X0)) )),
% 0.20/0.45    inference(resolution,[],[f53,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | v2_struct_0(X0) | v2_tex_2(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f7])).
% 0.20/0.45  fof(f7,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.20/0.45  fof(f53,plain,(
% 0.20/0.45    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.45    inference(resolution,[],[f52,f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.45  fof(f52,plain,(
% 0.20/0.45    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.45    inference(resolution,[],[f49,f25])).
% 0.20/0.45  fof(f49,plain,(
% 0.20/0.45    ( ! [X2,X1] : (~v1_xboole_0(X1) | r1_tarski(X1,X2)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f47,f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    ( ! [X2,X1] : (r1_tarski(X1,X2) | ~v1_xboole_0(X1) | v1_xboole_0(k1_tarski(sK2(X1,X2)))) )),
% 0.20/0.45    inference(resolution,[],[f38,f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.45  fof(f38,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_subset_1(k1_tarski(sK2(X0,X1)),k1_zfmisc_1(X0)) | r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(resolution,[],[f34,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.45  fof(f87,plain,(
% 0.20/0.45    ( ! [X6] : (~v2_pre_topc(X6) | ~v3_tdlat_3(X6) | ~l1_pre_topc(X6) | v2_struct_0(X6) | ~v2_tex_2(k1_xboole_0,X6) | v3_tex_2(sK1(X6,k1_xboole_0),X6)) )),
% 0.20/0.45    inference(resolution,[],[f30,f53])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | v3_tex_2(sK1(X0,X1),X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (? [X2] : (v3_tex_2(X2,X0) & r1_tarski(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : ((? [X2] : ((v3_tex_2(X2,X0) & r1_tarski(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v3_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(v3_tex_2(X2,X0) & r1_tarski(X1,X2))) & v2_tex_2(X1,X0))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tex_2)).
% 0.20/0.45  fof(f102,plain,(
% 0.20/0.45    ~v3_tex_2(sK1(sK0,k1_xboole_0),sK0)),
% 0.20/0.45    inference(resolution,[],[f101,f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tex_2(X1,sK0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f101,plain,(
% 0.20/0.45    m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(subsumption_resolution,[],[f100,f21])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    v2_struct_0(sK0) | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(subsumption_resolution,[],[f99,f24])).
% 0.20/0.45  fof(f99,plain,(
% 0.20/0.45    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(subsumption_resolution,[],[f98,f22])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(sK1(sK0,k1_xboole_0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(resolution,[],[f93,f23])).
% 0.20/0.45  fof(f93,plain,(
% 0.20/0.45    ( ! [X6] : (~v3_tdlat_3(X6) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | v2_struct_0(X6) | m1_subset_1(sK1(X6,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f92,f58])).
% 0.20/0.45  fof(f92,plain,(
% 0.20/0.45    ( ! [X6] : (~v2_pre_topc(X6) | ~v3_tdlat_3(X6) | ~l1_pre_topc(X6) | v2_struct_0(X6) | ~v2_tex_2(k1_xboole_0,X6) | m1_subset_1(sK1(X6,k1_xboole_0),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 0.20/0.45    inference(resolution,[],[f28,f53])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | m1_subset_1(sK1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (22294)------------------------------
% 0.20/0.45  % (22294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (22294)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (22294)Memory used [KB]: 5373
% 0.20/0.45  % (22294)Time elapsed: 0.051 s
% 0.20/0.45  % (22294)------------------------------
% 0.20/0.45  % (22294)------------------------------
% 0.20/0.45  % (22287)Success in time 0.101 s
%------------------------------------------------------------------------------
