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
% DateTime   : Thu Dec  3 13:23:06 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 244 expanded)
%              Number of leaves         :    3 (  42 expanded)
%              Depth                    :   23
%              Number of atoms          :  210 (1232 expanded)
%              Number of equality atoms :    9 (  36 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(subsumption_resolution,[],[f54,f12])).

fof(f12,plain,(
    ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => m1_connsp_2(X2,X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f54,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(subsumption_resolution,[],[f53,f32])).

fof(f32,plain,(
    r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f31,f26])).

fof(f26,plain,(
    sK2 = sK3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f25,f14])).

fof(f14,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f25,plain,
    ( v2_struct_0(sK0)
    | sK2 = sK3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f24,f13])).

fof(f13,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f24,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK2 = sK3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f23,f16])).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f23,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK2 = sK3(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f22,f15])).

fof(f15,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f6])).

fof(f22,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK2 = sK3(sK0,sK1,sK2) ),
    inference(resolution,[],[f18,f11])).

fof(f11,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f6])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | sK3(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).

fof(f31,plain,(
    r2_hidden(sK1,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f30,f14])).

fof(f30,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(sK1,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f29,f13])).

fof(f29,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f28,f16])).

fof(f28,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,sK3(sK0,sK1,sK2)) ),
    inference(subsumption_resolution,[],[f27,f15])).

fof(f27,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,sK3(sK0,sK1,sK2)) ),
    inference(resolution,[],[f19,f11])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,sK3(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,
    ( ~ r2_hidden(sK1,sK2)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(resolution,[],[f52,f13])).

fof(f52,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ r2_hidden(X4,sK2)
      | m1_connsp_2(sK2,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f51,f38])).

fof(f38,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(forward_demodulation,[],[f37,f26])).

fof(f37,plain,(
    v3_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f36,f14])).

fof(f36,plain,
    ( v2_struct_0(sK0)
    | v3_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f35,f13])).

fof(f35,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f34,f16])).

fof(f34,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f33,f15])).

fof(f33,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK3(sK0,sK1,sK2),sK0) ),
    inference(resolution,[],[f20,f11])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v3_pre_topc(sK3(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v3_pre_topc(sK2,sK0)
      | ~ r2_hidden(X4,sK2)
      | m1_connsp_2(sK2,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f50,f14])).

fof(f50,plain,(
    ! [X4] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v3_pre_topc(sK2,sK0)
      | ~ r2_hidden(X4,sK2)
      | m1_connsp_2(sK2,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f49,f16])).

fof(f49,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v3_pre_topc(sK2,sK0)
      | ~ r2_hidden(X4,sK2)
      | m1_connsp_2(sK2,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f46,f15])).

fof(f46,plain,(
    ! [X4] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ v3_pre_topc(sK2,sK0)
      | ~ r2_hidden(X4,sK2)
      | m1_connsp_2(sK2,sK0,X4) ) ),
    inference(resolution,[],[f21,f44])).

fof(f44,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f43,f14])).

fof(f43,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f42,f11])).

fof(f42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f41,f13])).

fof(f41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f40,f16])).

fof(f40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f39,f15])).

fof(f39,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f17,f26])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:40:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (21667)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.47  % (21675)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.48  % (21674)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.48  % (21666)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.48  % (21675)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f54,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ~m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (~m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f5])).
% 0.21/0.49  fof(f5,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (~m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f3])).
% 0.21/0.49  fof(f3,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f53,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    r2_hidden(sK1,sK2)),
% 0.21/0.49    inference(forward_demodulation,[],[f31,f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    sK2 = sK3(sK0,sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f25,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    v2_struct_0(sK0) | sK2 = sK3(sK0,sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f24,f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | sK2 = sK3(sK0,sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f23,f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | sK2 = sK3(sK0,sK1,sK2)),
% 0.21/0.49    inference(subsumption_resolution,[],[f22,f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | sK2 = sK3(sK0,sK1,sK2)),
% 0.21/0.49    inference(resolution,[],[f18,f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 0.21/0.49    inference(cnf_transformation,[],[f6])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | sK3(X0,X1,X2) = X2) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f7])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_6)).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    r2_hidden(sK1,sK3(sK0,sK1,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f30,f14])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    v2_struct_0(sK0) | r2_hidden(sK1,sK3(sK0,sK1,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f29,f13])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,sK3(sK0,sK1,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f28,f16])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,sK3(sK0,sK1,sK2))),
% 0.21/0.49    inference(subsumption_resolution,[],[f27,f15])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK1,sK3(sK0,sK1,sK2))),
% 0.21/0.49    inference(resolution,[],[f19,f11])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,sK3(X0,X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ~r2_hidden(sK1,sK2) | m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(resolution,[],[f52,f13])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_hidden(X4,sK2) | m1_connsp_2(sK2,sK0,X4)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f51,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v3_pre_topc(sK2,sK0)),
% 0.21/0.49    inference(forward_demodulation,[],[f37,f26])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    v3_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f36,f14])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    v2_struct_0(sK0) | v3_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f35,f13])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | v3_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f34,f16])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | v3_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f33,f15])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | v3_pre_topc(sK3(sK0,sK1,sK2),sK0)),
% 0.21/0.49    inference(resolution,[],[f20,f11])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | v3_pre_topc(sK3(X0,X1,X2),X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | ~v3_pre_topc(sK2,sK0) | ~r2_hidden(X4,sK2) | m1_connsp_2(sK2,sK0,X4)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f50,f14])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X4] : (v2_struct_0(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~v3_pre_topc(sK2,sK0) | ~r2_hidden(X4,sK2) | m1_connsp_2(sK2,sK0,X4)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f49,f16])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X4] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~v3_pre_topc(sK2,sK0) | ~r2_hidden(X4,sK2) | m1_connsp_2(sK2,sK0,X4)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f46,f15])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X4] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~v3_pre_topc(sK2,sK0) | ~r2_hidden(X4,sK2) | m1_connsp_2(sK2,sK0,X4)) )),
% 0.21/0.49    inference(resolution,[],[f21,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f43,f14])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f42,f11])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f41,f13])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f40,f16])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f39,f15])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | v2_struct_0(sK0)),
% 0.21/0.49    inference(superposition,[],[f17,f26])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f8])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (21675)------------------------------
% 0.21/0.49  % (21675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (21675)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (21675)Memory used [KB]: 6140
% 0.21/0.49  % (21675)Time elapsed: 0.080 s
% 0.21/0.49  % (21675)------------------------------
% 0.21/0.49  % (21675)------------------------------
% 0.21/0.49  % (21658)Success in time 0.126 s
%------------------------------------------------------------------------------
