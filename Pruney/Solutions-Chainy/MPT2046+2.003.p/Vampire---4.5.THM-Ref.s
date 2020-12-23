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
% DateTime   : Thu Dec  3 13:23:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 133 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :   24
%              Number of atoms          :  203 ( 598 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(subsumption_resolution,[],[f56,f17])).

fof(f17,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r2_waybel_7(X0,k1_yellow19(X0,X1),X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_waybel_7(X0,k1_yellow19(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow19)).

fof(f56,plain,(
    ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f55,f18])).

fof(f18,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f55,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f54,f15])).

fof(f15,plain,(
    ~ r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f7])).

fof(f54,plain,
    ( r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,
    ( r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1) ),
    inference(resolution,[],[f51,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X3)
              | ~ v3_pre_topc(X3,X0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( r2_waybel_7(X0,X1,X2)
        <=> ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r2_hidden(X2,X3)
                  & v3_pre_topc(X3,X0) )
               => r2_hidden(X3,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_waybel_7)).

fof(f51,plain,(
    ! [X0] :
      ( r2_hidden(sK2(sK0,X0,sK1),k1_yellow19(sK0,sK1))
      | r2_waybel_7(sK0,X0,sK1) ) ),
    inference(subsumption_resolution,[],[f50,f16])).

fof(f16,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f50,plain,(
    ! [X0] :
      ( r2_waybel_7(sK0,X0,sK1)
      | v2_struct_0(sK0)
      | r2_hidden(sK2(sK0,X0,sK1),k1_yellow19(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f49,f14])).

fof(f14,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0] :
      ( r2_waybel_7(sK0,X0,sK1)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(sK2(sK0,X0,sK1),k1_yellow19(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f48,f18])).

fof(f48,plain,(
    ! [X0] :
      ( r2_waybel_7(sK0,X0,sK1)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(sK2(sK0,X0,sK1),k1_yellow19(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f47,f17])).

fof(f47,plain,(
    ! [X0] :
      ( r2_waybel_7(sK0,X0,sK1)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(sK2(sK0,X0,sK1),k1_yellow19(sK0,sK1)) ) ),
    inference(resolution,[],[f46,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X2,k1_yellow19(X0,X1)) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X2,k1_yellow19(X0,X1))
            <=> m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow19)).

fof(f46,plain,(
    ! [X0] :
      ( m1_connsp_2(sK2(sK0,X0,sK1),sK0,sK1)
      | r2_waybel_7(sK0,X0,sK1) ) ),
    inference(resolution,[],[f45,f14])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_connsp_2(sK2(sK0,X1,X0),sK0,X0)
      | r2_waybel_7(sK0,X1,X0) ) ),
    inference(duplicate_literal_removal,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_connsp_2(sK2(sK0,X1,X0),sK0,X0)
      | r2_waybel_7(sK0,X1,X0)
      | r2_waybel_7(sK0,X1,X0) ) ),
    inference(resolution,[],[f43,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK2(sK0,X1,X0))
      | r2_waybel_7(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f29,f17])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | r2_hidden(X0,sK2(sK0,X1,X0))
      | r2_waybel_7(sK0,X1,X0) ) ),
    inference(resolution,[],[f25,f18])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X2,sK2(X0,X1,X2))
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,sK2(sK0,X1,X2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_connsp_2(sK2(sK0,X1,X2),sK0,X0)
      | r2_waybel_7(sK0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f42,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(sK2(sK0,X0,X1),sK0)
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f27,f17])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | v3_pre_topc(sK2(sK0,X0,X1),sK0)
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(resolution,[],[f24,f18])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(sK2(X0,X1,X2),X0)
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_pre_topc(sK2(sK0,X1,X2),sK0)
      | ~ r2_hidden(X0,sK2(sK0,X1,X2))
      | m1_connsp_2(sK2(sK0,X1,X2),sK0,X0)
      | r2_waybel_7(sK0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f41,f16])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_pre_topc(sK2(sK0,X1,X2),sK0)
      | ~ r2_hidden(X0,sK2(sK0,X1,X2))
      | m1_connsp_2(sK2(sK0,X1,X2),sK0,X0)
      | r2_waybel_7(sK0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f40,f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_pre_topc(sK2(sK0,X1,X2),sK0)
      | ~ r2_hidden(X0,sK2(sK0,X1,X2))
      | m1_connsp_2(sK2(sK0,X1,X2),sK0,X0)
      | r2_waybel_7(sK0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f39,f17])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v3_pre_topc(sK2(sK0,X1,X2),sK0)
      | ~ r2_hidden(X0,sK2(sK0,X1,X2))
      | m1_connsp_2(sK2(sK0,X1,X2),sK0,X0)
      | r2_waybel_7(sK0,X1,X2) ) ),
    inference(resolution,[],[f21,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f31,f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | m1_subset_1(sK2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(resolution,[],[f23,f18])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f13])).

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
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (6000)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.47  % (6002)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.47  % (6002)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f56,f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r2_waybel_7(X0,k1_yellow19(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f6])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (~r2_waybel_7(X0,k1_yellow19(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_waybel_7(X0,k1_yellow19(X0,X1),X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f4])).
% 0.21/0.47  fof(f4,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_waybel_7(X0,k1_yellow19(X0,X1),X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow19)).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f55,f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f54,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ~r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f54,plain,(
% 0.21/0.47    r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f52])).
% 0.21/0.47  fof(f52,plain,(
% 0.21/0.47    r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r2_waybel_7(sK0,k1_yellow19(sK0,sK1),sK1)),
% 0.21/0.47    inference(resolution,[],[f51,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_waybel_7(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : ((r2_hidden(X3,X1) | (~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,X3) & v3_pre_topc(X3,X0)) => r2_hidden(X3,X1)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_waybel_7)).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X0] : (r2_hidden(sK2(sK0,X0,sK1),k1_yellow19(sK0,sK1)) | r2_waybel_7(sK0,X0,sK1)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f50,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0] : (r2_waybel_7(sK0,X0,sK1) | v2_struct_0(sK0) | r2_hidden(sK2(sK0,X0,sK1),k1_yellow19(sK0,sK1))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f49,f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0] : (r2_waybel_7(sK0,X0,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK2(sK0,X0,sK1),k1_yellow19(sK0,sK1))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f48,f18])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    ( ! [X0] : (r2_waybel_7(sK0,X0,sK1) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK2(sK0,X0,sK1),k1_yellow19(sK0,sK1))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f47,f17])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X0] : (r2_waybel_7(sK0,X0,sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK2(sK0,X0,sK1),k1_yellow19(sK0,sK1))) )),
% 0.21/0.47    inference(resolution,[],[f46,f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X2,k1_yellow19(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f8])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X2,k1_yellow19(X0,X1)) <=> m1_connsp_2(X2,X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_yellow19)).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X0] : (m1_connsp_2(sK2(sK0,X0,sK1),sK0,sK1) | r2_waybel_7(sK0,X0,sK1)) )),
% 0.21/0.47    inference(resolution,[],[f45,f14])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(sK2(sK0,X1,X0),sK0,X0) | r2_waybel_7(sK0,X1,X0)) )),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(sK2(sK0,X1,X0),sK0,X0) | r2_waybel_7(sK0,X1,X0) | r2_waybel_7(sK0,X1,X0)) )),
% 0.21/0.47    inference(resolution,[],[f43,f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X0,sK2(sK0,X1,X0)) | r2_waybel_7(sK0,X1,X0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f29,f17])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_pre_topc(sK0) | r2_hidden(X0,sK2(sK0,X1,X0)) | r2_waybel_7(sK0,X1,X0)) )),
% 0.21/0.47    inference(resolution,[],[f25,f18])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_hidden(X2,sK2(X0,X1,X2)) | r2_waybel_7(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r2_hidden(X0,sK2(sK0,X1,X2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(sK2(sK0,X1,X2),sK0,X0) | r2_waybel_7(sK0,X1,X2)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f42,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v3_pre_topc(sK2(sK0,X0,X1),sK0) | r2_waybel_7(sK0,X0,X1)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f27,f17])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_pre_topc(sK0) | v3_pre_topc(sK2(sK0,X0,X1),sK0) | r2_waybel_7(sK0,X0,X1)) )),
% 0.21/0.47    inference(resolution,[],[f24,f18])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(sK2(X0,X1,X2),X0) | r2_waybel_7(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_pre_topc(sK2(sK0,X1,X2),sK0) | ~r2_hidden(X0,sK2(sK0,X1,X2)) | m1_connsp_2(sK2(sK0,X1,X2),sK0,X0) | r2_waybel_7(sK0,X1,X2)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f41,f16])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_pre_topc(sK2(sK0,X1,X2),sK0) | ~r2_hidden(X0,sK2(sK0,X1,X2)) | m1_connsp_2(sK2(sK0,X1,X2),sK0,X0) | r2_waybel_7(sK0,X1,X2)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f40,f18])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_pre_topc(sK2(sK0,X1,X2),sK0) | ~r2_hidden(X0,sK2(sK0,X1,X2)) | m1_connsp_2(sK2(sK0,X1,X2),sK0,X0) | r2_waybel_7(sK0,X1,X2)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f39,f17])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v3_pre_topc(sK2(sK0,X1,X2),sK0) | ~r2_hidden(X0,sK2(sK0,X1,X2)) | m1_connsp_2(sK2(sK0,X1,X2),sK0,X0) | r2_waybel_7(sK0,X1,X2)) )),
% 0.21/0.47    inference(resolution,[],[f21,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (m1_subset_1(sK2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_waybel_7(sK0,X0,X1)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f31,f17])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v2_pre_topc(sK0) | m1_subset_1(sK2(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_waybel_7(sK0,X0,X1)) )),
% 0.21/0.47    inference(resolution,[],[f23,f18])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | r2_waybel_7(X0,X1,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (6002)------------------------------
% 0.21/0.47  % (6002)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (6002)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (6002)Memory used [KB]: 5373
% 0.21/0.47  % (6002)Time elapsed: 0.048 s
% 0.21/0.47  % (6002)------------------------------
% 0.21/0.47  % (6002)------------------------------
% 0.21/0.48  % (5995)Success in time 0.116 s
%------------------------------------------------------------------------------
