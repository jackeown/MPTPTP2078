%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   43 ( 111 expanded)
%              Number of leaves         :    4 (  20 expanded)
%              Depth                    :   19
%              Number of atoms          :  148 ( 528 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(subsumption_resolution,[],[f54,f15])).

fof(f15,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_waybel_7(X0,X2,X3)
          & r2_waybel_7(X0,X1,X3)
          & r1_tarski(X1,X2) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1,X2,X3] :
          ( ~ r2_waybel_7(X0,X2,X3)
          & r2_waybel_7(X0,X1,X3)
          & r1_tarski(X1,X2) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2,X3] :
            ( ( r2_waybel_7(X0,X1,X3)
              & r1_tarski(X1,X2) )
           => r2_waybel_7(X0,X2,X3) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2,X3] :
          ( ( r2_waybel_7(X0,X1,X3)
            & r1_tarski(X1,X2) )
         => r2_waybel_7(X0,X2,X3) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow19)).

fof(f54,plain,(
    ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f53,f16])).

fof(f16,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f53,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f52,f13])).

fof(f13,plain,(
    ~ r2_waybel_7(sK0,sK2,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f52,plain,
    ( r2_waybel_7(sK0,sK2,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0) ),
    inference(duplicate_literal_removal,[],[f51])).

fof(f51,plain,
    ( r2_waybel_7(sK0,sK2,sK3)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r2_waybel_7(sK0,sK2,sK3) ),
    inference(resolution,[],[f49,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_waybel_7)).

fof(f49,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0,sK3),sK2)
      | r2_waybel_7(sK0,X0,sK3) ) ),
    inference(resolution,[],[f46,f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f22,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2)) ),
    inference(resolution,[],[f23,f11])).

fof(f11,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK4(sK0,X0,sK3),sK1)
      | r2_waybel_7(sK0,X0,sK3) ) ),
    inference(resolution,[],[f45,f12])).

fof(f12,plain,(
    r2_waybel_7(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f7])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_waybel_7(sK0,X2,X1)
      | r2_hidden(sK4(sK0,X0,X1),X2)
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(sK0,X0,X1),X2)
      | ~ r2_waybel_7(sK0,X2,X1)
      | r2_waybel_7(sK0,X0,X1)
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(resolution,[],[f40,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,sK4(sK0,X1,X0))
      | r2_waybel_7(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f30,f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | r2_hidden(X0,sK4(sK0,X1,X0))
      | r2_waybel_7(sK0,X1,X0) ) ),
    inference(resolution,[],[f20,f16])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X2,sK4(X0,X1,X2))
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,sK4(sK0,X0,X1))
      | r2_hidden(sK4(sK0,X0,X1),X3)
      | ~ r2_waybel_7(sK0,X3,X2)
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f39,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(sK4(sK0,X0,X1),sK0)
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f28,f15])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | v3_pre_topc(sK4(sK0,X0,X1),sK0)
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(resolution,[],[f19,f16])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v3_pre_topc(sK4(sK0,X0,X1),sK0)
      | ~ r2_hidden(X2,sK4(sK0,X0,X1))
      | r2_hidden(sK4(sK0,X0,X1),X3)
      | ~ r2_waybel_7(sK0,X3,X2)
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f38,f15])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ v3_pre_topc(sK4(sK0,X0,X1),sK0)
      | ~ r2_hidden(X2,sK4(sK0,X0,X1))
      | r2_hidden(sK4(sK0,X0,X1),X3)
      | ~ r2_waybel_7(sK0,X3,X2)
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f37,f16])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ v3_pre_topc(sK4(sK0,X0,X1),sK0)
      | ~ r2_hidden(X2,sK4(sK0,X0,X1))
      | r2_hidden(sK4(sK0,X0,X1),X3)
      | ~ r2_waybel_7(sK0,X3,X2)
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(resolution,[],[f17,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f32,f15])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_waybel_7(sK0,X0,X1) ) ),
    inference(resolution,[],[f18,f16])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f17,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(X3,X1)
      | ~ r2_waybel_7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:45:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (25539)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.48  % (25547)lrs+1_1_av=off:bsr=on:br=off:gs=on:gsem=on:lma=on:lwlo=on:nm=64:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_152 on theBenchmark
% 0.21/0.48  % (25550)ott+11_5:1_afp=100000:afq=1.1:br=off:gs=on:nm=64:nwc=1:sos=all:urr=on:updr=off_287 on theBenchmark
% 0.21/0.48  % (25541)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (25548)ott+1_40_av=off:bs=unit_only:bsr=on:br=off:fsr=off:lma=on:nm=64:newcnf=on:nwc=1.5:sp=occurrence:urr=on:updr=off_81 on theBenchmark
% 0.21/0.48  % (25539)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f54,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1,X2,X3] : (~r2_waybel_7(X0,X2,X3) & r2_waybel_7(X0,X1,X3) & r1_tarski(X1,X2)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : (? [X1,X2,X3] : (~r2_waybel_7(X0,X2,X3) & (r2_waybel_7(X0,X1,X3) & r1_tarski(X1,X2))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1,X2,X3] : ((r2_waybel_7(X0,X1,X3) & r1_tarski(X1,X2)) => r2_waybel_7(X0,X2,X3)))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1,X2,X3] : ((r2_waybel_7(X0,X1,X3) & r1_tarski(X1,X2)) => r2_waybel_7(X0,X2,X3)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_yellow19)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f53,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f52,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ~r2_waybel_7(sK0,sK2,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    r2_waybel_7(sK0,sK2,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f51])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    r2_waybel_7(sK0,sK2,sK3) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r2_waybel_7(sK0,sK2,sK3)),
% 0.21/0.48    inference(resolution,[],[f49,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_waybel_7(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : ((r2_hidden(X3,X1) | (~r2_hidden(X2,X3) | ~v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (r2_waybel_7(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,X3) & v3_pre_topc(X3,X0)) => r2_hidden(X3,X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_waybel_7)).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK4(sK0,X0,sK3),sK2) | r2_waybel_7(sK0,X0,sK3)) )),
% 0.21/0.48    inference(resolution,[],[f46,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,sK1) | r2_hidden(X0,sK2)) )),
% 0.21/0.48    inference(resolution,[],[f22,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(sK2))),
% 0.21/0.48    inference(resolution,[],[f23,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    r1_tarski(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0] : (r2_hidden(sK4(sK0,X0,sK3),sK1) | r2_waybel_7(sK0,X0,sK3)) )),
% 0.21/0.48    inference(resolution,[],[f45,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    r2_waybel_7(sK0,sK1,sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~r2_waybel_7(sK0,X2,X1) | r2_hidden(sK4(sK0,X0,X1),X2) | r2_waybel_7(sK0,X0,X1)) )),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (r2_hidden(sK4(sK0,X0,X1),X2) | ~r2_waybel_7(sK0,X2,X1) | r2_waybel_7(sK0,X0,X1) | r2_waybel_7(sK0,X0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f40,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X0,sK4(sK0,X1,X0)) | r2_waybel_7(sK0,X1,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f30,f15])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pre_topc(sK0) | r2_hidden(X0,sK4(sK0,X1,X0)) | r2_waybel_7(sK0,X1,X0)) )),
% 0.21/0.48    inference(resolution,[],[f20,f16])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_hidden(X2,sK4(X0,X1,X2)) | r2_waybel_7(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,sK4(sK0,X0,X1)) | r2_hidden(sK4(sK0,X0,X1),X3) | ~r2_waybel_7(sK0,X3,X2) | r2_waybel_7(sK0,X0,X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f39,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v3_pre_topc(sK4(sK0,X0,X1),sK0) | r2_waybel_7(sK0,X0,X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f28,f15])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pre_topc(sK0) | v3_pre_topc(sK4(sK0,X0,X1),sK0) | r2_waybel_7(sK0,X0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f19,f16])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(sK4(X0,X1,X2),X0) | r2_waybel_7(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v3_pre_topc(sK4(sK0,X0,X1),sK0) | ~r2_hidden(X2,sK4(sK0,X0,X1)) | r2_hidden(sK4(sK0,X0,X1),X3) | ~r2_waybel_7(sK0,X3,X2) | r2_waybel_7(sK0,X0,X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f38,f15])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(sK0) | ~v3_pre_topc(sK4(sK0,X0,X1),sK0) | ~r2_hidden(X2,sK4(sK0,X0,X1)) | r2_hidden(sK4(sK0,X0,X1),X3) | ~r2_waybel_7(sK0,X3,X2) | r2_waybel_7(sK0,X0,X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f37,f16])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~v3_pre_topc(sK4(sK0,X0,X1),sK0) | ~r2_hidden(X2,sK4(sK0,X0,X1)) | r2_hidden(sK4(sK0,X0,X1),X3) | ~r2_waybel_7(sK0,X3,X2) | r2_waybel_7(sK0,X0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f17,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X0,X1] : (m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_waybel_7(sK0,X0,X1)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f32,f15])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v2_pre_topc(sK0) | m1_subset_1(sK4(sK0,X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_waybel_7(sK0,X0,X1)) )),
% 0.21/0.48    inference(resolution,[],[f18,f16])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | r2_waybel_7(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~v3_pre_topc(X3,X0) | ~r2_hidden(X2,X3) | r2_hidden(X3,X1) | ~r2_waybel_7(X0,X1,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (25539)------------------------------
% 0.21/0.48  % (25539)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (25539)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (25539)Memory used [KB]: 5373
% 0.21/0.48  % (25539)Time elapsed: 0.057 s
% 0.21/0.48  % (25539)------------------------------
% 0.21/0.48  % (25539)------------------------------
% 0.21/0.49  % (25532)Success in time 0.121 s
%------------------------------------------------------------------------------
