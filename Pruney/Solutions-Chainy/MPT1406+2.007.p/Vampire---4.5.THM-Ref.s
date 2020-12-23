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
% DateTime   : Thu Dec  3 13:15:29 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   38 (  83 expanded)
%              Number of leaves         :    5 (  15 expanded)
%              Depth                    :   12
%              Number of atoms          :  126 ( 367 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f89,plain,(
    $false ),
    inference(subsumption_resolution,[],[f88,f17])).

fof(f17,plain,(
    ~ r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,X2)
              & m2_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(X1,X2)
              & m2_connsp_2(X2,X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_connsp_2(X2,X0,X1)
               => r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_connsp_2(X2,X0,X1)
             => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_connsp_2)).

fof(f88,plain,(
    r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f86,f38])).

fof(f38,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f35,f21])).

fof(f21,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f33,f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f33,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f32,f16])).

fof(f16,plain,(
    m2_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ~ m2_connsp_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f31,f20])).

fof(f20,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ m2_connsp_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f30,f21])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m2_connsp_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f25,f18])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m2_connsp_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X2] :
          ( m2_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_connsp_2)).

fof(f86,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tops_1(sK0,sK2),X0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f84,f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f84,plain,(
    r1_tarski(sK1,k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f81,f16])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m2_connsp_2(X0,sK0,sK1)
      | r1_tarski(sK1,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f80,f20])).

fof(f80,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | r1_tarski(sK1,k1_tops_1(sK0,X0))
      | ~ m2_connsp_2(X0,sK0,sK1) ) ),
    inference(subsumption_resolution,[],[f78,f21])).

fof(f78,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | r1_tarski(sK1,k1_tops_1(sK0,X0))
      | ~ m2_connsp_2(X0,sK0,sK1) ) ),
    inference(resolution,[],[f57,f18])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1) ) ),
    inference(subsumption_resolution,[],[f24,f25])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

% (26540)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:47:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.45  % (26532)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.21/0.46  % (26533)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.46  % (26533)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(subsumption_resolution,[],[f88,f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ~r1_tarski(sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,X2) & m2_connsp_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.46    inference(flattening,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(X1,X2) & m2_connsp_2(X2,X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,negated_conjecture,(
% 0.21/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m2_connsp_2(X2,X0,X1) => r1_tarski(X1,X2))))),
% 0.21/0.46    inference(negated_conjecture,[],[f5])).
% 0.21/0.46  fof(f5,conjecture,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m2_connsp_2(X2,X0,X1) => r1_tarski(X1,X2))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_connsp_2)).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    r1_tarski(sK1,sK2)),
% 0.21/0.46    inference(resolution,[],[f86,f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.21/0.46    inference(subsumption_resolution,[],[f35,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    l1_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.21/0.46    inference(resolution,[],[f33,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    inference(resolution,[],[f32,f16])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    m2_connsp_2(sK2,sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    ( ! [X0] : (~m2_connsp_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f31,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    v2_pre_topc(sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_pre_topc(sK0) | ~m2_connsp_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f30,f21])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~m2_connsp_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.46    inference(resolution,[],[f25,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m2_connsp_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,axiom,(
% 0.21/0.46    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X2] : (m2_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m2_connsp_2)).
% 0.21/0.46  fof(f86,plain,(
% 0.21/0.46    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,sK2),X0) | r1_tarski(sK1,X0)) )),
% 0.21/0.46    inference(resolution,[],[f84,f26])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    r1_tarski(sK1,k1_tops_1(sK0,sK2))),
% 0.21/0.46    inference(resolution,[],[f81,f16])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    ( ! [X0] : (~m2_connsp_2(X0,sK0,sK1) | r1_tarski(sK1,k1_tops_1(sK0,X0))) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f80,f20])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    ( ! [X0] : (~v2_pre_topc(sK0) | r1_tarski(sK1,k1_tops_1(sK0,X0)) | ~m2_connsp_2(X0,sK0,sK1)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f78,f21])).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    ( ! [X0] : (~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r1_tarski(sK1,k1_tops_1(sK0,X0)) | ~m2_connsp_2(X0,sK0,sK1)) )),
% 0.21/0.46    inference(resolution,[],[f57,f18])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1)) )),
% 0.21/0.46    inference(subsumption_resolution,[],[f24,f25])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.46    inference(flattening,[],[f10])).
% 0.21/0.46  % (26540)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (26533)------------------------------
% 0.21/0.46  % (26533)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (26533)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (26533)Memory used [KB]: 5373
% 0.21/0.46  % (26533)Time elapsed: 0.053 s
% 0.21/0.46  % (26533)------------------------------
% 0.21/0.46  % (26533)------------------------------
% 0.21/0.46  % (26526)Success in time 0.111 s
%------------------------------------------------------------------------------
