%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:05 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   41 ( 120 expanded)
%              Number of leaves         :    5 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :  212 (1083 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f112,plain,(
    $false ),
    inference(global_subsumption,[],[f15,f22,f16,f17,f18,f23,f109])).

fof(f109,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | ~ m1_pre_topc(sK1,sK2)
    | ~ m1_pre_topc(sK3,sK2) ),
    inference(resolution,[],[f86,f19])).

fof(f19,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
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
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( m1_pre_topc(X3,X2)
                        & m1_pre_topc(X1,X2) )
                     => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tmap_1)).

fof(f86,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK2)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X1,sK2) ) ),
    inference(global_subsumption,[],[f20,f24,f25,f26,f21,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK2)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK2)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,sK0)
      | ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X1,sK2)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f80,f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X4,X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X4)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      | ~ m1_pre_topc(X3,X4)
                      | ~ m1_pre_topc(X1,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      | ~ m1_pre_topc(X3,X4)
                      | ~ m1_pre_topc(X1,X2)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X1,X2) )
                       => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tmap_1)).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK2,sK2))
      | m1_pre_topc(X0,sK2) ) ),
    inference(global_subsumption,[],[f46,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,k1_tsep_1(sK0,sK2,sK2))
      | ~ l1_pre_topc(sK2)
      | m1_pre_topc(X0,sK2) ) ),
    inference(superposition,[],[f28,f67])).

fof(f67,plain,(
    k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(global_subsumption,[],[f20,f24,f25,f26,f51])).

fof(f51,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK2)
    | v2_struct_0(sK0)
    | k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)) ),
    inference(resolution,[],[f29,f21])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f46,plain,(
    l1_pre_topc(sK2) ),
    inference(global_subsumption,[],[f26,f35])).

fof(f35,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f27,f21])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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

fof(f21,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f20,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f18,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f16,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f22,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:49:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.46  % (19356)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.19/0.47  % (19348)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.19/0.47  % (19356)Refutation not found, incomplete strategy% (19356)------------------------------
% 0.19/0.47  % (19356)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (19356)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (19356)Memory used [KB]: 10618
% 0.19/0.47  % (19356)Time elapsed: 0.045 s
% 0.19/0.47  % (19356)------------------------------
% 0.19/0.47  % (19356)------------------------------
% 0.19/0.49  % (19345)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.19/0.50  % (19345)Refutation found. Thanks to Tanya!
% 0.19/0.50  % SZS status Theorem for theBenchmark
% 0.19/0.50  % SZS output start Proof for theBenchmark
% 0.19/0.50  fof(f112,plain,(
% 0.19/0.50    $false),
% 0.19/0.50    inference(global_subsumption,[],[f15,f22,f16,f17,f18,f23,f109])).
% 0.19/0.50  fof(f109,plain,(
% 0.19/0.50    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(sK1,sK2) | ~m1_pre_topc(sK3,sK2)),
% 0.19/0.50    inference(resolution,[],[f86,f19])).
% 0.19/0.50  fof(f19,plain,(
% 0.19/0.50    ~m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f8,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f7])).
% 0.19/0.50  fof(f7,plain,(
% 0.19/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f6])).
% 0.19/0.50  fof(f6,negated_conjecture,(
% 0.19/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 0.19/0.50    inference(negated_conjecture,[],[f5])).
% 0.19/0.50  fof(f5,conjecture,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tmap_1)).
% 0.19/0.50  fof(f86,plain,(
% 0.19/0.50    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK2)) )),
% 0.19/0.50    inference(global_subsumption,[],[f20,f24,f25,f26,f21,f85])).
% 0.19/0.50  fof(f85,plain,(
% 0.19/0.50    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK2) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(sK0)) )),
% 0.19/0.50    inference(duplicate_literal_removal,[],[f84])).
% 0.19/0.50  fof(f84,plain,(
% 0.19/0.50    ( ! [X0,X1] : (m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK2) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X1,sK2) | v2_struct_0(sK0)) )),
% 0.19/0.50    inference(resolution,[],[f80,f30])).
% 0.19/0.50  fof(f30,plain,(
% 0.19/0.50    ( ! [X4,X2,X0,X3,X1] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X4) | ~m1_pre_topc(X4,X0) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X4) | v2_struct_0(X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f14])).
% 0.19/0.50  fof(f14,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) | ~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f13])).
% 0.19/0.50  fof(f13,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) | (~m1_pre_topc(X3,X4) | ~m1_pre_topc(X1,X2))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f4])).
% 0.19/0.50  fof(f4,axiom,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X3,X4) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))))))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tmap_1)).
% 0.19/0.50  fof(f80,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_pre_topc(X0,k1_tsep_1(sK0,sK2,sK2)) | m1_pre_topc(X0,sK2)) )),
% 0.19/0.50    inference(global_subsumption,[],[f46,f79])).
% 0.19/0.50  fof(f79,plain,(
% 0.19/0.50    ( ! [X0] : (~m1_pre_topc(X0,k1_tsep_1(sK0,sK2,sK2)) | ~l1_pre_topc(sK2) | m1_pre_topc(X0,sK2)) )),
% 0.19/0.50    inference(superposition,[],[f28,f67])).
% 0.19/0.50  fof(f67,plain,(
% 0.19/0.50    k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.19/0.50    inference(global_subsumption,[],[f20,f24,f25,f26,f51])).
% 0.19/0.50  fof(f51,plain,(
% 0.19/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | k1_tsep_1(sK0,sK2,sK2) = g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),
% 0.19/0.50    inference(resolution,[],[f29,f21])).
% 0.19/0.50  fof(f29,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )),
% 0.19/0.50    inference(cnf_transformation,[],[f12])).
% 0.19/0.50  fof(f12,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.50    inference(flattening,[],[f11])).
% 0.19/0.50  fof(f11,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.50    inference(ennf_transformation,[],[f3])).
% 0.19/0.50  fof(f3,axiom,(
% 0.19/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).
% 0.19/0.50  fof(f28,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | m1_pre_topc(X1,X0)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f10])).
% 0.19/0.50  fof(f10,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f2])).
% 0.19/0.50  fof(f2,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.19/0.50  fof(f46,plain,(
% 0.19/0.50    l1_pre_topc(sK2)),
% 0.19/0.50    inference(global_subsumption,[],[f26,f35])).
% 0.19/0.50  fof(f35,plain,(
% 0.19/0.50    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.19/0.50    inference(resolution,[],[f27,f21])).
% 0.19/0.50  fof(f27,plain,(
% 0.19/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.19/0.50    inference(cnf_transformation,[],[f9])).
% 0.19/0.50  fof(f9,plain,(
% 0.19/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.19/0.50    inference(ennf_transformation,[],[f1])).
% 0.19/0.50  fof(f1,axiom,(
% 0.19/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.19/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.19/0.50  fof(f21,plain,(
% 0.19/0.50    m1_pre_topc(sK2,sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f26,plain,(
% 0.19/0.50    l1_pre_topc(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f25,plain,(
% 0.19/0.50    v2_pre_topc(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f24,plain,(
% 0.19/0.50    ~v2_struct_0(sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f20,plain,(
% 0.19/0.50    ~v2_struct_0(sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f23,plain,(
% 0.19/0.50    m1_pre_topc(sK1,sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f18,plain,(
% 0.19/0.50    m1_pre_topc(sK3,sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f17,plain,(
% 0.19/0.50    m1_pre_topc(sK1,sK2)),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f16,plain,(
% 0.19/0.50    m1_pre_topc(sK3,sK0)),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f22,plain,(
% 0.19/0.50    ~v2_struct_0(sK1)),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  fof(f15,plain,(
% 0.19/0.50    ~v2_struct_0(sK3)),
% 0.19/0.50    inference(cnf_transformation,[],[f8])).
% 0.19/0.50  % SZS output end Proof for theBenchmark
% 0.19/0.50  % (19345)------------------------------
% 0.19/0.50  % (19345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (19345)Termination reason: Refutation
% 0.19/0.50  
% 0.19/0.50  % (19345)Memory used [KB]: 10746
% 0.19/0.50  % (19345)Time elapsed: 0.063 s
% 0.19/0.50  % (19345)------------------------------
% 0.19/0.50  % (19345)------------------------------
% 0.19/0.50  % (19332)Success in time 0.15 s
%------------------------------------------------------------------------------
