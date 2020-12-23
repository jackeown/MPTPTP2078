%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 125 expanded)
%              Number of leaves         :    5 (  24 expanded)
%              Depth                    :   13
%              Number of atoms          :  225 (1220 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   20 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f83,plain,(
    $false ),
    inference(global_subsumption,[],[f21,f23,f17,f18,f19,f22,f24,f80])).

fof(f80,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK2,sK3)
    | r1_tsep_1(sK1,sK2) ),
    inference(resolution,[],[f69,f20])).

fof(f20,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
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
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
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
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
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
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                      | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).

fof(f69,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK3)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X1,sK3)
      | r1_tsep_1(X0,X1) ) ),
    inference(global_subsumption,[],[f15,f25,f26,f27,f16,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK3)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X1,sK3)
      | r1_tsep_1(X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK3)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | v2_struct_0(sK3)
      | ~ m1_pre_topc(sK3,sK0)
      | ~ m1_pre_topc(X0,sK3)
      | ~ m1_pre_topc(X1,sK3)
      | r1_tsep_1(X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f66,f31])).

fof(f31,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
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
      | ~ m1_pre_topc(X1,X3)
      | ~ m1_pre_topc(X2,X4)
      | r1_tsep_1(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
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
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
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
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X1,X3) )
                       => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tmap_1)).

fof(f66,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK3))
      | m1_pre_topc(X0,sK3) ) ),
    inference(global_subsumption,[],[f37,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK3))
      | ~ l1_pre_topc(sK3)
      | m1_pre_topc(X0,sK3) ) ),
    inference(superposition,[],[f29,f47])).

fof(f47,plain,(
    k2_tsep_1(sK0,sK3,sK3) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(global_subsumption,[],[f15,f25,f26,f27,f42])).

fof(f42,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK3)
    | v2_struct_0(sK0)
    | k2_tsep_1(sK0,sK3,sK3) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) ),
    inference(resolution,[],[f30,f16])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
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
         => k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tmap_1)).

fof(f29,plain,(
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

fof(f37,plain,(
    l1_pre_topc(sK3) ),
    inference(global_subsumption,[],[f27,f32])).

fof(f32,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f28,f16])).

fof(f28,plain,(
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

fof(f16,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f15,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f24,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f22,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f19,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f18,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f17,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f8])).

fof(f23,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f8])).

fof(f21,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:56:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.43  % (1932)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.45  % (1924)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.45  % (1932)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f83,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(global_subsumption,[],[f21,f23,f17,f18,f19,f22,f24,f80])).
% 0.20/0.45  fof(f80,plain,(
% 0.20/0.45    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK2,sK3) | r1_tsep_1(sK1,sK2)),
% 0.20/0.45    inference(resolution,[],[f69,f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f7])).
% 0.20/0.45  fof(f7,plain,(
% 0.20/0.45    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,negated_conjecture,(
% 0.20/0.45    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.20/0.45    inference(negated_conjecture,[],[f5])).
% 0.20/0.45  fof(f5,conjecture,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tmap_1)).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK3) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X0,X1)) )),
% 0.20/0.45    inference(global_subsumption,[],[f15,f25,f26,f27,f16,f68])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK3) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X0,X1) | v2_struct_0(sK0)) )),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f67])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    ( ! [X0,X1] : (m1_pre_topc(k2_tsep_1(sK0,X0,X1),sK3) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~m1_pre_topc(sK3,sK0) | ~m1_pre_topc(X0,sK3) | ~m1_pre_topc(X1,sK3) | r1_tsep_1(X0,X1) | v2_struct_0(sK0)) )),
% 0.20/0.45    inference(resolution,[],[f66,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X4,X2,X0,X3,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~m1_pre_topc(X3,X0) | v2_struct_0(X4) | ~m1_pre_topc(X4,X0) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X2,X4) | r1_tsep_1(X1,X2) | v2_struct_0(X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2))))))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_tmap_1)).
% 0.20/0.45  fof(f66,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK3)) | m1_pre_topc(X0,sK3)) )),
% 0.20/0.45    inference(global_subsumption,[],[f37,f65])).
% 0.20/0.45  fof(f65,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_pre_topc(X0,k2_tsep_1(sK0,sK3,sK3)) | ~l1_pre_topc(sK3) | m1_pre_topc(X0,sK3)) )),
% 0.20/0.45    inference(superposition,[],[f29,f47])).
% 0.20/0.45  fof(f47,plain,(
% 0.20/0.45    k2_tsep_1(sK0,sK3,sK3) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.20/0.45    inference(global_subsumption,[],[f15,f25,f26,f27,f42])).
% 0.20/0.45  fof(f42,plain,(
% 0.20/0.45    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK3) | v2_struct_0(sK0) | k2_tsep_1(sK0,sK3,sK3) = g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),
% 0.20/0.45    inference(resolution,[],[f30,f16])).
% 0.20/0.45  fof(f30,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.45    inference(flattening,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k2_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_tmap_1)).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | m1_pre_topc(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    l1_pre_topc(sK3)),
% 0.20/0.45    inference(global_subsumption,[],[f27,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.20/0.45    inference(resolution,[],[f28,f16])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f9])).
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    m1_pre_topc(sK3,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    l1_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    v2_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ~v2_struct_0(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ~v2_struct_0(sK3)),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    m1_pre_topc(sK1,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    m1_pre_topc(sK2,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ~r1_tsep_1(sK1,sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    m1_pre_topc(sK2,sK3)),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    m1_pre_topc(sK1,sK3)),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ~v2_struct_0(sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ~v2_struct_0(sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f8])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (1932)------------------------------
% 0.20/0.45  % (1932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (1932)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (1932)Memory used [KB]: 10618
% 0.20/0.45  % (1932)Time elapsed: 0.067 s
% 0.20/0.45  % (1932)------------------------------
% 0.20/0.45  % (1932)------------------------------
% 0.20/0.45  % (1917)Success in time 0.095 s
%------------------------------------------------------------------------------
