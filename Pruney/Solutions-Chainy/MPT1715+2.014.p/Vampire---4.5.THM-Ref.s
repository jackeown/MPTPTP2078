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
% DateTime   : Thu Dec  3 13:18:00 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 468 expanded)
%              Number of leaves         :    8 (  92 expanded)
%              Depth                    :   22
%              Number of atoms          :  235 (3212 expanded)
%              Number of equality atoms :    6 (  12 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f98,plain,(
    $false ),
    inference(subsumption_resolution,[],[f97,f94])).

fof(f94,plain,(
    ~ r1_tsep_1(sK1,sK3) ),
    inference(resolution,[],[f93,f21])).

fof(f21,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ r1_tsep_1(X3,X1)
                    | ~ r1_tsep_1(X1,X3) )
                  & ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X2,X3) )
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
                   => ( m1_pre_topc(X1,X2)
                     => ( ( r1_tsep_1(X3,X1)
                          & r1_tsep_1(X1,X3) )
                        | ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f93,plain,(
    r1_tsep_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f92,f52])).

fof(f52,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f49,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f49,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f45,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f36,f24])).

fof(f24,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f92,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK3,sK1) ),
    inference(resolution,[],[f91,f61])).

fof(f61,plain,(
    r1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f60,f54])).

fof(f54,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f51,f35])).

fof(f51,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f48,f32])).

fof(f48,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f36,f27])).

fof(f27,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,
    ( ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2) ),
    inference(subsumption_resolution,[],[f59,f52])).

fof(f59,plain,
    ( ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK3,sK2) ),
    inference(resolution,[],[f58,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f58,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f57,f52])).

fof(f57,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f56,f54])).

fof(f56,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK2,sK3)
    | r1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f40,f22])).

fof(f22,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f91,plain,(
    ! [X0] :
      ( ~ r1_tsep_1(X0,sK2)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f90,f53])).

fof(f53,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f50,f35])).

fof(f50,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f47,f32])).

fof(f47,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f36,f29])).

fof(f29,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f90,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,sK2)
      | ~ l1_struct_0(sK1)
      | r1_tsep_1(X0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,sK2)
      | ~ l1_struct_0(sK1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,sK1) ) ),
    inference(resolution,[],[f88,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f88,plain,(
    ! [X0] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f87,f54])).

fof(f87,plain,(
    ! [X0] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1))
      | ~ l1_struct_0(sK2)
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,sK2) ) ),
    inference(resolution,[],[f86,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f86,plain,(
    ! [X2] :
      ( ~ r1_xboole_0(X2,u1_struct_0(sK2))
      | r1_xboole_0(X2,u1_struct_0(sK1)) ) ),
    inference(superposition,[],[f41,f83])).

fof(f83,plain,(
    u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f82,f29])).

fof(f82,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f80,f25])).

fof(f25,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK2)
      | ~ m1_pre_topc(X0,sK0)
      | u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f77,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f77,plain,(
    ! [X3] :
      ( r1_tarski(u1_struct_0(X3),u1_struct_0(sK2))
      | ~ m1_pre_topc(X3,sK2)
      | ~ m1_pre_topc(X3,sK0) ) ),
    inference(subsumption_resolution,[],[f76,f31])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f76,plain,(
    ! [X3] :
      ( ~ m1_pre_topc(X3,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X3,sK2)
      | r1_tarski(u1_struct_0(X3),u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f70,f32])).

fof(f70,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X3,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ m1_pre_topc(X3,sK2)
      | r1_tarski(u1_struct_0(X3),u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f37,f27])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f97,plain,(
    r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f96,f52])).

fof(f96,plain,
    ( ~ l1_struct_0(sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f95,f53])).

fof(f95,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | r1_tsep_1(sK1,sK3) ),
    inference(resolution,[],[f93,f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:59:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (15243)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.50  % (15247)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.50  % (15239)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.50  % (15251)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (15239)Refutation not found, incomplete strategy% (15239)------------------------------
% 0.22/0.51  % (15239)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (15239)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (15239)Memory used [KB]: 10618
% 0.22/0.51  % (15239)Time elapsed: 0.066 s
% 0.22/0.51  % (15239)------------------------------
% 0.22/0.51  % (15239)------------------------------
% 0.22/0.52  % (15241)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (15244)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (15233)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.52  % (15244)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(subsumption_resolution,[],[f97,f94])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ~r1_tsep_1(sK1,sK3)),
% 0.22/0.52    inference(resolution,[],[f93,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.52    inference(negated_conjecture,[],[f8])).
% 0.22/0.52  fof(f8,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    r1_tsep_1(sK3,sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f92,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    l1_struct_0(sK3)),
% 0.22/0.52    inference(resolution,[],[f49,f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    l1_pre_topc(sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f45,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.22/0.52    inference(resolution,[],[f36,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    m1_pre_topc(sK3,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    ~l1_struct_0(sK3) | r1_tsep_1(sK3,sK1)),
% 0.22/0.52    inference(resolution,[],[f91,f61])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    r1_tsep_1(sK3,sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f60,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    l1_struct_0(sK2)),
% 0.22/0.52    inference(resolution,[],[f51,f35])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    l1_pre_topc(sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f48,f32])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.22/0.52    inference(resolution,[],[f36,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    m1_pre_topc(sK2,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2)),
% 0.22/0.52    inference(subsumption_resolution,[],[f59,f52])).
% 0.22/0.52  fof(f59,plain,(
% 0.22/0.52    ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | r1_tsep_1(sK3,sK2)),
% 0.22/0.52    inference(resolution,[],[f58,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X1,X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    r1_tsep_1(sK2,sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f57,f52])).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    ~l1_struct_0(sK3) | r1_tsep_1(sK2,sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f56,f54])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | r1_tsep_1(sK2,sK3)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f55])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | r1_tsep_1(sK2,sK3) | r1_tsep_1(sK2,sK3)),
% 0.22/0.52    inference(resolution,[],[f40,f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    ( ! [X0] : (~r1_tsep_1(X0,sK2) | ~l1_struct_0(X0) | r1_tsep_1(X0,sK1)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f90,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    l1_struct_0(sK1)),
% 0.22/0.52    inference(resolution,[],[f50,f35])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    l1_pre_topc(sK1)),
% 0.22/0.52    inference(subsumption_resolution,[],[f47,f32])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 0.22/0.52    inference(resolution,[],[f36,f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    m1_pre_topc(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_struct_0(X0) | ~r1_tsep_1(X0,sK2) | ~l1_struct_0(sK1) | r1_tsep_1(X0,sK1)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    ( ! [X0] : (~l1_struct_0(X0) | ~r1_tsep_1(X0,sK2) | ~l1_struct_0(sK1) | ~l1_struct_0(X0) | r1_tsep_1(X0,sK1)) )),
% 0.22/0.52    inference(resolution,[],[f88,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | r1_tsep_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    ( ! [X0] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,sK2)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f87,f54])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    ( ! [X0] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(sK1)) | ~l1_struct_0(sK2) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,sK2)) )),
% 0.22/0.52    inference(resolution,[],[f86,f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f12])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ( ! [X2] : (~r1_xboole_0(X2,u1_struct_0(sK2)) | r1_xboole_0(X2,u1_struct_0(sK1))) )),
% 0.22/0.52    inference(superposition,[],[f41,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.22/0.52    inference(subsumption_resolution,[],[f82,f29])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ~m1_pre_topc(sK1,sK0) | u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.22/0.52    inference(resolution,[],[f80,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    m1_pre_topc(sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_pre_topc(X0,sK2) | ~m1_pre_topc(X0,sK0) | u1_struct_0(sK2) = k2_xboole_0(u1_struct_0(X0),u1_struct_0(sK2))) )),
% 0.22/0.52    inference(resolution,[],[f77,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.52  fof(f77,plain,(
% 0.22/0.52    ( ! [X3] : (r1_tarski(u1_struct_0(X3),u1_struct_0(sK2)) | ~m1_pre_topc(X3,sK2) | ~m1_pre_topc(X3,sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f76,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    v2_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f11])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X3] : (~m1_pre_topc(X3,sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK2) | r1_tarski(u1_struct_0(X3),u1_struct_0(sK2))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f70,f32])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X3] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X3,sK0) | ~v2_pre_topc(sK0) | ~m1_pre_topc(X3,sK2) | r1_tarski(u1_struct_0(X3),u1_struct_0(sK2))) )),
% 0.22/0.52    inference(resolution,[],[f37,f27])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~m1_pre_topc(X1,X2) | r1_tarski(u1_struct_0(X1),u1_struct_0(X2))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.52    inference(flattening,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    r1_tsep_1(sK1,sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f96,f52])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    ~l1_struct_0(sK3) | r1_tsep_1(sK1,sK3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f95,f53])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | r1_tsep_1(sK1,sK3)),
% 0.22/0.52    inference(resolution,[],[f93,f40])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (15244)------------------------------
% 0.22/0.52  % (15244)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (15244)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (15244)Memory used [KB]: 6140
% 0.22/0.52  % (15244)Time elapsed: 0.049 s
% 0.22/0.52  % (15244)------------------------------
% 0.22/0.52  % (15244)------------------------------
% 0.22/0.52  % (15230)Success in time 0.152 s
%------------------------------------------------------------------------------
