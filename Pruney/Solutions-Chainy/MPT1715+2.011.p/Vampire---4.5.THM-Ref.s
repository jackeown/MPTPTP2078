%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 328 expanded)
%              Number of leaves         :    8 (  66 expanded)
%              Depth                    :   17
%              Number of atoms          :  215 (2127 expanded)
%              Number of equality atoms :    8 (  18 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f331,plain,(
    $false ),
    inference(subsumption_resolution,[],[f330,f321])).

fof(f321,plain,(
    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(resolution,[],[f117,f131])).

fof(f131,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f125,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f125,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f27,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f27,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f117,plain,
    ( ~ l1_pre_topc(sK2)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f116,f111])).

fof(f111,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f25,f47])).

fof(f25,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f11])).

fof(f116,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(resolution,[],[f25,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f330,plain,(
    ~ r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2)) ),
    inference(resolution,[],[f251,f262])).

fof(f262,plain,(
    r1_xboole_0(k2_struct_0(sK2),k2_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f261,f156])).

fof(f156,plain,(
    k2_struct_0(sK2) = u1_struct_0(sK2) ),
    inference(resolution,[],[f134,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f134,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f131,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f261,plain,(
    r1_xboole_0(u1_struct_0(sK2),k2_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f260,f118])).

fof(f118,plain,(
    u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(resolution,[],[f89,f33])).

fof(f89,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f86,f36])).

fof(f86,plain,(
    l1_pre_topc(sK3) ),
    inference(subsumption_resolution,[],[f80,f32])).

fof(f80,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3) ),
    inference(resolution,[],[f24,f47])).

fof(f24,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f260,plain,(
    r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f259,f89])).

fof(f259,plain,
    ( ~ l1_struct_0(sK3)
    | r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f258,f134])).

fof(f258,plain,
    ( ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK3)
    | r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(resolution,[],[f256,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_struct_0(X1)
      | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f256,plain,(
    r1_tsep_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f255,f134])).

fof(f255,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f254,f89])).

fof(f254,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,
    ( r1_tsep_1(sK2,sK3)
    | ~ l1_struct_0(sK3)
    | ~ l1_struct_0(sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(resolution,[],[f22,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f22,plain,
    ( r1_tsep_1(sK3,sK2)
    | r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f11])).

fof(f251,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k2_struct_0(sK3))
      | ~ r1_tarski(k2_struct_0(sK1),X0) ) ),
    inference(resolution,[],[f211,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f211,plain,(
    ~ r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f210,f194])).

fof(f194,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f172,f33])).

fof(f172,plain,(
    l1_struct_0(sK1) ),
    inference(resolution,[],[f169,f36])).

fof(f169,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f163,f32])).

fof(f163,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f29,f47])).

fof(f29,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f210,plain,(
    ~ r1_xboole_0(u1_struct_0(sK1),k2_struct_0(sK3)) ),
    inference(forward_demodulation,[],[f209,f118])).

fof(f209,plain,(
    ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f208,f89])).

fof(f208,plain,
    ( ~ l1_struct_0(sK3)
    | ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(subsumption_resolution,[],[f207,f172])).

fof(f207,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    inference(resolution,[],[f205,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_struct_0(X1)
      | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f205,plain,(
    ~ r1_tsep_1(sK1,sK3) ),
    inference(subsumption_resolution,[],[f204,f89])).

fof(f204,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f203,f172])).

fof(f203,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,
    ( ~ r1_tsep_1(sK1,sK3)
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK3)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(resolution,[],[f21,f48])).

fof(f21,plain,
    ( ~ r1_tsep_1(sK3,sK1)
    | ~ r1_tsep_1(sK1,sK3) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:05:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (25464)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (25464)Refutation not found, incomplete strategy% (25464)------------------------------
% 0.22/0.49  % (25464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25464)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (25464)Memory used [KB]: 10618
% 0.22/0.49  % (25464)Time elapsed: 0.068 s
% 0.22/0.49  % (25464)------------------------------
% 0.22/0.49  % (25464)------------------------------
% 0.22/0.50  % (25473)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (25466)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (25473)Refutation not found, incomplete strategy% (25473)------------------------------
% 0.22/0.50  % (25473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25473)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (25473)Memory used [KB]: 6140
% 0.22/0.50  % (25473)Time elapsed: 0.072 s
% 0.22/0.50  % (25473)------------------------------
% 0.22/0.50  % (25473)------------------------------
% 0.22/0.50  % (25478)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (25476)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (25483)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  % (25476)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f331,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f330,f321])).
% 0.22/0.51  fof(f321,plain,(
% 0.22/0.51    r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.22/0.51    inference(resolution,[],[f117,f131])).
% 0.22/0.51  fof(f131,plain,(
% 0.22/0.51    l1_pre_topc(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f125,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    l1_pre_topc(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3)) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f10])).
% 0.22/0.51  fof(f10,plain,(
% 0.22/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((((~r1_tsep_1(X3,X1) | ~r1_tsep_1(X1,X3)) & (r1_tsep_1(X3,X2) | r1_tsep_1(X2,X3))) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.51    inference(negated_conjecture,[],[f8])).
% 0.22/0.51  fof(f8,conjecture,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tmap_1)).
% 0.22/0.51  fof(f125,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.22/0.51    inference(resolution,[],[f27,f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    m1_pre_topc(sK2,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    ~l1_pre_topc(sK2) | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.22/0.51    inference(subsumption_resolution,[],[f116,f111])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    ~l1_pre_topc(sK2) | l1_pre_topc(sK1)),
% 0.22/0.51    inference(resolution,[],[f25,f47])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    m1_pre_topc(sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f116,plain,(
% 0.22/0.51    ~l1_pre_topc(sK2) | ~l1_pre_topc(sK1) | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.22/0.51    inference(resolution,[],[f25,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~m1_pre_topc(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.22/0.51  fof(f330,plain,(
% 0.22/0.51    ~r1_tarski(k2_struct_0(sK1),k2_struct_0(sK2))),
% 0.22/0.51    inference(resolution,[],[f251,f262])).
% 0.22/0.51  fof(f262,plain,(
% 0.22/0.51    r1_xboole_0(k2_struct_0(sK2),k2_struct_0(sK3))),
% 0.22/0.51    inference(forward_demodulation,[],[f261,f156])).
% 0.22/0.51  fof(f156,plain,(
% 0.22/0.51    k2_struct_0(sK2) = u1_struct_0(sK2)),
% 0.22/0.51    inference(resolution,[],[f134,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,plain,(
% 0.22/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    l1_struct_0(sK2)),
% 0.22/0.51    inference(resolution,[],[f131,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,plain,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.51  fof(f261,plain,(
% 0.22/0.51    r1_xboole_0(u1_struct_0(sK2),k2_struct_0(sK3))),
% 0.22/0.51    inference(forward_demodulation,[],[f260,f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    u1_struct_0(sK3) = k2_struct_0(sK3)),
% 0.22/0.51    inference(resolution,[],[f89,f33])).
% 0.22/0.51  fof(f89,plain,(
% 0.22/0.51    l1_struct_0(sK3)),
% 0.22/0.51    inference(resolution,[],[f86,f36])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    l1_pre_topc(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f80,f32])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | l1_pre_topc(sK3)),
% 0.22/0.51    inference(resolution,[],[f24,f47])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    m1_pre_topc(sK3,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f260,plain,(
% 0.22/0.51    r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.22/0.51    inference(subsumption_resolution,[],[f259,f89])).
% 0.22/0.51  fof(f259,plain,(
% 0.22/0.51    ~l1_struct_0(sK3) | r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.22/0.51    inference(subsumption_resolution,[],[f258,f134])).
% 0.22/0.51  fof(f258,plain,(
% 0.22/0.51    ~l1_struct_0(sK2) | ~l1_struct_0(sK3) | r1_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.22/0.51    inference(resolution,[],[f256,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_struct_0(X1) | r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.22/0.51  fof(f256,plain,(
% 0.22/0.51    r1_tsep_1(sK2,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f255,f134])).
% 0.22/0.51  fof(f255,plain,(
% 0.22/0.51    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK2)),
% 0.22/0.51    inference(subsumption_resolution,[],[f254,f89])).
% 0.22/0.51  fof(f254,plain,(
% 0.22/0.51    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f252])).
% 0.22/0.51  fof(f252,plain,(
% 0.22/0.51    r1_tsep_1(sK2,sK3) | ~l1_struct_0(sK3) | ~l1_struct_0(sK2) | r1_tsep_1(sK2,sK3)),
% 0.22/0.51    inference(resolution,[],[f22,f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | r1_tsep_1(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    r1_tsep_1(sK3,sK2) | r1_tsep_1(sK2,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f251,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_xboole_0(X0,k2_struct_0(sK3)) | ~r1_tarski(k2_struct_0(sK1),X0)) )),
% 0.22/0.51    inference(resolution,[],[f211,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    ~r1_xboole_0(k2_struct_0(sK1),k2_struct_0(sK3))),
% 0.22/0.51    inference(forward_demodulation,[],[f210,f194])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.22/0.51    inference(resolution,[],[f172,f33])).
% 0.22/0.51  fof(f172,plain,(
% 0.22/0.51    l1_struct_0(sK1)),
% 0.22/0.51    inference(resolution,[],[f169,f36])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    l1_pre_topc(sK1)),
% 0.22/0.51    inference(subsumption_resolution,[],[f163,f32])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | l1_pre_topc(sK1)),
% 0.22/0.51    inference(resolution,[],[f29,f47])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    m1_pre_topc(sK1,sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    ~r1_xboole_0(u1_struct_0(sK1),k2_struct_0(sK3))),
% 0.22/0.51    inference(forward_demodulation,[],[f209,f118])).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    ~r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))),
% 0.22/0.51    inference(subsumption_resolution,[],[f208,f89])).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    ~l1_struct_0(sK3) | ~r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))),
% 0.22/0.51    inference(subsumption_resolution,[],[f207,f172])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | ~r1_xboole_0(u1_struct_0(sK1),u1_struct_0(sK3))),
% 0.22/0.51    inference(resolution,[],[f205,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_struct_0(X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    ~r1_tsep_1(sK1,sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f204,f89])).
% 0.22/0.51  fof(f204,plain,(
% 0.22/0.51    ~r1_tsep_1(sK1,sK3) | ~l1_struct_0(sK3)),
% 0.22/0.51    inference(subsumption_resolution,[],[f203,f172])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    ~r1_tsep_1(sK1,sK3) | ~l1_struct_0(sK1) | ~l1_struct_0(sK3)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f201])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    ~r1_tsep_1(sK1,sK3) | ~l1_struct_0(sK1) | ~l1_struct_0(sK3) | ~r1_tsep_1(sK1,sK3)),
% 0.22/0.51    inference(resolution,[],[f21,f48])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ~r1_tsep_1(sK3,sK1) | ~r1_tsep_1(sK1,sK3)),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (25476)------------------------------
% 0.22/0.51  % (25476)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25476)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (25476)Memory used [KB]: 1663
% 0.22/0.51  % (25476)Time elapsed: 0.091 s
% 0.22/0.51  % (25476)------------------------------
% 0.22/0.51  % (25476)------------------------------
% 0.22/0.51  % (25462)Success in time 0.152 s
%------------------------------------------------------------------------------
