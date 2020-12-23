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
% DateTime   : Thu Dec  3 13:15:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 161 expanded)
%              Number of leaves         :   12 (  32 expanded)
%              Depth                    :   16
%              Number of atoms          :  202 ( 921 expanded)
%              Number of equality atoms :   17 (  85 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(subsumption_resolution,[],[f105,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_xboole_0 = X2
              & ! [X3] :
                  ( ( r2_hidden(X3,X2)
                  <=> ( r2_hidden(X1,X3)
                      & v4_pre_topc(X3,X0)
                      & v3_pre_topc(X3,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
               => ~ ( k1_xboole_0 = X2
                    & ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ( r2_hidden(X3,X2)
                        <=> ( r2_hidden(X1,X3)
                            & v4_pre_topc(X3,X0)
                            & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ~ ( k1_xboole_0 = X2
                  & ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( r2_hidden(X3,X2)
                      <=> ( r2_hidden(X1,X3)
                          & v4_pre_topc(X3,X0)
                          & v3_pre_topc(X3,X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).

fof(f105,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f104,f36])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f104,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f103,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f103,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f102,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK3(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v4_pre_topc(X1,X0)
          & v3_pre_topc(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).

fof(f102,plain,(
    v1_xboole_0(sK3(sK0)) ),
    inference(subsumption_resolution,[],[f98,f92])).

fof(f92,plain,(
    v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f79,f91])).

fof(f91,plain,(
    ~ r2_hidden(sK1,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f90,f75])).

fof(f75,plain,(
    v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f74,f36])).

fof(f74,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f46,f35])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f90,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f89,f77])).

fof(f77,plain,(
    v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f76,f36])).

fof(f76,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f47,f35])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f89,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f66,f60])).

fof(f60,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f38,f37])).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f66,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(backward_demodulation,[],[f63,f65])).

fof(f65,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f39,f61])).

fof(f61,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f40,f36])).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f63,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(subsumption_resolution,[],[f56,f62])).

fof(f62,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f48,f53])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k2_zfmisc_1(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f48,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f56,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(forward_demodulation,[],[f30,f32])).

fof(f32,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f79,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f49,f71])).

fof(f71,plain,(
    m1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f33,f65])).

fof(f33,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f98,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK3(sK0)) ),
    inference(resolution,[],[f96,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f96,plain,(
    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f95,f65])).

fof(f95,plain,(
    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f94,f36])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f93,f34])).

fof(f93,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f42,f35])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:50:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (22373)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (22370)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (22385)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (22373)Refutation not found, incomplete strategy% (22373)------------------------------
% 0.20/0.48  % (22373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22373)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (22373)Memory used [KB]: 10618
% 0.20/0.48  % (22373)Time elapsed: 0.058 s
% 0.20/0.48  % (22373)------------------------------
% 0.20/0.48  % (22373)------------------------------
% 0.20/0.48  % (22370)Refutation not found, incomplete strategy% (22370)------------------------------
% 0.20/0.48  % (22370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22385)Refutation not found, incomplete strategy% (22385)------------------------------
% 0.20/0.48  % (22385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22385)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (22385)Memory used [KB]: 6140
% 0.20/0.48  % (22385)Time elapsed: 0.069 s
% 0.20/0.48  % (22385)------------------------------
% 0.20/0.48  % (22385)------------------------------
% 0.20/0.48  % (22387)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (22387)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f105,f34])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f13])).
% 0.20/0.48  fof(f13,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.20/0.48    inference(negated_conjecture,[],[f12])).
% 0.20/0.48  fof(f12,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f104,f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f103,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f102,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0] : (~v1_xboole_0(sK3(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v4_pre_topc(X1,X0) & v3_pre_topc(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_tops_1)).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    v1_xboole_0(sK3(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f98,f92])).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    v1_xboole_0(k2_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f79,f91])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ~r2_hidden(sK1,k2_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f90,f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f74,f36])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.20/0.48    inference(resolution,[],[f46,f35])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(k2_struct_0(X0),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~r2_hidden(sK1,k2_struct_0(sK0))),
% 0.20/0.48    inference(subsumption_resolution,[],[f89,f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f76,f36])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.20/0.48    inference(resolution,[],[f47,f35])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~r2_hidden(sK1,k2_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f66,f60])).
% 0.20/0.48  fof(f60,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(forward_demodulation,[],[f38,f37])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.48  fof(f66,plain,(
% 0.20/0.48    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3)) )),
% 0.20/0.48    inference(backward_demodulation,[],[f63,f65])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f39,f61])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    l1_struct_0(sK0)),
% 0.20/0.48    inference(resolution,[],[f40,f36])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f56,f62])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(superposition,[],[f48,f53])).
% 0.20/0.48  fof(f53,plain,(
% 0.20/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3)) )),
% 0.20/0.48    inference(forward_demodulation,[],[f30,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    k1_xboole_0 = sK2),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | r2_hidden(X3,sK2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    v1_xboole_0(k2_struct_0(sK0)) | r2_hidden(sK1,k2_struct_0(sK0))),
% 0.20/0.48    inference(resolution,[],[f49,f71])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.48    inference(backward_demodulation,[],[f33,f65])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.48    inference(cnf_transformation,[],[f15])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    inference(flattening,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ~v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(sK3(sK0))),
% 0.20/0.48    inference(resolution,[],[f96,f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.20/0.48  fof(f96,plain,(
% 0.20/0.48    m1_subset_1(sK3(sK0),k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.48    inference(forward_demodulation,[],[f95,f65])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f94,f36])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(subsumption_resolution,[],[f93,f34])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | m1_subset_1(sK3(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(resolution,[],[f42,f35])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f20])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (22387)------------------------------
% 0.20/0.48  % (22387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (22387)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (22387)Memory used [KB]: 1663
% 0.20/0.48  % (22387)Time elapsed: 0.074 s
% 0.20/0.48  % (22387)------------------------------
% 0.20/0.48  % (22387)------------------------------
% 0.20/0.48  % (22370)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (22369)Success in time 0.128 s
%------------------------------------------------------------------------------
