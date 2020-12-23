%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:21 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 132 expanded)
%              Number of leaves         :   11 (  27 expanded)
%              Depth                    :   14
%              Number of atoms          :  166 ( 691 expanded)
%              Number of equality atoms :   17 (  69 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f82,plain,(
    $false ),
    inference(subsumption_resolution,[],[f81,f32])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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

fof(f81,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f80,f55])).

fof(f55,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f38,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f80,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f79,f78])).

fof(f78,plain,(
    v1_xboole_0(k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f71,f77])).

fof(f77,plain,(
    ~ r2_hidden(sK1,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f76,f69])).

fof(f69,plain,(
    v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f68,f34])).

fof(f68,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f41,f33])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f41,plain,(
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

fof(f76,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f75,f67])).

fof(f67,plain,(
    v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f66,f34])).

fof(f66,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f40,f33])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f75,plain,
    ( ~ v3_pre_topc(k2_struct_0(sK0),sK0)
    | ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | ~ r2_hidden(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f60,f54])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f36,f35])).

fof(f35,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f60,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(backward_demodulation,[],[f57,f59])).

fof(f59,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f37,f55])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f57,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(subsumption_resolution,[],[f50,f56])).

fof(f56,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f42,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
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

fof(f42,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f50,plain,(
    ! [X3] :
      ( r2_hidden(X3,k1_xboole_0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3) ) ),
    inference(forward_demodulation,[],[f28,f30])).

fof(f30,plain,(
    k1_xboole_0 = sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ v4_pre_topc(X3,sK0)
      | ~ r2_hidden(sK1,X3)
      | r2_hidden(X3,sK2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f71,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | r2_hidden(sK1,k2_struct_0(sK0)) ),
    inference(resolution,[],[f43,f65])).

fof(f65,plain,(
    m1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f31,f59])).

fof(f31,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f79,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f39,f59])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:49:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.48  % (20369)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.23/0.49  % (20369)Refutation not found, incomplete strategy% (20369)------------------------------
% 0.23/0.49  % (20369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (20377)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.23/0.49  % (20369)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.49  
% 0.23/0.49  % (20369)Memory used [KB]: 6140
% 0.23/0.49  % (20369)Time elapsed: 0.069 s
% 0.23/0.49  % (20369)------------------------------
% 0.23/0.49  % (20369)------------------------------
% 0.23/0.50  % (20384)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.23/0.50  % (20384)Refutation not found, incomplete strategy% (20384)------------------------------
% 0.23/0.50  % (20384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (20384)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (20384)Memory used [KB]: 6140
% 0.23/0.50  % (20384)Time elapsed: 0.037 s
% 0.23/0.50  % (20384)------------------------------
% 0.23/0.50  % (20384)------------------------------
% 0.23/0.50  % (20386)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.23/0.50  % (20386)Refutation found. Thanks to Tanya!
% 0.23/0.50  % SZS status Theorem for theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f82,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(subsumption_resolution,[],[f81,f32])).
% 0.23/0.50  fof(f32,plain,(
% 0.23/0.50    ~v2_struct_0(sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f14])).
% 0.23/0.50  fof(f14,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (? [X2] : (k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.23/0.50    inference(flattening,[],[f13])).
% 0.23/0.50  fof(f13,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (? [X2] : ((k1_xboole_0 = X2 & ! [X3] : ((r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f12])).
% 0.23/0.50  fof(f12,negated_conjecture,(
% 0.23/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.23/0.50    inference(negated_conjecture,[],[f11])).
% 0.23/0.50  fof(f11,conjecture,(
% 0.23/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => ~(k1_xboole_0 = X2 & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X3,X2) <=> (r2_hidden(X1,X3) & v4_pre_topc(X3,X0) & v3_pre_topc(X3,X0))))))))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_connsp_2)).
% 0.23/0.50  fof(f81,plain,(
% 0.23/0.50    v2_struct_0(sK0)),
% 0.23/0.50    inference(subsumption_resolution,[],[f80,f55])).
% 0.23/0.50  fof(f55,plain,(
% 0.23/0.50    l1_struct_0(sK0)),
% 0.23/0.50    inference(resolution,[],[f38,f34])).
% 0.23/0.50  fof(f34,plain,(
% 0.23/0.50    l1_pre_topc(sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f14])).
% 0.23/0.50  fof(f38,plain,(
% 0.23/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f16])).
% 0.23/0.50  fof(f16,plain,(
% 0.23/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f7])).
% 0.23/0.50  fof(f7,axiom,(
% 0.23/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.23/0.50  fof(f80,plain,(
% 0.23/0.50    ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.23/0.50    inference(subsumption_resolution,[],[f79,f78])).
% 0.23/0.50  fof(f78,plain,(
% 0.23/0.50    v1_xboole_0(k2_struct_0(sK0))),
% 0.23/0.50    inference(subsumption_resolution,[],[f71,f77])).
% 0.23/0.50  fof(f77,plain,(
% 0.23/0.50    ~r2_hidden(sK1,k2_struct_0(sK0))),
% 0.23/0.50    inference(subsumption_resolution,[],[f76,f69])).
% 0.23/0.50  fof(f69,plain,(
% 0.23/0.50    v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.23/0.50    inference(subsumption_resolution,[],[f68,f34])).
% 0.23/0.50  fof(f68,plain,(
% 0.23/0.50    ~l1_pre_topc(sK0) | v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.23/0.50    inference(resolution,[],[f41,f33])).
% 0.23/0.50  fof(f33,plain,(
% 0.23/0.50    v2_pre_topc(sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f14])).
% 0.23/0.50  fof(f41,plain,(
% 0.23/0.50    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(k2_struct_0(X0),X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f22])).
% 0.23/0.50  fof(f22,plain,(
% 0.23/0.50    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.50    inference(flattening,[],[f21])).
% 0.23/0.50  fof(f21,plain,(
% 0.23/0.50    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f9])).
% 0.23/0.50  fof(f9,axiom,(
% 0.23/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.23/0.50  fof(f76,plain,(
% 0.23/0.50    ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~r2_hidden(sK1,k2_struct_0(sK0))),
% 0.23/0.50    inference(subsumption_resolution,[],[f75,f67])).
% 0.23/0.50  fof(f67,plain,(
% 0.23/0.50    v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.23/0.50    inference(subsumption_resolution,[],[f66,f34])).
% 0.23/0.50  fof(f66,plain,(
% 0.23/0.50    ~l1_pre_topc(sK0) | v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.23/0.50    inference(resolution,[],[f40,f33])).
% 0.23/0.50  fof(f40,plain,(
% 0.23/0.50    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f20])).
% 0.23/0.50  fof(f20,plain,(
% 0.23/0.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.23/0.50    inference(flattening,[],[f19])).
% 0.23/0.50  fof(f19,plain,(
% 0.23/0.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f10])).
% 0.23/0.50  fof(f10,axiom,(
% 0.23/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.23/0.50  fof(f75,plain,(
% 0.23/0.50    ~v3_pre_topc(k2_struct_0(sK0),sK0) | ~v4_pre_topc(k2_struct_0(sK0),sK0) | ~r2_hidden(sK1,k2_struct_0(sK0))),
% 0.23/0.50    inference(resolution,[],[f60,f54])).
% 0.23/0.50  fof(f54,plain,(
% 0.23/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.23/0.50    inference(forward_demodulation,[],[f36,f35])).
% 0.23/0.50  fof(f35,plain,(
% 0.23/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.23/0.50    inference(cnf_transformation,[],[f3])).
% 0.23/0.50  fof(f3,axiom,(
% 0.23/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.23/0.50  fof(f36,plain,(
% 0.23/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f4])).
% 0.23/0.50  fof(f4,axiom,(
% 0.23/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.23/0.50  fof(f60,plain,(
% 0.23/0.50    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3)) )),
% 0.23/0.50    inference(backward_demodulation,[],[f57,f59])).
% 0.23/0.50  fof(f59,plain,(
% 0.23/0.50    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.23/0.50    inference(resolution,[],[f37,f55])).
% 0.23/0.50  fof(f37,plain,(
% 0.23/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f15])).
% 0.23/0.50  fof(f15,plain,(
% 0.23/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f6])).
% 0.23/0.50  fof(f6,axiom,(
% 0.23/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.23/0.50  fof(f57,plain,(
% 0.23/0.50    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3)) )),
% 0.23/0.50    inference(subsumption_resolution,[],[f50,f56])).
% 0.23/0.50  fof(f56,plain,(
% 0.23/0.50    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.23/0.50    inference(superposition,[],[f42,f47])).
% 0.23/0.50  fof(f47,plain,(
% 0.23/0.50    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.23/0.50    inference(equality_resolution,[],[f46])).
% 0.23/0.50  fof(f46,plain,(
% 0.23/0.50    ( ! [X0,X1] : (k1_xboole_0 != X1 | k2_zfmisc_1(X0,X1) = k1_xboole_0) )),
% 0.23/0.50    inference(cnf_transformation,[],[f1])).
% 0.23/0.50  fof(f1,axiom,(
% 0.23/0.50    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.23/0.50  fof(f42,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.23/0.50    inference(cnf_transformation,[],[f2])).
% 0.23/0.50  fof(f2,axiom,(
% 0.23/0.50    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.23/0.50  fof(f50,plain,(
% 0.23/0.50    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3)) )),
% 0.23/0.50    inference(forward_demodulation,[],[f28,f30])).
% 0.23/0.50  fof(f30,plain,(
% 0.23/0.50    k1_xboole_0 = sK2),
% 0.23/0.50    inference(cnf_transformation,[],[f14])).
% 0.23/0.50  fof(f28,plain,(
% 0.23/0.50    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~v4_pre_topc(X3,sK0) | ~r2_hidden(sK1,X3) | r2_hidden(X3,sK2)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f14])).
% 0.23/0.50  fof(f71,plain,(
% 0.23/0.50    v1_xboole_0(k2_struct_0(sK0)) | r2_hidden(sK1,k2_struct_0(sK0))),
% 0.23/0.50    inference(resolution,[],[f43,f65])).
% 0.23/0.50  fof(f65,plain,(
% 0.23/0.50    m1_subset_1(sK1,k2_struct_0(sK0))),
% 0.23/0.50    inference(backward_demodulation,[],[f31,f59])).
% 0.23/0.50  fof(f31,plain,(
% 0.23/0.50    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.23/0.50    inference(cnf_transformation,[],[f14])).
% 0.23/0.50  fof(f43,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f24])).
% 0.23/0.50  fof(f24,plain,(
% 0.23/0.50    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.23/0.50    inference(flattening,[],[f23])).
% 0.23/0.50  fof(f23,plain,(
% 0.23/0.50    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.23/0.50    inference(ennf_transformation,[],[f5])).
% 0.23/0.50  fof(f5,axiom,(
% 0.23/0.50    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.23/0.50  fof(f79,plain,(
% 0.23/0.50    ~v1_xboole_0(k2_struct_0(sK0)) | ~l1_struct_0(sK0) | v2_struct_0(sK0)),
% 0.23/0.50    inference(superposition,[],[f39,f59])).
% 0.23/0.50  fof(f39,plain,(
% 0.23/0.50    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f18])).
% 0.23/0.50  fof(f18,plain,(
% 0.23/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.23/0.50    inference(flattening,[],[f17])).
% 0.23/0.50  fof(f17,plain,(
% 0.23/0.50    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f8])).
% 0.23/0.50  fof(f8,axiom,(
% 0.23/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.23/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.23/0.50  % SZS output end Proof for theBenchmark
% 0.23/0.50  % (20386)------------------------------
% 0.23/0.50  % (20386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (20386)Termination reason: Refutation
% 0.23/0.50  
% 0.23/0.50  % (20386)Memory used [KB]: 1663
% 0.23/0.50  % (20386)Time elapsed: 0.083 s
% 0.23/0.50  % (20386)------------------------------
% 0.23/0.50  % (20386)------------------------------
% 0.23/0.50  % (20368)Success in time 0.132 s
%------------------------------------------------------------------------------
