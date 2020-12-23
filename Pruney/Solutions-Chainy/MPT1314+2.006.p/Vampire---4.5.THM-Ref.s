%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 378 expanded)
%              Number of leaves         :   11 (  76 expanded)
%              Depth                    :   20
%              Number of atoms          :  162 (1471 expanded)
%              Number of equality atoms :   28 ( 231 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f843,plain,(
    $false ),
    inference(subsumption_resolution,[],[f842,f45])).

fof(f45,plain,(
    ~ v3_pre_topc(sK1,sK2) ),
    inference(backward_demodulation,[],[f25,f24])).

fof(f24,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v3_pre_topc(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              & v3_pre_topc(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v3_pre_topc(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                     => ( X1 = X3
                       => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f25,plain,(
    ~ v3_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f842,plain,(
    v3_pre_topc(sK1,sK2) ),
    inference(forward_demodulation,[],[f841,f91])).

fof(f91,plain,(
    sK1 = k3_xboole_0(sK1,k2_struct_0(sK2)) ),
    inference(resolution,[],[f86,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f86,plain,(
    r1_tarski(sK1,k2_struct_0(sK2)) ),
    inference(resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f68,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(backward_demodulation,[],[f46,f67])).

fof(f67,plain,(
    u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(resolution,[],[f66,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f66,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f60,f31])).

fof(f31,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

% (6706)Refutation not found, incomplete strategy% (6706)------------------------------
% (6706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (6706)Termination reason: Refutation not found, incomplete strategy

% (6706)Memory used [KB]: 10618
% (6706)Time elapsed: 0.094 s
% (6706)------------------------------
% (6706)------------------------------
fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f60,plain,(
    l1_pre_topc(sK2) ),
    inference(subsumption_resolution,[],[f59,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f26,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f26,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(forward_demodulation,[],[f23,f24])).

% (6709)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f23,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2))) ),
    inference(cnf_transformation,[],[f14])).

fof(f841,plain,(
    v3_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2) ),
    inference(forward_demodulation,[],[f840,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f840,plain,(
    v3_pre_topc(k3_xboole_0(k2_struct_0(sK2),sK1),sK2) ),
    inference(forward_demodulation,[],[f839,f87])).

fof(f87,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(k2_struct_0(sK2),sK1,X0) ),
    inference(backward_demodulation,[],[f83,f84])).

fof(f84,plain,(
    ! [X1] : k3_xboole_0(X1,sK1) = k9_subset_1(k2_struct_0(sK2),X1,sK1) ),
    inference(resolution,[],[f68,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f83,plain,(
    ! [X0] : k9_subset_1(k2_struct_0(sK2),X0,sK1) = k9_subset_1(k2_struct_0(sK2),sK1,X0) ),
    inference(resolution,[],[f68,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f839,plain,(
    v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2) ),
    inference(subsumption_resolution,[],[f838,f54])).

fof(f54,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f28,f53])).

fof(f53,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f52,f30])).

fof(f52,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f29,f31])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f838,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2) ),
    inference(forward_demodulation,[],[f837,f53])).

fof(f837,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2) ),
    inference(subsumption_resolution,[],[f836,f156])).

fof(f156,plain,(
    ! [X3] : m1_subset_1(k3_xboole_0(X3,sK1),k1_zfmisc_1(k2_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f155,f68])).

fof(f155,plain,(
    ! [X3] :
      ( m1_subset_1(k3_xboole_0(X3,sK1),k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2))) ) ),
    inference(superposition,[],[f41,f84])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f836,plain,
    ( ~ m1_subset_1(k3_xboole_0(k2_struct_0(sK2),sK1),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2) ),
    inference(forward_demodulation,[],[f835,f87])).

fof(f835,plain,
    ( ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2) ),
    inference(subsumption_resolution,[],[f834,f26])).

fof(f834,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2) ),
    inference(subsumption_resolution,[],[f829,f29])).

fof(f829,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2) ),
    inference(resolution,[],[f107,f27])).

fof(f27,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f107,plain,(
    ! [X14,X13] :
      ( ~ v3_pre_topc(X13,X14)
      | ~ l1_pre_topc(X14)
      | ~ m1_pre_topc(sK2,X14)
      | ~ m1_subset_1(k9_subset_1(k2_struct_0(sK2),X13,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2)))
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X14)))
      | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X13,k2_struct_0(sK2)),sK2) ) ),
    inference(superposition,[],[f44,f67])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
      | v3_pre_topc(X2,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => ( v3_pre_topc(X2,X1)
              <=> ? [X3] :
                    ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                    & v3_pre_topc(X3,X0)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:25:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (6720)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (6710)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (6712)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (6718)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (6705)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (6717)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (6716)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (6711)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (6721)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (6723)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (6722)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (6725)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (6706)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (6707)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (6718)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f843,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f842,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ~v3_pre_topc(sK1,sK2)),
% 0.21/0.51    inference(backward_demodulation,[],[f25,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    sK1 = sK3),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~v3_pre_topc(X3,X2) & X1 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : ((~v3_pre_topc(X3,X2) & X1 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) & v3_pre_topc(X1,X0)) & m1_pre_topc(X2,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.21/0.51    inference(negated_conjecture,[],[f11])).
% 0.21/0.51  fof(f11,conjecture,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ~v3_pre_topc(sK3,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f842,plain,(
% 0.21/0.51    v3_pre_topc(sK1,sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f841,f91])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    sK1 = k3_xboole_0(sK1,k2_struct_0(sK2))),
% 0.21/0.51    inference(resolution,[],[f86,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    r1_tarski(sK1,k2_struct_0(sK2))),
% 0.21/0.51    inference(resolution,[],[f68,f40])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.51  fof(f68,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))),
% 0.21/0.51    inference(backward_demodulation,[],[f46,f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    u1_struct_0(sK2) = k2_struct_0(sK2)),
% 0.21/0.51    inference(resolution,[],[f66,f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    l1_struct_0(sK2)),
% 0.21/0.51    inference(resolution,[],[f60,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  % (6706)Refutation not found, incomplete strategy% (6706)------------------------------
% 0.21/0.51  % (6706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6706)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (6706)Memory used [KB]: 10618
% 0.21/0.51  % (6706)Time elapsed: 0.094 s
% 0.21/0.51  % (6706)------------------------------
% 0.21/0.51  % (6706)------------------------------
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    l1_pre_topc(sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f59,f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    l1_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.21/0.51    inference(resolution,[],[f26,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    m1_pre_topc(sK2,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.51    inference(forward_demodulation,[],[f23,f24])).
% 0.21/0.51  % (6709)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK2)))),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f841,plain,(
% 0.21/0.51    v3_pre_topc(k3_xboole_0(sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f840,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.51  fof(f840,plain,(
% 0.21/0.51    v3_pre_topc(k3_xboole_0(k2_struct_0(sK2),sK1),sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f839,f87])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X0] : (k3_xboole_0(X0,sK1) = k9_subset_1(k2_struct_0(sK2),sK1,X0)) )),
% 0.21/0.51    inference(backward_demodulation,[],[f83,f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X1] : (k3_xboole_0(X1,sK1) = k9_subset_1(k2_struct_0(sK2),X1,sK1)) )),
% 0.21/0.51    inference(resolution,[],[f68,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0] : (k9_subset_1(k2_struct_0(sK2),X0,sK1) = k9_subset_1(k2_struct_0(sK2),sK1,X0)) )),
% 0.21/0.51    inference(resolution,[],[f68,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).
% 0.21/0.51  fof(f839,plain,(
% 0.21/0.51    v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f838,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.51    inference(backward_demodulation,[],[f28,f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f52,f30])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    l1_struct_0(sK0)),
% 0.21/0.51    inference(resolution,[],[f29,f31])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f838,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f837,f53])).
% 0.21/0.51  fof(f837,plain,(
% 0.21/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f836,f156])).
% 0.21/0.51  fof(f156,plain,(
% 0.21/0.51    ( ! [X3] : (m1_subset_1(k3_xboole_0(X3,sK1),k1_zfmisc_1(k2_struct_0(sK2)))) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f155,f68])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X3] : (m1_subset_1(k3_xboole_0(X3,sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK2)))) )),
% 0.21/0.51    inference(superposition,[],[f41,f84])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.51  fof(f836,plain,(
% 0.21/0.51    ~m1_subset_1(k3_xboole_0(k2_struct_0(sK2),sK1),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.51    inference(forward_demodulation,[],[f835,f87])).
% 0.21/0.51  fof(f835,plain,(
% 0.21/0.51    ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f834,f26])).
% 0.21/0.51  fof(f834,plain,(
% 0.21/0.51    ~m1_pre_topc(sK2,sK0) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.51    inference(subsumption_resolution,[],[f829,f29])).
% 0.21/0.51  fof(f829,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),sK1,k2_struct_0(sK2)),sK2)),
% 0.21/0.51    inference(resolution,[],[f107,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    v3_pre_topc(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f14])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    ( ! [X14,X13] : (~v3_pre_topc(X13,X14) | ~l1_pre_topc(X14) | ~m1_pre_topc(sK2,X14) | ~m1_subset_1(k9_subset_1(k2_struct_0(sK2),X13,k2_struct_0(sK2)),k1_zfmisc_1(k2_struct_0(sK2))) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X14))) | v3_pre_topc(k9_subset_1(k2_struct_0(sK2),X13,k2_struct_0(sK2)),sK2)) )),
% 0.21/0.51    inference(superposition,[],[f44,f67])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | v3_pre_topc(k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)),X1)) )),
% 0.21/0.51    inference(equality_resolution,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | v3_pre_topc(X2,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X2,X1) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_tops_2)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (6718)------------------------------
% 0.21/0.51  % (6718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6718)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (6718)Memory used [KB]: 2046
% 0.21/0.51  % (6718)Time elapsed: 0.076 s
% 0.21/0.51  % (6718)------------------------------
% 0.21/0.51  % (6718)------------------------------
% 0.21/0.51  % (6708)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (6704)Success in time 0.148 s
%------------------------------------------------------------------------------
