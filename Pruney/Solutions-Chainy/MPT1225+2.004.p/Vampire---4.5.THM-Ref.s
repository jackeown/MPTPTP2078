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
% DateTime   : Thu Dec  3 13:10:54 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   71 (1004 expanded)
%              Number of leaves         :   10 ( 233 expanded)
%              Depth                    :   18
%              Number of atoms          :  161 (3444 expanded)
%              Number of equality atoms :   33 ( 787 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f702,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f362,f339,f151])).

fof(f151,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X8,k9_subset_1(X7,X6,X7))
      | sP5(X8,X7,X6) ) ),
    inference(superposition,[],[f54,f92])).

fof(f92,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k9_subset_1(X1,X0,X1) ),
    inference(unit_resulting_resolution,[],[f56,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f39,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f56,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f52,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f52,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f44,f30])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f339,plain,(
    r2_hidden(sK3(k9_subset_1(sK2,sK1,sK2),sK1),k9_subset_1(sK2,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f331,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f331,plain,(
    ~ r1_tarski(k9_subset_1(sK2,sK1,sK2),sK1) ),
    inference(unit_resulting_resolution,[],[f295,f325,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f34,f35])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f325,plain,(
    ~ r2_hidden(sK3(k9_subset_1(sK2,sK1,sK2),u1_struct_0(sK0)),sK1) ),
    inference(unit_resulting_resolution,[],[f58,f304,f34])).

fof(f304,plain,(
    ~ r2_hidden(sK3(k9_subset_1(sK2,sK1,sK2),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f295,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f24,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f24,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              & v4_pre_topc(X2,X0)
              & v4_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v4_pre_topc(X1,X0) )
                 => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v4_pre_topc(X1,X0) )
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_1)).

fof(f295,plain,(
    ~ r1_tarski(k9_subset_1(sK2,sK1,sK2),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f25,f285,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f26,f37])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f285,plain,(
    ~ r1_tarski(k9_subset_1(sK2,sK1,sK2),k2_pre_topc(sK0,k9_subset_1(sK2,sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f135,f258,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f258,plain,(
    r1_tarski(k2_pre_topc(sK0,k9_subset_1(sK2,sK1,sK2)),k9_subset_1(sK2,sK1,sK2)) ),
    inference(forward_demodulation,[],[f257,f98])).

fof(f98,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2) ),
    inference(forward_demodulation,[],[f90,f92])).

% (17187)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (17178)Refutation not found, incomplete strategy% (17178)------------------------------
% (17178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17178)Termination reason: Refutation not found, incomplete strategy

% (17178)Memory used [KB]: 10618
% (17178)Time elapsed: 0.145 s
% (17178)------------------------------
% (17178)------------------------------
% (17180)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% (17171)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% (17171)Refutation not found, incomplete strategy% (17171)------------------------------
% (17171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17171)Termination reason: Refutation not found, incomplete strategy

% (17171)Memory used [KB]: 10874
% (17171)Time elapsed: 0.161 s
% (17171)------------------------------
% (17171)------------------------------
fof(f90,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2)) ),
    inference(unit_resulting_resolution,[],[f20,f47])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f257,plain,(
    r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(sK2,sK1,sK2)) ),
    inference(forward_demodulation,[],[f256,f120])).

fof(f120,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f25,f21,f24,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f21,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f256,plain,(
    r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(sK2,k2_pre_topc(sK0,sK1),sK2)) ),
    inference(forward_demodulation,[],[f255,f98])).

fof(f255,plain,(
    r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK2)) ),
    inference(forward_demodulation,[],[f220,f119])).

fof(f119,plain,(
    sK2 = k2_pre_topc(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f25,f22,f20,f28])).

fof(f22,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f220,plain,(
    r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(unit_resulting_resolution,[],[f25,f20,f24,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

fof(f135,plain,(
    k9_subset_1(sK2,sK1,sK2) != k2_pre_topc(sK0,k9_subset_1(sK2,sK1,sK2)) ),
    inference(forward_demodulation,[],[f133,f98])).

fof(f133,plain,(
    k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_pre_topc(sK0,k9_subset_1(sK2,sK1,sK2)) ),
    inference(backward_demodulation,[],[f126,f119])).

fof(f126,plain,(
    k2_pre_topc(sK0,k9_subset_1(sK2,sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)) ),
    inference(backward_demodulation,[],[f99,f120])).

fof(f99,plain,(
    k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k9_subset_1(sK2,sK1,sK2)) ),
    inference(backward_demodulation,[],[f23,f98])).

fof(f23,plain,(
    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f25,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f362,plain,(
    ! [X0] : ~ sP5(sK3(k9_subset_1(sK2,sK1,sK2),sK1),X0,sK1) ),
    inference(unit_resulting_resolution,[],[f338,f41])).

fof(f41,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f338,plain,(
    ~ r2_hidden(sK3(k9_subset_1(sK2,sK1,sK2),sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f331,f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:53:45 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (17185)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (17176)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (17166)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.53  % (17168)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.27/0.53  % (17175)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.54  % (17162)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.54  % (17161)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.27/0.54  % (17189)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.27/0.54  % (17167)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.27/0.54  % (17188)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.27/0.54  % (17165)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.54  % (17164)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.54  % (17190)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.38/0.55  % (17163)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.55  % (17178)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.38/0.55  % (17186)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.55  % (17174)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.55  % (17179)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.38/0.55  % (17163)Refutation not found, incomplete strategy% (17163)------------------------------
% 1.38/0.55  % (17163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (17163)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (17163)Memory used [KB]: 10746
% 1.38/0.55  % (17163)Time elapsed: 0.135 s
% 1.38/0.55  % (17163)------------------------------
% 1.38/0.55  % (17163)------------------------------
% 1.38/0.55  % (17177)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.55  % (17181)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.38/0.55  % (17182)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.55  % (17169)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.55  % (17183)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.56  % (17170)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.38/0.56  % (17169)Refutation not found, incomplete strategy% (17169)------------------------------
% 1.38/0.56  % (17169)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (17169)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (17169)Memory used [KB]: 10746
% 1.38/0.56  % (17169)Time elapsed: 0.149 s
% 1.38/0.56  % (17169)------------------------------
% 1.38/0.56  % (17169)------------------------------
% 1.38/0.56  % (17172)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.56  % (17173)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.56  % (17184)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.38/0.56  % (17172)Refutation not found, incomplete strategy% (17172)------------------------------
% 1.38/0.56  % (17172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (17172)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (17172)Memory used [KB]: 10746
% 1.38/0.56  % (17172)Time elapsed: 0.150 s
% 1.38/0.56  % (17172)------------------------------
% 1.38/0.56  % (17172)------------------------------
% 1.38/0.56  % (17185)Refutation found. Thanks to Tanya!
% 1.38/0.56  % SZS status Theorem for theBenchmark
% 1.38/0.56  % SZS output start Proof for theBenchmark
% 1.38/0.56  fof(f702,plain,(
% 1.38/0.56    $false),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f362,f339,f151])).
% 1.38/0.56  fof(f151,plain,(
% 1.38/0.56    ( ! [X6,X8,X7] : (~r2_hidden(X8,k9_subset_1(X7,X6,X7)) | sP5(X8,X7,X6)) )),
% 1.38/0.56    inference(superposition,[],[f54,f92])).
% 1.38/0.56  fof(f92,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k9_subset_1(X1,X0,X1)) )),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f56,f47])).
% 1.38/0.56  fof(f47,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.38/0.56    inference(definition_unfolding,[],[f39,f30])).
% 1.38/0.56  fof(f30,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f5])).
% 1.38/0.56  fof(f5,axiom,(
% 1.38/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.38/0.56  fof(f39,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f19])).
% 1.38/0.56  fof(f19,plain,(
% 1.38/0.56    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.38/0.56    inference(ennf_transformation,[],[f4])).
% 1.38/0.56  fof(f4,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.38/0.56  fof(f56,plain,(
% 1.38/0.56    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f52,f37])).
% 1.38/0.56  fof(f37,plain,(
% 1.38/0.56    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f6])).
% 1.38/0.56  fof(f6,axiom,(
% 1.38/0.56    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.38/0.56  fof(f52,plain,(
% 1.38/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.38/0.56    inference(equality_resolution,[],[f32])).
% 1.38/0.56  fof(f32,plain,(
% 1.38/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.38/0.56    inference(cnf_transformation,[],[f3])).
% 1.38/0.56  fof(f3,axiom,(
% 1.38/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.38/0.56  fof(f54,plain,(
% 1.38/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | sP5(X3,X1,X0)) )),
% 1.38/0.56    inference(equality_resolution,[],[f50])).
% 1.38/0.56  fof(f50,plain,(
% 1.38/0.56    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.38/0.56    inference(definition_unfolding,[],[f44,f30])).
% 1.38/0.56  fof(f44,plain,(
% 1.38/0.56    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.38/0.56    inference(cnf_transformation,[],[f2])).
% 1.38/0.56  fof(f2,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.38/0.56  fof(f339,plain,(
% 1.38/0.56    r2_hidden(sK3(k9_subset_1(sK2,sK1,sK2),sK1),k9_subset_1(sK2,sK1,sK2))),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f331,f35])).
% 1.38/0.56  fof(f35,plain,(
% 1.38/0.56    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f18])).
% 1.38/0.56  fof(f18,plain,(
% 1.38/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.38/0.56    inference(ennf_transformation,[],[f1])).
% 1.38/0.56  fof(f1,axiom,(
% 1.38/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.38/0.56  fof(f331,plain,(
% 1.38/0.56    ~r1_tarski(k9_subset_1(sK2,sK1,sK2),sK1)),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f295,f325,f72])).
% 1.38/0.56  fof(f72,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 1.38/0.56    inference(resolution,[],[f34,f35])).
% 1.38/0.56  fof(f34,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f18])).
% 1.38/0.56  fof(f325,plain,(
% 1.38/0.56    ~r2_hidden(sK3(k9_subset_1(sK2,sK1,sK2),u1_struct_0(sK0)),sK1)),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f58,f304,f34])).
% 1.38/0.56  fof(f304,plain,(
% 1.38/0.56    ~r2_hidden(sK3(k9_subset_1(sK2,sK1,sK2),u1_struct_0(sK0)),u1_struct_0(sK0))),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f295,f36])).
% 1.38/0.56  fof(f36,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f18])).
% 1.38/0.56  fof(f58,plain,(
% 1.38/0.56    r1_tarski(sK1,u1_struct_0(sK0))),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f24,f38])).
% 1.38/0.56  fof(f38,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f6])).
% 1.38/0.56  fof(f24,plain,(
% 1.38/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.38/0.56    inference(cnf_transformation,[],[f13])).
% 1.38/0.56  fof(f13,plain,(
% 1.38/0.56    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.38/0.56    inference(flattening,[],[f12])).
% 1.38/0.56  fof(f12,plain,(
% 1.38/0.56    ? [X0] : (? [X1] : (? [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) & (v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.38/0.56    inference(ennf_transformation,[],[f11])).
% 1.38/0.56  fof(f11,negated_conjecture,(
% 1.38/0.56    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 1.38/0.56    inference(negated_conjecture,[],[f10])).
% 1.38/0.56  fof(f10,conjecture,(
% 1.38/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v4_pre_topc(X2,X0) & v4_pre_topc(X1,X0)) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_tops_1)).
% 1.38/0.56  fof(f295,plain,(
% 1.38/0.56    ~r1_tarski(k9_subset_1(sK2,sK1,sK2),u1_struct_0(sK0))),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f25,f285,f88])).
% 1.38/0.56  fof(f88,plain,(
% 1.38/0.56    ( ! [X0,X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0) | ~r1_tarski(X1,u1_struct_0(X0))) )),
% 1.38/0.56    inference(resolution,[],[f26,f37])).
% 1.38/0.56  fof(f26,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(X1,k2_pre_topc(X0,X1))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f14])).
% 1.38/0.56  fof(f14,plain,(
% 1.38/0.56    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.56    inference(ennf_transformation,[],[f7])).
% 1.38/0.56  fof(f7,axiom,(
% 1.38/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 1.38/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 1.38/0.56  fof(f285,plain,(
% 1.38/0.56    ~r1_tarski(k9_subset_1(sK2,sK1,sK2),k2_pre_topc(sK0,k9_subset_1(sK2,sK1,sK2)))),
% 1.38/0.56    inference(unit_resulting_resolution,[],[f135,f258,f33])).
% 1.38/0.56  fof(f33,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.38/0.56    inference(cnf_transformation,[],[f3])).
% 1.38/0.56  fof(f258,plain,(
% 1.38/0.56    r1_tarski(k2_pre_topc(sK0,k9_subset_1(sK2,sK1,sK2)),k9_subset_1(sK2,sK1,sK2))),
% 1.38/0.56    inference(forward_demodulation,[],[f257,f98])).
% 1.38/0.56  fof(f98,plain,(
% 1.38/0.56    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k9_subset_1(sK2,X0,sK2)) )),
% 1.38/0.56    inference(forward_demodulation,[],[f90,f92])).
% 1.38/0.56  % (17187)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.56  % (17178)Refutation not found, incomplete strategy% (17178)------------------------------
% 1.38/0.56  % (17178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (17178)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (17178)Memory used [KB]: 10618
% 1.38/0.56  % (17178)Time elapsed: 0.145 s
% 1.38/0.56  % (17178)------------------------------
% 1.38/0.56  % (17178)------------------------------
% 1.38/0.57  % (17180)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.57  % (17171)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.38/0.58  % (17171)Refutation not found, incomplete strategy% (17171)------------------------------
% 1.38/0.58  % (17171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (17171)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.58  
% 1.38/0.58  % (17171)Memory used [KB]: 10874
% 1.38/0.58  % (17171)Time elapsed: 0.161 s
% 1.38/0.58  % (17171)------------------------------
% 1.38/0.58  % (17171)------------------------------
% 1.38/0.58  fof(f90,plain,(
% 1.38/0.58    ( ! [X0] : (k9_subset_1(u1_struct_0(sK0),X0,sK2) = k1_setfam_1(k2_tarski(X0,sK2))) )),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f20,f47])).
% 1.38/0.58  fof(f20,plain,(
% 1.38/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.38/0.58    inference(cnf_transformation,[],[f13])).
% 1.38/0.58  fof(f257,plain,(
% 1.38/0.58    r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(sK2,sK1,sK2))),
% 1.38/0.58    inference(forward_demodulation,[],[f256,f120])).
% 1.38/0.58  fof(f120,plain,(
% 1.38/0.58    sK1 = k2_pre_topc(sK0,sK1)),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f25,f21,f24,f28])).
% 1.38/0.58  fof(f28,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 1.38/0.58    inference(cnf_transformation,[],[f16])).
% 1.38/0.58  fof(f16,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.58    inference(flattening,[],[f15])).
% 1.38/0.58  fof(f15,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.58    inference(ennf_transformation,[],[f9])).
% 1.38/0.58  fof(f9,axiom,(
% 1.38/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 1.38/0.58  fof(f21,plain,(
% 1.38/0.58    v4_pre_topc(sK1,sK0)),
% 1.38/0.58    inference(cnf_transformation,[],[f13])).
% 1.38/0.58  fof(f256,plain,(
% 1.38/0.58    r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(sK2,k2_pre_topc(sK0,sK1),sK2))),
% 1.38/0.58    inference(forward_demodulation,[],[f255,f98])).
% 1.38/0.58  fof(f255,plain,(
% 1.38/0.58    r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK2))),
% 1.38/0.58    inference(forward_demodulation,[],[f220,f119])).
% 1.38/0.58  fof(f119,plain,(
% 1.38/0.58    sK2 = k2_pre_topc(sK0,sK2)),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f25,f22,f20,f28])).
% 1.38/0.58  fof(f22,plain,(
% 1.38/0.58    v4_pre_topc(sK2,sK0)),
% 1.38/0.58    inference(cnf_transformation,[],[f13])).
% 1.38/0.58  fof(f220,plain,(
% 1.38/0.58    r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f25,f20,f24,f29])).
% 1.38/0.58  fof(f29,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f17])).
% 1.38/0.58  fof(f17,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.38/0.58    inference(ennf_transformation,[],[f8])).
% 1.38/0.58  fof(f8,axiom,(
% 1.38/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).
% 1.38/0.58  fof(f135,plain,(
% 1.38/0.58    k9_subset_1(sK2,sK1,sK2) != k2_pre_topc(sK0,k9_subset_1(sK2,sK1,sK2))),
% 1.38/0.58    inference(forward_demodulation,[],[f133,f98])).
% 1.38/0.58  fof(f133,plain,(
% 1.38/0.58    k9_subset_1(u1_struct_0(sK0),sK1,sK2) != k2_pre_topc(sK0,k9_subset_1(sK2,sK1,sK2))),
% 1.38/0.58    inference(backward_demodulation,[],[f126,f119])).
% 1.38/0.58  fof(f126,plain,(
% 1.38/0.58    k2_pre_topc(sK0,k9_subset_1(sK2,sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))),
% 1.38/0.58    inference(backward_demodulation,[],[f99,f120])).
% 1.38/0.58  fof(f99,plain,(
% 1.38/0.58    k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)) != k2_pre_topc(sK0,k9_subset_1(sK2,sK1,sK2))),
% 1.38/0.58    inference(backward_demodulation,[],[f23,f98])).
% 1.38/0.58  fof(f23,plain,(
% 1.38/0.58    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))),
% 1.38/0.58    inference(cnf_transformation,[],[f13])).
% 1.38/0.58  fof(f25,plain,(
% 1.38/0.58    l1_pre_topc(sK0)),
% 1.38/0.58    inference(cnf_transformation,[],[f13])).
% 1.38/0.58  fof(f362,plain,(
% 1.38/0.58    ( ! [X0] : (~sP5(sK3(k9_subset_1(sK2,sK1,sK2),sK1),X0,sK1)) )),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f338,f41])).
% 1.38/0.58  fof(f41,plain,(
% 1.38/0.58    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f2])).
% 1.38/0.58  fof(f338,plain,(
% 1.38/0.58    ~r2_hidden(sK3(k9_subset_1(sK2,sK1,sK2),sK1),sK1)),
% 1.38/0.58    inference(unit_resulting_resolution,[],[f331,f36])).
% 1.38/0.58  % SZS output end Proof for theBenchmark
% 1.38/0.58  % (17185)------------------------------
% 1.38/0.58  % (17185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (17185)Termination reason: Refutation
% 1.38/0.58  
% 1.38/0.58  % (17185)Memory used [KB]: 6652
% 1.38/0.58  % (17185)Time elapsed: 0.090 s
% 1.38/0.58  % (17185)------------------------------
% 1.38/0.58  % (17185)------------------------------
% 1.38/0.58  % (17182)Refutation not found, incomplete strategy% (17182)------------------------------
% 1.38/0.58  % (17182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (17182)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.58  
% 1.38/0.58  % (17182)Memory used [KB]: 1791
% 1.38/0.58  % (17182)Time elapsed: 0.170 s
% 1.38/0.58  % (17182)------------------------------
% 1.38/0.58  % (17182)------------------------------
% 1.38/0.58  % (17160)Success in time 0.209 s
%------------------------------------------------------------------------------
