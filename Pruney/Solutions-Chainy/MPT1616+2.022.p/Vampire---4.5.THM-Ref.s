%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 165 expanded)
%              Number of leaves         :   10 (  34 expanded)
%              Depth                    :   23
%              Number of atoms          :  200 ( 535 expanded)
%              Number of equality atoms :   23 (  69 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f319,plain,(
    $false ),
    inference(resolution,[],[f317,f162])).

fof(f162,plain,(
    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f160,f71])).

fof(f71,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f160,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_pre_topc(sK0),X0)
      | r2_hidden(u1_struct_0(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f159,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f159,plain,(
    ! [X0] :
      ( ~ r1_tarski(u1_pre_topc(sK0),X0)
      | ~ l1_pre_topc(sK0)
      | r2_hidden(u1_struct_0(sK0),X0) ) ),
    inference(resolution,[],[f88,f27])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f88,plain,(
    ! [X4,X3] :
      ( ~ v2_pre_topc(X3)
      | ~ r1_tarski(u1_pre_topc(X3),X4)
      | ~ l1_pre_topc(X3)
      | r2_hidden(u1_struct_0(X3),X4) ) ),
    inference(resolution,[],[f59,f50])).

fof(f50,plain,(
    ! [X0] :
      ( r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( ! [X2] :
                  ( r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))
                  | ~ r2_hidden(X2,u1_pre_topc(X0))
                  | ~ r2_hidden(X1,u1_pre_topc(X0))
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          & ! [X3] :
              ( r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0))
              | ~ r1_tarski(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X3] :
              ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X3,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    inference(rectify,[],[f9])).

% (31001)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% (30993)Refutation not found, incomplete strategy% (30993)------------------------------
% (30993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (30993)Termination reason: Refutation not found, incomplete strategy

% (30993)Memory used [KB]: 10618
% (30993)Time elapsed: 0.182 s
% (30993)------------------------------
% (30993)------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_pre_topc(X0)
      <=> ( ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r2_hidden(X2,u1_pre_topc(X0))
                      & r2_hidden(X1,u1_pre_topc(X0)) )
                   => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) ) ) )
          & ! [X1] :
              ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
             => ( r1_tarski(X1,u1_pre_topc(X0))
               => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) )
          & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f317,plain,(
    ! [X0] : ~ r2_hidden(X0,u1_pre_topc(sK0)) ),
    inference(resolution,[],[f312,f71])).

fof(f312,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,u1_pre_topc(sK0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f301,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f301,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0)))
      | ~ r2_hidden(X1,X0) ) ),
    inference(resolution,[],[f297,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f297,plain,(
    v1_xboole_0(u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f296,f29])).

fof(f29,plain,(
    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f296,plain,
    ( v1_xboole_0(u1_pre_topc(sK0))
    | u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f295,f162])).

fof(f295,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | v1_xboole_0(u1_pre_topc(sK0))
    | u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(superposition,[],[f31,f234])).

fof(f234,plain,(
    u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) ),
    inference(resolution,[],[f233,f195])).

fof(f195,plain,
    ( ~ r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) ),
    inference(resolution,[],[f192,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f192,plain,(
    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))
    | r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) ),
    inference(resolution,[],[f173,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f173,plain,(
    ! [X0] :
      ( r2_hidden(sK4(u1_struct_0(sK0),X0),k3_tarski(u1_pre_topc(sK0)))
      | r1_tarski(u1_struct_0(sK0),X0) ) ),
    inference(resolution,[],[f164,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f164,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k3_tarski(u1_pre_topc(sK0))) ) ),
    inference(resolution,[],[f162,f73])).

fof(f73,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X2,X3)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f233,plain,(
    r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f229])).

fof(f229,plain,
    ( r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))
    | r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f223,f61])).

fof(f223,plain,(
    ! [X1] :
      ( r2_hidden(sK4(k3_tarski(u1_pre_topc(sK0)),X1),u1_struct_0(sK0))
      | r1_tarski(k3_tarski(u1_pre_topc(sK0)),X1) ) ),
    inference(resolution,[],[f221,f60])).

fof(f221,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_tarski(u1_pre_topc(sK0)))
      | r2_hidden(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k3_tarski(u1_pre_topc(sK0)))
      | r2_hidden(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k3_tarski(u1_pre_topc(sK0))) ) ),
    inference(resolution,[],[f215,f75])).

fof(f75,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,sK6(X0,X2))
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,sK6(X0,X2))
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f215,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK6(u1_pre_topc(sK0),X0))
      | ~ r2_hidden(X0,k3_tarski(u1_pre_topc(sK0)))
      | r2_hidden(X1,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f212,f30])).

fof(f30,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f212,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k3_tarski(u1_pre_topc(sK0)))
      | ~ r2_hidden(X1,sK6(u1_pre_topc(sK0),X0))
      | r2_hidden(X1,k3_tarski(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(resolution,[],[f210,f73])).

fof(f210,plain,(
    ! [X2] :
      ( r2_hidden(sK6(u1_pre_topc(sK0),X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,k3_tarski(u1_pre_topc(sK0))) ) ),
    inference(resolution,[],[f89,f82])).

fof(f82,plain,(
    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f81,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f81,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f32,f28])).

fof(f32,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r2_hidden(sK6(X1,X0),X2)
      | ~ r2_hidden(X0,k3_tarski(X1)) ) ),
    inference(resolution,[],[f74,f59])).

fof(f74,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK6(X0,X2),X0)
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f31,plain,(
    ! [X0] :
      ( ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:50:20 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (30983)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (30995)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (30984)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (30991)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.55  % (31011)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.22/0.55  % (31000)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (31010)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.55  % (30998)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.55  % (31000)Refutation not found, incomplete strategy% (31000)------------------------------
% 0.22/0.55  % (31000)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31000)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31000)Memory used [KB]: 10618
% 0.22/0.55  % (31000)Time elapsed: 0.129 s
% 0.22/0.55  % (31000)------------------------------
% 0.22/0.55  % (31000)------------------------------
% 0.22/0.56  % (30990)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.56  % (30986)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.56  % (31002)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.56  % (31005)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.57  % (31006)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.57  % (30987)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.57  % (30988)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (30989)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.57  % (30992)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.57  % (31012)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.57  % (31003)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.57  % (30994)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.57  % (30985)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  % (30994)Refutation not found, incomplete strategy% (30994)------------------------------
% 0.22/0.57  % (30994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (30994)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (30994)Memory used [KB]: 10618
% 0.22/0.57  % (30994)Time elapsed: 0.153 s
% 0.22/0.57  % (30994)------------------------------
% 0.22/0.57  % (30994)------------------------------
% 0.22/0.57  % (30999)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.57  % (31004)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.58  % (31007)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.58  % (31003)Refutation not found, incomplete strategy% (31003)------------------------------
% 0.22/0.58  % (31003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (31003)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (31003)Memory used [KB]: 10746
% 0.22/0.58  % (31003)Time elapsed: 0.114 s
% 0.22/0.58  % (31003)------------------------------
% 0.22/0.58  % (31003)------------------------------
% 0.22/0.58  % (30996)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.58  % (31004)Refutation not found, incomplete strategy% (31004)------------------------------
% 0.22/0.58  % (31004)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (31004)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (31004)Memory used [KB]: 1791
% 0.22/0.58  % (31004)Time elapsed: 0.162 s
% 0.22/0.58  % (31004)------------------------------
% 0.22/0.58  % (31004)------------------------------
% 0.22/0.58  % (30997)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.59  % (31008)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.59  % (30989)Refutation found. Thanks to Tanya!
% 0.22/0.59  % SZS status Theorem for theBenchmark
% 0.22/0.59  % (30993)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.60  % (30985)Refutation not found, incomplete strategy% (30985)------------------------------
% 0.22/0.60  % (30985)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (30985)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (30985)Memory used [KB]: 10746
% 0.22/0.60  % (30985)Time elapsed: 0.179 s
% 0.22/0.60  % (30985)------------------------------
% 0.22/0.60  % (30985)------------------------------
% 0.22/0.60  % (31009)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.22/0.60  % SZS output start Proof for theBenchmark
% 0.22/0.60  fof(f319,plain,(
% 0.22/0.60    $false),
% 0.22/0.60    inference(resolution,[],[f317,f162])).
% 0.22/0.60  fof(f162,plain,(
% 0.22/0.60    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 0.22/0.60    inference(resolution,[],[f160,f71])).
% 0.22/0.60  fof(f71,plain,(
% 0.22/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.60    inference(equality_resolution,[],[f57])).
% 0.22/0.60  fof(f57,plain,(
% 0.22/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.60    inference(cnf_transformation,[],[f2])).
% 0.22/0.60  fof(f2,axiom,(
% 0.22/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.60  fof(f160,plain,(
% 0.22/0.60    ( ! [X0] : (~r1_tarski(u1_pre_topc(sK0),X0) | r2_hidden(u1_struct_0(sK0),X0)) )),
% 0.22/0.60    inference(subsumption_resolution,[],[f159,f28])).
% 0.22/0.60  fof(f28,plain,(
% 0.22/0.60    l1_pre_topc(sK0)),
% 0.22/0.60    inference(cnf_transformation,[],[f17])).
% 0.22/0.60  fof(f17,plain,(
% 0.22/0.60    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.60    inference(flattening,[],[f16])).
% 0.22/0.60  fof(f16,plain,(
% 0.22/0.60    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.60    inference(ennf_transformation,[],[f15])).
% 0.22/0.60  fof(f15,plain,(
% 0.22/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.22/0.60    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.60  fof(f13,negated_conjecture,(
% 0.22/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.22/0.60    inference(negated_conjecture,[],[f12])).
% 0.22/0.60  fof(f12,conjecture,(
% 0.22/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.22/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).
% 0.22/0.60  fof(f159,plain,(
% 0.22/0.60    ( ! [X0] : (~r1_tarski(u1_pre_topc(sK0),X0) | ~l1_pre_topc(sK0) | r2_hidden(u1_struct_0(sK0),X0)) )),
% 0.22/0.60    inference(resolution,[],[f88,f27])).
% 0.22/0.60  fof(f27,plain,(
% 0.22/0.60    v2_pre_topc(sK0)),
% 0.22/0.60    inference(cnf_transformation,[],[f17])).
% 0.22/0.60  fof(f88,plain,(
% 0.22/0.60    ( ! [X4,X3] : (~v2_pre_topc(X3) | ~r1_tarski(u1_pre_topc(X3),X4) | ~l1_pre_topc(X3) | r2_hidden(u1_struct_0(X3),X4)) )),
% 0.22/0.60    inference(resolution,[],[f59,f50])).
% 0.22/0.60  fof(f50,plain,(
% 0.22/0.60    ( ! [X0] : (r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.22/0.60    inference(cnf_transformation,[],[f22])).
% 0.22/0.60  fof(f22,plain,(
% 0.22/0.60    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.60    inference(flattening,[],[f21])).
% 0.22/0.60  fof(f21,plain,(
% 0.22/0.60    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.60    inference(ennf_transformation,[],[f14])).
% 0.22/0.60  fof(f14,plain,(
% 0.22/0.60    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.60    inference(rectify,[],[f9])).
% 0.22/0.60  % (31001)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.22/0.60  % (30993)Refutation not found, incomplete strategy% (30993)------------------------------
% 0.22/0.60  % (30993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.60  % (30993)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.60  
% 0.22/0.60  % (30993)Memory used [KB]: 10618
% 0.22/0.60  % (30993)Time elapsed: 0.182 s
% 0.22/0.60  % (30993)------------------------------
% 0.22/0.60  % (30993)------------------------------
% 0.22/0.61  fof(f9,axiom,(
% 0.22/0.61    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.22/0.61  fof(f59,plain,(
% 0.22/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f25])).
% 0.22/0.61  fof(f25,plain,(
% 0.22/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.61    inference(ennf_transformation,[],[f1])).
% 0.22/0.61  fof(f1,axiom,(
% 0.22/0.61    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.61  fof(f317,plain,(
% 0.22/0.61    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0))) )),
% 0.22/0.61    inference(resolution,[],[f312,f71])).
% 0.22/0.61  fof(f312,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~r1_tarski(X1,u1_pre_topc(sK0)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.61    inference(resolution,[],[f301,f68])).
% 0.22/0.61  fof(f68,plain,(
% 0.22/0.61    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f7])).
% 0.22/0.61  fof(f7,axiom,(
% 0.22/0.61    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.61  fof(f301,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_pre_topc(sK0))) | ~r2_hidden(X1,X0)) )),
% 0.22/0.61    inference(resolution,[],[f297,f70])).
% 0.22/0.61  fof(f70,plain,(
% 0.22/0.61    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f26])).
% 0.22/0.61  fof(f26,plain,(
% 0.22/0.61    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.61    inference(ennf_transformation,[],[f8])).
% 0.22/0.61  fof(f8,axiom,(
% 0.22/0.61    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.61  fof(f297,plain,(
% 0.22/0.61    v1_xboole_0(u1_pre_topc(sK0))),
% 0.22/0.61    inference(subsumption_resolution,[],[f296,f29])).
% 0.22/0.61  fof(f29,plain,(
% 0.22/0.61    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.22/0.61    inference(cnf_transformation,[],[f17])).
% 0.22/0.61  fof(f296,plain,(
% 0.22/0.61    v1_xboole_0(u1_pre_topc(sK0)) | u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.22/0.61    inference(subsumption_resolution,[],[f295,f162])).
% 0.22/0.61  fof(f295,plain,(
% 0.22/0.61    ~r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | v1_xboole_0(u1_pre_topc(sK0)) | u1_struct_0(sK0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.22/0.61    inference(superposition,[],[f31,f234])).
% 0.22/0.61  fof(f234,plain,(
% 0.22/0.61    u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))),
% 0.22/0.61    inference(resolution,[],[f233,f195])).
% 0.22/0.61  fof(f195,plain,(
% 0.22/0.61    ~r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) | u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))),
% 0.22/0.61    inference(resolution,[],[f192,f58])).
% 0.22/0.61  fof(f58,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.61    inference(cnf_transformation,[],[f2])).
% 0.22/0.61  fof(f192,plain,(
% 0.22/0.61    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))),
% 0.22/0.61    inference(duplicate_literal_removal,[],[f188])).
% 0.22/0.61  fof(f188,plain,(
% 0.22/0.61    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) | r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))),
% 0.22/0.61    inference(resolution,[],[f173,f61])).
% 0.22/0.61  fof(f61,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f25])).
% 0.22/0.61  fof(f173,plain,(
% 0.22/0.61    ( ! [X0] : (r2_hidden(sK4(u1_struct_0(sK0),X0),k3_tarski(u1_pre_topc(sK0))) | r1_tarski(u1_struct_0(sK0),X0)) )),
% 0.22/0.61    inference(resolution,[],[f164,f60])).
% 0.22/0.61  fof(f60,plain,(
% 0.22/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f25])).
% 0.22/0.61  fof(f164,plain,(
% 0.22/0.61    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK0)) | r2_hidden(X0,k3_tarski(u1_pre_topc(sK0)))) )),
% 0.22/0.61    inference(resolution,[],[f162,f73])).
% 0.22/0.61  fof(f73,plain,(
% 0.22/0.61    ( ! [X2,X0,X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3) | r2_hidden(X2,k3_tarski(X0))) )),
% 0.22/0.61    inference(equality_resolution,[],[f67])).
% 0.22/0.61  fof(f67,plain,(
% 0.22/0.61    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 0.22/0.61    inference(cnf_transformation,[],[f3])).
% 0.22/0.61  fof(f3,axiom,(
% 0.22/0.61    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 0.22/0.61  fof(f233,plain,(
% 0.22/0.61    r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))),
% 0.22/0.61    inference(duplicate_literal_removal,[],[f229])).
% 0.22/0.61  fof(f229,plain,(
% 0.22/0.61    r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) | r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))),
% 0.22/0.61    inference(resolution,[],[f223,f61])).
% 0.22/0.61  fof(f223,plain,(
% 0.22/0.61    ( ! [X1] : (r2_hidden(sK4(k3_tarski(u1_pre_topc(sK0)),X1),u1_struct_0(sK0)) | r1_tarski(k3_tarski(u1_pre_topc(sK0)),X1)) )),
% 0.22/0.61    inference(resolution,[],[f221,f60])).
% 0.22/0.61  fof(f221,plain,(
% 0.22/0.61    ( ! [X0] : (~r2_hidden(X0,k3_tarski(u1_pre_topc(sK0))) | r2_hidden(X0,u1_struct_0(sK0))) )),
% 0.22/0.61    inference(duplicate_literal_removal,[],[f216])).
% 0.22/0.61  fof(f216,plain,(
% 0.22/0.61    ( ! [X0] : (~r2_hidden(X0,k3_tarski(u1_pre_topc(sK0))) | r2_hidden(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_tarski(u1_pre_topc(sK0)))) )),
% 0.22/0.61    inference(resolution,[],[f215,f75])).
% 0.22/0.61  fof(f75,plain,(
% 0.22/0.61    ( ! [X2,X0] : (r2_hidden(X2,sK6(X0,X2)) | ~r2_hidden(X2,k3_tarski(X0))) )),
% 0.22/0.61    inference(equality_resolution,[],[f65])).
% 0.22/0.61  fof(f65,plain,(
% 0.22/0.61    ( ! [X2,X0,X1] : (r2_hidden(X2,sK6(X0,X2)) | ~r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 0.22/0.61    inference(cnf_transformation,[],[f3])).
% 0.22/0.61  fof(f215,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~r2_hidden(X1,sK6(u1_pre_topc(sK0),X0)) | ~r2_hidden(X0,k3_tarski(u1_pre_topc(sK0))) | r2_hidden(X1,u1_struct_0(sK0))) )),
% 0.22/0.61    inference(forward_demodulation,[],[f212,f30])).
% 0.22/0.61  fof(f30,plain,(
% 0.22/0.61    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.22/0.61    inference(cnf_transformation,[],[f4])).
% 0.22/0.61  fof(f4,axiom,(
% 0.22/0.61    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.22/0.61  fof(f212,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~r2_hidden(X0,k3_tarski(u1_pre_topc(sK0))) | ~r2_hidden(X1,sK6(u1_pre_topc(sK0),X0)) | r2_hidden(X1,k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.22/0.61    inference(resolution,[],[f210,f73])).
% 0.22/0.61  fof(f210,plain,(
% 0.22/0.61    ( ! [X2] : (r2_hidden(sK6(u1_pre_topc(sK0),X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,k3_tarski(u1_pre_topc(sK0)))) )),
% 0.22/0.61    inference(resolution,[],[f89,f82])).
% 0.22/0.61  fof(f82,plain,(
% 0.22/0.61    r1_tarski(u1_pre_topc(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.61    inference(resolution,[],[f81,f69])).
% 0.22/0.61  fof(f69,plain,(
% 0.22/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.61    inference(cnf_transformation,[],[f7])).
% 0.22/0.61  fof(f81,plain,(
% 0.22/0.61    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.61    inference(resolution,[],[f32,f28])).
% 0.22/0.61  fof(f32,plain,(
% 0.22/0.61    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.22/0.61    inference(cnf_transformation,[],[f20])).
% 0.22/0.61  fof(f20,plain,(
% 0.22/0.61    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f10])).
% 0.22/0.61  fof(f10,axiom,(
% 0.22/0.61    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.61  fof(f89,plain,(
% 0.22/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r2_hidden(sK6(X1,X0),X2) | ~r2_hidden(X0,k3_tarski(X1))) )),
% 0.22/0.61    inference(resolution,[],[f74,f59])).
% 0.22/0.61  fof(f74,plain,(
% 0.22/0.61    ( ! [X2,X0] : (r2_hidden(sK6(X0,X2),X0) | ~r2_hidden(X2,k3_tarski(X0))) )),
% 0.22/0.61    inference(equality_resolution,[],[f66])).
% 0.22/0.61  fof(f66,plain,(
% 0.22/0.61    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X2),X0) | ~r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 0.22/0.61    inference(cnf_transformation,[],[f3])).
% 0.22/0.61  fof(f31,plain,(
% 0.22/0.61    ( ! [X0] : (~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))) )),
% 0.22/0.61    inference(cnf_transformation,[],[f19])).
% 0.22/0.61  fof(f19,plain,(
% 0.22/0.61    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.22/0.61    inference(flattening,[],[f18])).
% 0.22/0.61  fof(f18,plain,(
% 0.22/0.61    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.22/0.61    inference(ennf_transformation,[],[f11])).
% 0.22/0.61  fof(f11,axiom,(
% 0.22/0.61    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.22/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.22/0.61  % SZS output end Proof for theBenchmark
% 0.22/0.61  % (30989)------------------------------
% 0.22/0.61  % (30989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.61  % (30989)Termination reason: Refutation
% 0.22/0.61  
% 0.22/0.61  % (30989)Memory used [KB]: 6396
% 0.22/0.61  % (30989)Time elapsed: 0.155 s
% 0.22/0.61  % (30989)------------------------------
% 0.22/0.61  % (30989)------------------------------
% 1.89/0.61  % (30982)Success in time 0.236 s
%------------------------------------------------------------------------------
