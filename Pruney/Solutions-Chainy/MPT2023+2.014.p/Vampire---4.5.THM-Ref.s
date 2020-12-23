%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:08 EST 2020

% Result     : Theorem 1.37s
% Output     : Refutation 1.37s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 506 expanded)
%              Number of leaves         :    9 ( 103 expanded)
%              Depth                    :   10
%              Number of atoms          :  220 (2848 expanded)
%              Number of equality atoms :   11 (  68 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f386,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f199,f222,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f222,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f30,f29,f28,f27,f154,f207,f219])).

fof(f219,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f33,f61])).

fof(f61,plain,(
    ~ r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

% (32290)Termination reason: Refutation not found, incomplete strategy

% (32290)Memory used [KB]: 10746
% (32290)Time elapsed: 0.143 s
% (32290)------------------------------
% (32290)------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f52,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f25,plain,(
    ~ m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                   => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))
                 => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_9)).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ v3_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
              <=> ( v3_pre_topc(X2,X0)
                  & r2_hidden(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f207,plain,(
    v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0) ),
    inference(unit_resulting_resolution,[],[f29,f30,f140,f141,f193,f192,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f43,f38])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).

fof(f192,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f187,f113])).

fof(f113,plain,(
    sK2 = sK4(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f26,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | sK4(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => ? [X3] :
                  ( v3_pre_topc(X3,X0)
                  & r2_hidden(X1,X3)
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).

fof(f26,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f187,plain,(
    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f28,f29,f30,f27,f26,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f193,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f186,f112])).

fof(f112,plain,(
    sK3 = sK4(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f24,f35])).

fof(f24,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f186,plain,(
    m1_subset_1(sK4(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f28,f29,f30,f27,f24,f34])).

fof(f141,plain,(
    v3_pre_topc(sK3,sK0) ),
    inference(forward_demodulation,[],[f136,f112])).

fof(f136,plain,(
    v3_pre_topc(sK4(sK0,sK1,sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f24,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v3_pre_topc(sK4(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f140,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(forward_demodulation,[],[f137,f113])).

fof(f137,plain,(
    v3_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f26,f37])).

fof(f154,plain,(
    r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f132,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f38])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f132,plain,(
    sP6(sK1,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f122,f123,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f123,plain,(
    r2_hidden(sK1,sK3) ),
    inference(forward_demodulation,[],[f118,f112])).

fof(f118,plain,(
    r2_hidden(sK1,sK4(sK0,sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f24,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,sK4(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f122,plain,(
    r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f119,f113])).

fof(f119,plain,(
    r2_hidden(sK1,sK4(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f26,f36])).

fof(f27,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f199,plain,(
    ! [X0] : r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f195,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f38])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f195,plain,(
    r1_tarski(sK2,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f192,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:19:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (32280)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.52  % (32296)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.25/0.52  % (32288)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.25/0.53  % (32285)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.53  % (32288)Refutation not found, incomplete strategy% (32288)------------------------------
% 1.25/0.53  % (32288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (32304)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.37/0.54  % (32288)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (32288)Memory used [KB]: 10746
% 1.37/0.54  % (32288)Time elapsed: 0.109 s
% 1.37/0.54  % (32288)------------------------------
% 1.37/0.54  % (32288)------------------------------
% 1.37/0.54  % (32282)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.54  % (32284)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.37/0.54  % (32303)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.54  % (32295)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.54  % (32282)Refutation not found, incomplete strategy% (32282)------------------------------
% 1.37/0.54  % (32282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.54  % (32282)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.54  
% 1.37/0.54  % (32282)Memory used [KB]: 10746
% 1.37/0.54  % (32282)Time elapsed: 0.125 s
% 1.37/0.54  % (32282)------------------------------
% 1.37/0.54  % (32282)------------------------------
% 1.37/0.55  % (32286)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.37/0.55  % (32294)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.37/0.55  % (32306)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.37/0.55  % (32309)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.55  % (32308)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.55  % (32298)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.55  % (32307)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.55  % (32293)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.37/0.56  % (32281)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.37/0.56  % (32300)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.37/0.56  % (32290)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.56  % (32287)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.37/0.56  % (32292)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.56  % (32290)Refutation not found, incomplete strategy% (32290)------------------------------
% 1.37/0.56  % (32290)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.56  % (32301)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.37/0.56  % (32302)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.37/0.57  % (32289)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.57  % (32304)Refutation found. Thanks to Tanya!
% 1.37/0.57  % SZS status Theorem for theBenchmark
% 1.37/0.57  % (32283)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.57  % (32297)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.37/0.58  % (32305)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.37/0.58  % SZS output start Proof for theBenchmark
% 1.37/0.58  fof(f386,plain,(
% 1.37/0.58    $false),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f199,f222,f40])).
% 1.37/0.58  fof(f40,plain,(
% 1.37/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f5])).
% 1.37/0.58  fof(f5,axiom,(
% 1.37/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.37/0.58  fof(f222,plain,(
% 1.37/0.58    ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.58    inference(global_subsumption,[],[f30,f29,f28,f27,f154,f207,f219])).
% 1.37/0.58  fof(f219,plain,(
% 1.37/0.58    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) | ~v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0) | v2_struct_0(sK0)),
% 1.37/0.58    inference(resolution,[],[f33,f61])).
% 1.37/0.58  fof(f61,plain,(
% 1.37/0.58    ~r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f52,f39])).
% 1.37/0.58  fof(f39,plain,(
% 1.37/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f18])).
% 1.37/0.58  fof(f18,plain,(
% 1.37/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.37/0.58    inference(ennf_transformation,[],[f4])).
% 1.37/0.58  % (32290)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.58  
% 1.37/0.58  % (32290)Memory used [KB]: 10746
% 1.37/0.58  % (32290)Time elapsed: 0.143 s
% 1.37/0.58  % (32290)------------------------------
% 1.37/0.58  % (32290)------------------------------
% 1.37/0.58  fof(f4,axiom,(
% 1.37/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.37/0.58  fof(f52,plain,(
% 1.37/0.58    ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.37/0.58    inference(definition_unfolding,[],[f25,f38])).
% 1.37/0.58  fof(f38,plain,(
% 1.37/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 1.37/0.58    inference(cnf_transformation,[],[f3])).
% 1.37/0.58  fof(f3,axiom,(
% 1.37/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.37/0.58  fof(f25,plain,(
% 1.37/0.58    ~m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.37/0.58    inference(cnf_transformation,[],[f13])).
% 1.37/0.58  fof(f13,plain,(
% 1.37/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.37/0.58    inference(flattening,[],[f12])).
% 1.37/0.58  fof(f12,plain,(
% 1.37/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.37/0.58    inference(ennf_transformation,[],[f11])).
% 1.37/0.58  fof(f11,negated_conjecture,(
% 1.37/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.37/0.58    inference(negated_conjecture,[],[f10])).
% 1.37/0.58  fof(f10,conjecture,(
% 1.37/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_9)).
% 1.37/0.58  fof(f33,plain,(
% 1.37/0.58    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~v3_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f15])).
% 1.37/0.58  fof(f15,plain,(
% 1.37/0.58    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.37/0.58    inference(flattening,[],[f14])).
% 1.37/0.58  fof(f14,plain,(
% 1.37/0.58    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.37/0.58    inference(ennf_transformation,[],[f9])).
% 1.37/0.58  fof(f9,axiom,(
% 1.37/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).
% 1.37/0.58  fof(f207,plain,(
% 1.37/0.58    v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0)),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f29,f30,f140,f141,f193,f192,f54])).
% 1.37/0.58  fof(f54,plain,(
% 1.37/0.58    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 1.37/0.58    inference(definition_unfolding,[],[f43,f38])).
% 1.37/0.58  fof(f43,plain,(
% 1.37/0.58    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k3_xboole_0(X1,X2),X0)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f21])).
% 1.37/0.58  fof(f21,plain,(
% 1.37/0.58    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.37/0.58    inference(flattening,[],[f20])).
% 1.37/0.58  fof(f20,plain,(
% 1.37/0.58    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.37/0.58    inference(ennf_transformation,[],[f7])).
% 1.37/0.58  fof(f7,axiom,(
% 1.37/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).
% 1.37/0.58  fof(f192,plain,(
% 1.37/0.58    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.58    inference(forward_demodulation,[],[f187,f113])).
% 1.37/0.58  fof(f113,plain,(
% 1.37/0.58    sK2 = sK4(sK0,sK1,sK2)),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f26,f35])).
% 1.37/0.58  fof(f35,plain,(
% 1.37/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | sK4(X0,X1,X2) = X2) )),
% 1.37/0.58    inference(cnf_transformation,[],[f17])).
% 1.37/0.58  fof(f17,plain,(
% 1.37/0.58    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.37/0.58    inference(flattening,[],[f16])).
% 1.37/0.58  fof(f16,plain,(
% 1.37/0.58    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.37/0.58    inference(ennf_transformation,[],[f8])).
% 1.37/0.58  fof(f8,axiom,(
% 1.37/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).
% 1.37/0.58  fof(f26,plain,(
% 1.37/0.58    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.37/0.58    inference(cnf_transformation,[],[f13])).
% 1.37/0.58  fof(f187,plain,(
% 1.37/0.58    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f28,f29,f30,f27,f26,f34])).
% 1.37/0.58  fof(f34,plain,(
% 1.37/0.58    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | v2_struct_0(X0)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f17])).
% 1.37/0.58  fof(f193,plain,(
% 1.37/0.58    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.58    inference(forward_demodulation,[],[f186,f112])).
% 1.37/0.58  fof(f112,plain,(
% 1.37/0.58    sK3 = sK4(sK0,sK1,sK3)),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f24,f35])).
% 1.37/0.58  fof(f24,plain,(
% 1.37/0.58    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.37/0.58    inference(cnf_transformation,[],[f13])).
% 1.37/0.58  fof(f186,plain,(
% 1.37/0.58    m1_subset_1(sK4(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f28,f29,f30,f27,f24,f34])).
% 1.37/0.58  fof(f141,plain,(
% 1.37/0.58    v3_pre_topc(sK3,sK0)),
% 1.37/0.58    inference(forward_demodulation,[],[f136,f112])).
% 1.37/0.58  fof(f136,plain,(
% 1.37/0.58    v3_pre_topc(sK4(sK0,sK1,sK3),sK0)),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f24,f37])).
% 1.37/0.58  fof(f37,plain,(
% 1.37/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | v3_pre_topc(sK4(X0,X1,X2),X0)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f17])).
% 1.37/0.58  fof(f140,plain,(
% 1.37/0.58    v3_pre_topc(sK2,sK0)),
% 1.37/0.58    inference(forward_demodulation,[],[f137,f113])).
% 1.37/0.58  fof(f137,plain,(
% 1.37/0.58    v3_pre_topc(sK4(sK0,sK1,sK2),sK0)),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f26,f37])).
% 1.37/0.58  fof(f154,plain,(
% 1.37/0.58    r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f132,f60])).
% 1.37/0.58  fof(f60,plain,(
% 1.37/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | ~sP6(X3,X1,X0)) )),
% 1.37/0.58    inference(equality_resolution,[],[f58])).
% 1.37/0.58  fof(f58,plain,(
% 1.37/0.58    ( ! [X2,X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 1.37/0.58    inference(definition_unfolding,[],[f48,f38])).
% 1.37/0.58  fof(f48,plain,(
% 1.37/0.58    ( ! [X2,X0,X3,X1] : (~sP6(X3,X1,X0) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 1.37/0.58    inference(cnf_transformation,[],[f1])).
% 1.37/0.58  fof(f1,axiom,(
% 1.37/0.58    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.37/0.58  fof(f132,plain,(
% 1.37/0.58    sP6(sK1,sK3,sK2)),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f122,f123,f45])).
% 1.37/0.58  fof(f45,plain,(
% 1.37/0.58    ( ! [X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f1])).
% 1.37/0.58  fof(f123,plain,(
% 1.37/0.58    r2_hidden(sK1,sK3)),
% 1.37/0.58    inference(forward_demodulation,[],[f118,f112])).
% 1.37/0.58  fof(f118,plain,(
% 1.37/0.58    r2_hidden(sK1,sK4(sK0,sK1,sK3))),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f24,f36])).
% 1.37/0.58  fof(f36,plain,(
% 1.37/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,sK4(X0,X1,X2))) )),
% 1.37/0.58    inference(cnf_transformation,[],[f17])).
% 1.37/0.58  fof(f122,plain,(
% 1.37/0.58    r2_hidden(sK1,sK2)),
% 1.37/0.58    inference(forward_demodulation,[],[f119,f113])).
% 1.37/0.58  fof(f119,plain,(
% 1.37/0.58    r2_hidden(sK1,sK4(sK0,sK1,sK2))),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f26,f36])).
% 1.37/0.58  fof(f27,plain,(
% 1.37/0.58    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.37/0.58    inference(cnf_transformation,[],[f13])).
% 1.37/0.58  fof(f28,plain,(
% 1.37/0.58    ~v2_struct_0(sK0)),
% 1.37/0.58    inference(cnf_transformation,[],[f13])).
% 1.37/0.58  fof(f29,plain,(
% 1.37/0.58    v2_pre_topc(sK0)),
% 1.37/0.58    inference(cnf_transformation,[],[f13])).
% 1.37/0.58  fof(f30,plain,(
% 1.37/0.58    l1_pre_topc(sK0)),
% 1.37/0.58    inference(cnf_transformation,[],[f13])).
% 1.37/0.58  fof(f199,plain,(
% 1.37/0.58    ( ! [X0] : (r1_tarski(k1_setfam_1(k2_tarski(sK2,X0)),u1_struct_0(sK0))) )),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f195,f53])).
% 1.37/0.58  fof(f53,plain,(
% 1.37/0.58    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 1.37/0.58    inference(definition_unfolding,[],[f42,f38])).
% 1.37/0.58  fof(f42,plain,(
% 1.37/0.58    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f19])).
% 1.37/0.58  fof(f19,plain,(
% 1.37/0.58    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.37/0.58    inference(ennf_transformation,[],[f2])).
% 1.37/0.58  fof(f2,axiom,(
% 1.37/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 1.37/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 1.37/0.58  fof(f195,plain,(
% 1.37/0.58    r1_tarski(sK2,u1_struct_0(sK0))),
% 1.37/0.58    inference(unit_resulting_resolution,[],[f192,f41])).
% 1.37/0.58  fof(f41,plain,(
% 1.37/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.37/0.58    inference(cnf_transformation,[],[f5])).
% 1.37/0.58  % SZS output end Proof for theBenchmark
% 1.37/0.58  % (32304)------------------------------
% 1.37/0.58  % (32304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.58  % (32304)Termination reason: Refutation
% 1.37/0.58  
% 1.37/0.58  % (32304)Memory used [KB]: 6524
% 1.37/0.58  % (32304)Time elapsed: 0.138 s
% 1.37/0.58  % (32304)------------------------------
% 1.37/0.58  % (32304)------------------------------
% 1.37/0.59  % (32279)Success in time 0.218 s
%------------------------------------------------------------------------------
