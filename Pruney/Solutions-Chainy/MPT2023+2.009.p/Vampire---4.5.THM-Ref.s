%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:07 EST 2020

% Result     : Theorem 2.93s
% Output     : Refutation 3.68s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 979 expanded)
%              Number of leaves         :   10 ( 200 expanded)
%              Depth                    :   12
%              Number of atoms          :  258 (5421 expanded)
%              Number of equality atoms :   13 ( 130 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (7196)Time limit reached!
% (7196)------------------------------
% (7196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7196)Termination reason: Time limit
% (7196)Termination phase: Saturation

% (7196)Memory used [KB]: 8315
% (7196)Time elapsed: 0.400 s
% (7196)------------------------------
% (7196)------------------------------
% (7258)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
fof(f2108,plain,(
    $false ),
    inference(global_subsumption,[],[f954,f2097])).

fof(f2097,plain,(
    ~ r2_hidden(sK5(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(sK0)),sK2) ),
    inference(unit_resulting_resolution,[],[f757,f482])).

fof(f482,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5(X0,u1_struct_0(sK0)),sK2)
      | r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f236,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f236,plain,(
    ! [X1] :
      ( r2_hidden(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK2) ) ),
    inference(resolution,[],[f230,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f230,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f224,f151])).

fof(f151,plain,(
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

fof(f27,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f224,plain,(
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

fof(f757,plain,(
    ~ r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f289,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f289,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f30,f29,f28,f27,f208,f260,f280])).

fof(f280,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f33,f71])).

fof(f71,plain,(
    ~ r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f54,f66,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f66,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f64,f43])).

fof(f64,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(duplicate_literal_removal,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( r1_tarski(X0,X0)
      | r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f42,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f54,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(definition_unfolding,[],[f25,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f25,plain,(
    ~ m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

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

fof(f260,plain,(
    v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0) ),
    inference(unit_resulting_resolution,[],[f29,f30,f194,f193,f230,f231,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f45,f38])).

fof(f45,plain,(
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

fof(f231,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f223,f150])).

fof(f150,plain,(
    sK3 = sK4(sK0,sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f24,f35])).

fof(f24,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f13])).

fof(f223,plain,(
    m1_subset_1(sK4(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f28,f29,f30,f27,f24,f34])).

fof(f193,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(forward_demodulation,[],[f189,f151])).

fof(f189,plain,(
    v3_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f26,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | v3_pre_topc(sK4(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f194,plain,(
    v3_pre_topc(sK3,sK0) ),
    inference(forward_demodulation,[],[f188,f150])).

fof(f188,plain,(
    v3_pre_topc(sK4(sK0,sK1,sK3),sK0) ),
    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f24,f37])).

fof(f208,plain,(
    r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f181,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f50,f38])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f181,plain,(
    sP7(sK1,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f162,f163,f47])).

fof(f47,plain,(
    ! [X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f163,plain,(
    r2_hidden(sK1,sK3) ),
    inference(forward_demodulation,[],[f157,f150])).

fof(f157,plain,(
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

fof(f162,plain,(
    r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f158,f151])).

fof(f158,plain,(
    r2_hidden(sK1,sK4(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f26,f36])).

fof(f954,plain,(
    r2_hidden(sK5(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(sK0)),sK2) ),
    inference(unit_resulting_resolution,[],[f757,f337])).

fof(f337,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK5(k1_setfam_1(k2_tarski(X3,X4)),X5),X3)
      | r1_tarski(k1_setfam_1(k2_tarski(X3,X4)),X5) ) ),
    inference(resolution,[],[f91,f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( sP7(sK5(k1_setfam_1(k2_tarski(X0,X1)),X2),X1,X0)
      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) ) ),
    inference(resolution,[],[f60,f41])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f51,f38])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:17:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (7195)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.55  % (7204)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (7196)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.56  % (7213)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.57  % (7202)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.57  % (7210)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.57  % (7205)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.58  % (7197)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.59  % (7194)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.59  % (7193)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.59  % (7214)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.59  % (7192)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.60  % (7202)Refutation not found, incomplete strategy% (7202)------------------------------
% 0.20/0.60  % (7202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (7202)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.60  % (7202)Memory used [KB]: 10746
% 0.20/0.60  % (7202)Time elapsed: 0.171 s
% 0.20/0.60  % (7202)------------------------------
% 0.20/0.60  % (7202)------------------------------
% 0.20/0.60  % (7206)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.60  % (7191)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.60  % (7211)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.60  % (7220)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.61  % (7219)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.61  % (7198)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.61  % (7207)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.61  % (7212)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.61  % (7209)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.61  % (7199)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.61  % (7215)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.62  % (7216)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.62  % (7203)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.62  % (7218)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.62  % (7208)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.63  % (7201)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.63  % (7200)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.94/0.64  % (7217)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 2.25/0.68  % (7201)Refutation not found, incomplete strategy% (7201)------------------------------
% 2.25/0.68  % (7201)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.25/0.68  % (7201)Termination reason: Refutation not found, incomplete strategy
% 2.25/0.68  
% 2.25/0.68  % (7201)Memory used [KB]: 10874
% 2.25/0.68  % (7201)Time elapsed: 0.227 s
% 2.25/0.68  % (7201)------------------------------
% 2.25/0.68  % (7201)------------------------------
% 2.93/0.83  % (7215)Refutation found. Thanks to Tanya!
% 2.93/0.83  % SZS status Theorem for theBenchmark
% 2.93/0.83  % SZS output start Proof for theBenchmark
% 2.93/0.83  % (7196)Time limit reached!
% 2.93/0.83  % (7196)------------------------------
% 2.93/0.83  % (7196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.93/0.83  % (7196)Termination reason: Time limit
% 2.93/0.83  % (7196)Termination phase: Saturation
% 2.93/0.83  
% 2.93/0.83  % (7196)Memory used [KB]: 8315
% 2.93/0.83  % (7196)Time elapsed: 0.400 s
% 2.93/0.83  % (7196)------------------------------
% 2.93/0.83  % (7196)------------------------------
% 3.68/0.85  % (7258)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.68/0.86  fof(f2108,plain,(
% 3.68/0.86    $false),
% 3.68/0.86    inference(global_subsumption,[],[f954,f2097])).
% 3.68/0.86  fof(f2097,plain,(
% 3.68/0.86    ~r2_hidden(sK5(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(sK0)),sK2)),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f757,f482])).
% 3.68/0.86  fof(f482,plain,(
% 3.68/0.86    ( ! [X0] : (~r2_hidden(sK5(X0,u1_struct_0(sK0)),sK2) | r1_tarski(X0,u1_struct_0(sK0))) )),
% 3.68/0.86    inference(resolution,[],[f236,f42])).
% 3.68/0.86  fof(f42,plain,(
% 3.68/0.86    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f19])).
% 3.68/0.86  fof(f19,plain,(
% 3.68/0.86    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.68/0.86    inference(ennf_transformation,[],[f1])).
% 3.68/0.86  fof(f1,axiom,(
% 3.68/0.86    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.68/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 3.68/0.86  fof(f236,plain,(
% 3.68/0.86    ( ! [X1] : (r2_hidden(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,sK2)) )),
% 3.68/0.86    inference(resolution,[],[f230,f39])).
% 3.68/0.86  fof(f39,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f18])).
% 3.68/0.86  fof(f18,plain,(
% 3.68/0.86    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.68/0.86    inference(ennf_transformation,[],[f3])).
% 3.68/0.86  fof(f3,axiom,(
% 3.68/0.86    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.68/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 3.68/0.86  fof(f230,plain,(
% 3.68/0.86    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.68/0.86    inference(forward_demodulation,[],[f224,f151])).
% 3.68/0.86  fof(f151,plain,(
% 3.68/0.86    sK2 = sK4(sK0,sK1,sK2)),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f26,f35])).
% 3.68/0.86  fof(f35,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | sK4(X0,X1,X2) = X2) )),
% 3.68/0.86    inference(cnf_transformation,[],[f17])).
% 3.68/0.86  fof(f17,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.68/0.86    inference(flattening,[],[f16])).
% 3.68/0.86  fof(f16,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : (? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.68/0.86    inference(ennf_transformation,[],[f8])).
% 3.68/0.86  fof(f8,axiom,(
% 3.68/0.86    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ? [X3] : (v3_pre_topc(X3,X0) & r2_hidden(X1,X3) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 3.68/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_yellow_6)).
% 3.68/0.86  fof(f26,plain,(
% 3.68/0.86    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.68/0.86    inference(cnf_transformation,[],[f13])).
% 3.68/0.86  fof(f13,plain,(
% 3.68/0.86    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.68/0.86    inference(flattening,[],[f12])).
% 3.68/0.86  fof(f12,plain,(
% 3.68/0.86    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.68/0.86    inference(ennf_transformation,[],[f11])).
% 3.68/0.86  fof(f11,negated_conjecture,(
% 3.68/0.86    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.68/0.86    inference(negated_conjecture,[],[f10])).
% 3.68/0.86  fof(f10,conjecture,(
% 3.68/0.86    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.68/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_9)).
% 3.68/0.86  fof(f27,plain,(
% 3.68/0.86    m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.68/0.86    inference(cnf_transformation,[],[f13])).
% 3.68/0.86  fof(f30,plain,(
% 3.68/0.86    l1_pre_topc(sK0)),
% 3.68/0.86    inference(cnf_transformation,[],[f13])).
% 3.68/0.86  fof(f28,plain,(
% 3.68/0.86    ~v2_struct_0(sK0)),
% 3.68/0.86    inference(cnf_transformation,[],[f13])).
% 3.68/0.86  fof(f29,plain,(
% 3.68/0.86    v2_pre_topc(sK0)),
% 3.68/0.86    inference(cnf_transformation,[],[f13])).
% 3.68/0.86  fof(f224,plain,(
% 3.68/0.86    m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f28,f29,f30,f27,f26,f34])).
% 3.68/0.86  fof(f34,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | v2_struct_0(X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f17])).
% 3.68/0.86  fof(f757,plain,(
% 3.68/0.86    ~r1_tarski(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(sK0))),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f289,f43])).
% 3.68/0.86  fof(f43,plain,(
% 3.68/0.86    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f5])).
% 3.68/0.86  fof(f5,axiom,(
% 3.68/0.86    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.68/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.68/0.86  fof(f289,plain,(
% 3.68/0.86    ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.68/0.86    inference(global_subsumption,[],[f30,f29,f28,f27,f208,f260,f280])).
% 3.68/0.86  fof(f280,plain,(
% 3.68/0.86    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) | ~v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0) | v2_struct_0(sK0)),
% 3.68/0.86    inference(resolution,[],[f33,f71])).
% 3.68/0.86  fof(f71,plain,(
% 3.68/0.86    ~r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f54,f66,f46])).
% 3.68/0.86  fof(f46,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f23])).
% 3.68/0.86  fof(f23,plain,(
% 3.68/0.86    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.68/0.86    inference(flattening,[],[f22])).
% 3.68/0.86  fof(f22,plain,(
% 3.68/0.86    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.68/0.86    inference(ennf_transformation,[],[f6])).
% 3.68/0.86  fof(f6,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.68/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 3.68/0.86  fof(f66,plain,(
% 3.68/0.86    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f64,f43])).
% 3.68/0.86  fof(f64,plain,(
% 3.68/0.86    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.68/0.86    inference(duplicate_literal_removal,[],[f63])).
% 3.68/0.86  fof(f63,plain,(
% 3.68/0.86    ( ! [X0] : (r1_tarski(X0,X0) | r1_tarski(X0,X0)) )),
% 3.68/0.86    inference(resolution,[],[f42,f41])).
% 3.68/0.86  fof(f41,plain,(
% 3.68/0.86    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f19])).
% 3.68/0.86  fof(f54,plain,(
% 3.68/0.86    ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.68/0.86    inference(definition_unfolding,[],[f25,f38])).
% 3.68/0.86  fof(f38,plain,(
% 3.68/0.86    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.68/0.86    inference(cnf_transformation,[],[f4])).
% 3.68/0.86  fof(f4,axiom,(
% 3.68/0.86    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.68/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.68/0.86  fof(f25,plain,(
% 3.68/0.86    ~m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.68/0.86    inference(cnf_transformation,[],[f13])).
% 3.68/0.86  fof(f33,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~v3_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f15])).
% 3.68/0.86  fof(f15,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.68/0.86    inference(flattening,[],[f14])).
% 3.68/0.86  fof(f14,plain,(
% 3.68/0.86    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.68/0.86    inference(ennf_transformation,[],[f9])).
% 3.68/0.86  fof(f9,axiom,(
% 3.68/0.86    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 3.68/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).
% 3.68/0.86  fof(f260,plain,(
% 3.68/0.86    v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0)),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f29,f30,f194,f193,f230,f231,f55])).
% 3.68/0.86  fof(f55,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 3.68/0.86    inference(definition_unfolding,[],[f45,f38])).
% 3.68/0.86  fof(f45,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k3_xboole_0(X1,X2),X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f21])).
% 3.68/0.86  fof(f21,plain,(
% 3.68/0.86    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.68/0.86    inference(flattening,[],[f20])).
% 3.68/0.86  fof(f20,plain,(
% 3.68/0.86    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.68/0.86    inference(ennf_transformation,[],[f7])).
% 3.68/0.86  fof(f7,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 3.68/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).
% 3.68/0.86  fof(f231,plain,(
% 3.68/0.86    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.68/0.86    inference(forward_demodulation,[],[f223,f150])).
% 3.68/0.86  fof(f150,plain,(
% 3.68/0.86    sK3 = sK4(sK0,sK1,sK3)),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f24,f35])).
% 3.68/0.86  fof(f24,plain,(
% 3.68/0.86    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.68/0.86    inference(cnf_transformation,[],[f13])).
% 3.68/0.86  fof(f223,plain,(
% 3.68/0.86    m1_subset_1(sK4(sK0,sK1,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f28,f29,f30,f27,f24,f34])).
% 3.68/0.86  fof(f193,plain,(
% 3.68/0.86    v3_pre_topc(sK2,sK0)),
% 3.68/0.86    inference(forward_demodulation,[],[f189,f151])).
% 3.68/0.86  fof(f189,plain,(
% 3.68/0.86    v3_pre_topc(sK4(sK0,sK1,sK2),sK0)),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f26,f37])).
% 3.68/0.86  fof(f37,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | v3_pre_topc(sK4(X0,X1,X2),X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f17])).
% 3.68/0.86  fof(f194,plain,(
% 3.68/0.86    v3_pre_topc(sK3,sK0)),
% 3.68/0.86    inference(forward_demodulation,[],[f188,f150])).
% 3.68/0.86  fof(f188,plain,(
% 3.68/0.86    v3_pre_topc(sK4(sK0,sK1,sK3),sK0)),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f24,f37])).
% 3.68/0.86  fof(f208,plain,(
% 3.68/0.86    r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f181,f61])).
% 3.68/0.86  fof(f61,plain,(
% 3.68/0.86    ( ! [X0,X3,X1] : (r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | ~sP7(X3,X1,X0)) )),
% 3.68/0.86    inference(equality_resolution,[],[f59])).
% 3.68/0.86  fof(f59,plain,(
% 3.68/0.86    ( ! [X2,X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 3.68/0.86    inference(definition_unfolding,[],[f50,f38])).
% 3.68/0.86  fof(f50,plain,(
% 3.68/0.86    ( ! [X2,X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.68/0.86    inference(cnf_transformation,[],[f2])).
% 3.68/0.86  fof(f2,axiom,(
% 3.68/0.86    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.68/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 3.68/0.86  fof(f181,plain,(
% 3.68/0.86    sP7(sK1,sK3,sK2)),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f162,f163,f47])).
% 3.68/0.86  fof(f47,plain,(
% 3.68/0.86    ( ! [X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f2])).
% 3.68/0.86  fof(f163,plain,(
% 3.68/0.86    r2_hidden(sK1,sK3)),
% 3.68/0.86    inference(forward_demodulation,[],[f157,f150])).
% 3.68/0.86  fof(f157,plain,(
% 3.68/0.86    r2_hidden(sK1,sK4(sK0,sK1,sK3))),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f24,f36])).
% 3.68/0.86  fof(f36,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,sK4(X0,X1,X2))) )),
% 3.68/0.86    inference(cnf_transformation,[],[f17])).
% 3.68/0.86  fof(f162,plain,(
% 3.68/0.86    r2_hidden(sK1,sK2)),
% 3.68/0.86    inference(forward_demodulation,[],[f158,f151])).
% 3.68/0.86  fof(f158,plain,(
% 3.68/0.86    r2_hidden(sK1,sK4(sK0,sK1,sK2))),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f29,f28,f30,f27,f26,f36])).
% 3.68/0.86  fof(f954,plain,(
% 3.68/0.86    r2_hidden(sK5(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(sK0)),sK2)),
% 3.68/0.86    inference(unit_resulting_resolution,[],[f757,f337])).
% 3.68/0.86  fof(f337,plain,(
% 3.68/0.86    ( ! [X4,X5,X3] : (r2_hidden(sK5(k1_setfam_1(k2_tarski(X3,X4)),X5),X3) | r1_tarski(k1_setfam_1(k2_tarski(X3,X4)),X5)) )),
% 3.68/0.86    inference(resolution,[],[f91,f48])).
% 3.68/0.86  fof(f48,plain,(
% 3.68/0.86    ( ! [X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 3.68/0.86    inference(cnf_transformation,[],[f2])).
% 3.68/0.86  fof(f91,plain,(
% 3.68/0.86    ( ! [X2,X0,X1] : (sP7(sK5(k1_setfam_1(k2_tarski(X0,X1)),X2),X1,X0) | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) )),
% 3.68/0.86    inference(resolution,[],[f60,f41])).
% 3.68/0.86  fof(f60,plain,(
% 3.68/0.86    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | sP7(X3,X1,X0)) )),
% 3.68/0.86    inference(equality_resolution,[],[f58])).
% 3.68/0.86  fof(f58,plain,(
% 3.68/0.86    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 3.68/0.86    inference(definition_unfolding,[],[f51,f38])).
% 3.68/0.86  fof(f51,plain,(
% 3.68/0.86    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.68/0.86    inference(cnf_transformation,[],[f2])).
% 3.68/0.86  % SZS output end Proof for theBenchmark
% 3.68/0.86  % (7215)------------------------------
% 3.68/0.86  % (7215)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.68/0.86  % (7215)Termination reason: Refutation
% 3.68/0.86  
% 3.68/0.86  % (7215)Memory used [KB]: 8827
% 3.68/0.86  % (7215)Time elapsed: 0.342 s
% 3.68/0.86  % (7215)------------------------------
% 3.68/0.86  % (7215)------------------------------
% 3.68/0.86  % (7190)Success in time 0.494 s
%------------------------------------------------------------------------------
