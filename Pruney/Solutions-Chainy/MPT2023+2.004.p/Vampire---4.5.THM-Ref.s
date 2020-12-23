%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:07 EST 2020

% Result     : Theorem 2.19s
% Output     : Refutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 806 expanded)
%              Number of leaves         :   13 ( 171 expanded)
%              Depth                    :   15
%              Number of atoms          :  276 (4149 expanded)
%              Number of equality atoms :   14 (  49 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1070,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f39,f40,f41,f38,f431,f381,f82,f325,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ v3_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f325,plain,(
    ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(X0,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f321,f320])).

fof(f320,plain,(
    ! [X0] : k1_setfam_1(k2_tarski(X0,sK3)) = k9_subset_1(u1_struct_0(sK0),X0,sK3) ),
    inference(unit_resulting_resolution,[],[f318,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f60,f48])).

fof(f48,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f318,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f39,f40,f41,f38,f311,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f311,plain,(
    m1_connsp_2(sK3,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f41,f39,f40,f38,f35,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f35,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f321,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f318,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f82,plain,(
    ~ r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f70,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f47,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f70,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(definition_unfolding,[],[f36,f48])).

fof(f36,plain,(
    ~ m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f381,plain,(
    r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f349,f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f66,f48])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f349,plain,(
    sP7(sK1,sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f326,f333,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f333,plain,(
    r2_hidden(sK1,sK2) ),
    inference(global_subsumption,[],[f41,f40,f39,f38,f319,f327])).

fof(f327,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f42,f168])).

fof(f168,plain,(
    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f37,f129,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f129,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f37,f125,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f125,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f119,f104])).

fof(f104,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f57,f47])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f119,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(global_subsumption,[],[f37,f118])).

fof(f118,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ r1_tarski(sK2,sK3) ),
    inference(superposition,[],[f70,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f53,f48])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f37,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f319,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f39,f40,f41,f38,f312,f55])).

fof(f312,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f41,f39,f40,f38,f37,f45])).

fof(f326,plain,(
    r2_hidden(sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f39,f41,f40,f38,f318,f167,f42])).

fof(f167,plain,(
    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f35,f129,f52])).

fof(f431,plain,(
    v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0) ),
    inference(unit_resulting_resolution,[],[f40,f41,f364,f357,f318,f319,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f61,f48])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).

fof(f357,plain,(
    v3_pre_topc(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f39,f41,f40,f38,f318,f167,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f364,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(global_subsumption,[],[f41,f40,f39,f38,f319,f358])).

fof(f358,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f43,f168])).

fof(f38,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n015.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 16:22:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.51  % (1542)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (1558)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.53  % (1550)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (1538)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (1546)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (1560)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (1546)Refutation not found, incomplete strategy% (1546)------------------------------
% 0.21/0.54  % (1546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (1546)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (1546)Memory used [KB]: 10618
% 0.21/0.54  % (1546)Time elapsed: 0.122 s
% 0.21/0.54  % (1546)------------------------------
% 0.21/0.54  % (1546)------------------------------
% 0.21/0.54  % (1543)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.54  % (1563)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (1537)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (1539)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (1544)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (1545)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (1552)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (1562)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (1540)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (1551)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (1555)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (1564)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (1537)Refutation not found, incomplete strategy% (1537)------------------------------
% 0.21/0.55  % (1537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1537)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1537)Memory used [KB]: 1663
% 0.21/0.55  % (1537)Time elapsed: 0.135 s
% 0.21/0.55  % (1537)------------------------------
% 0.21/0.55  % (1537)------------------------------
% 0.21/0.55  % (1554)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (1565)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (1554)Refutation not found, incomplete strategy% (1554)------------------------------
% 0.21/0.55  % (1554)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (1554)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (1554)Memory used [KB]: 10618
% 0.21/0.55  % (1554)Time elapsed: 0.147 s
% 0.21/0.55  % (1554)------------------------------
% 0.21/0.55  % (1554)------------------------------
% 0.21/0.55  % (1561)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (1559)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.56  % (1566)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (1549)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (1547)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (1547)Refutation not found, incomplete strategy% (1547)------------------------------
% 0.21/0.56  % (1547)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (1553)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (1557)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.57  % (1541)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.57  % (1547)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (1547)Memory used [KB]: 10618
% 0.21/0.57  % (1547)Time elapsed: 0.148 s
% 0.21/0.57  % (1547)------------------------------
% 0.21/0.57  % (1547)------------------------------
% 0.21/0.58  % (1556)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.59  % (1559)Refutation not found, incomplete strategy% (1559)------------------------------
% 0.21/0.59  % (1559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.59  % (1559)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.59  
% 0.21/0.59  % (1559)Memory used [KB]: 11129
% 0.21/0.59  % (1559)Time elapsed: 0.184 s
% 0.21/0.59  % (1559)------------------------------
% 0.21/0.59  % (1559)------------------------------
% 0.21/0.59  % (1548)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.60  % (1548)Refutation not found, incomplete strategy% (1548)------------------------------
% 0.21/0.60  % (1548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.61  % (1548)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.61  
% 0.21/0.61  % (1548)Memory used [KB]: 10618
% 0.21/0.61  % (1548)Time elapsed: 0.163 s
% 0.21/0.61  % (1548)------------------------------
% 0.21/0.61  % (1548)------------------------------
% 2.19/0.66  % (1561)Refutation found. Thanks to Tanya!
% 2.19/0.66  % SZS status Theorem for theBenchmark
% 2.19/0.66  % SZS output start Proof for theBenchmark
% 2.19/0.66  fof(f1070,plain,(
% 2.19/0.66    $false),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f39,f40,f41,f38,f431,f381,f82,f325,f44])).
% 2.19/0.66  fof(f44,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~v3_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f20])).
% 2.19/0.66  fof(f20,plain,(
% 2.19/0.66    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.19/0.66    inference(flattening,[],[f19])).
% 2.19/0.66  fof(f19,plain,(
% 2.19/0.66    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.19/0.66    inference(ennf_transformation,[],[f13])).
% 2.19/0.66  fof(f13,axiom,(
% 2.19/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_yellow_6)).
% 2.19/0.66  fof(f325,plain,(
% 2.19/0.66    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(X0,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.19/0.66    inference(backward_demodulation,[],[f321,f320])).
% 2.19/0.66  fof(f320,plain,(
% 2.19/0.66    ( ! [X0] : (k1_setfam_1(k2_tarski(X0,sK3)) = k9_subset_1(u1_struct_0(sK0),X0,sK3)) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f318,f72])).
% 2.19/0.66  fof(f72,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.19/0.66    inference(definition_unfolding,[],[f60,f48])).
% 2.19/0.66  fof(f48,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.19/0.66    inference(cnf_transformation,[],[f8])).
% 2.19/0.66  fof(f8,axiom,(
% 2.19/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.19/0.66  fof(f60,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f30])).
% 2.19/0.66  fof(f30,plain,(
% 2.19/0.66    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.19/0.66    inference(ennf_transformation,[],[f7])).
% 2.19/0.66  fof(f7,axiom,(
% 2.19/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.19/0.66  fof(f318,plain,(
% 2.19/0.66    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f39,f40,f41,f38,f311,f55])).
% 2.19/0.66  fof(f55,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f27])).
% 2.19/0.66  fof(f27,plain,(
% 2.19/0.66    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.19/0.66    inference(flattening,[],[f26])).
% 2.19/0.66  fof(f26,plain,(
% 2.19/0.66    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.19/0.66    inference(ennf_transformation,[],[f12])).
% 2.19/0.66  fof(f12,axiom,(
% 2.19/0.66    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 2.19/0.66  fof(f311,plain,(
% 2.19/0.66    m1_connsp_2(sK3,sK0,sK1)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f41,f39,f40,f38,f35,f45])).
% 2.19/0.66  fof(f45,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_connsp_2(X2,X0,X1)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f22])).
% 2.19/0.66  fof(f22,plain,(
% 2.19/0.66    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.19/0.66    inference(flattening,[],[f21])).
% 2.19/0.66  fof(f21,plain,(
% 2.19/0.66    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.19/0.66    inference(ennf_transformation,[],[f14])).
% 2.19/0.66  fof(f14,axiom,(
% 2.19/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_waybel_9)).
% 2.19/0.66  fof(f35,plain,(
% 2.19/0.66    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.19/0.66    inference(cnf_transformation,[],[f18])).
% 2.19/0.66  fof(f18,plain,(
% 2.19/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.19/0.66    inference(flattening,[],[f17])).
% 2.19/0.66  fof(f17,plain,(
% 2.19/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.19/0.66    inference(ennf_transformation,[],[f16])).
% 2.19/0.66  fof(f16,negated_conjecture,(
% 2.19/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 2.19/0.66    inference(negated_conjecture,[],[f15])).
% 2.19/0.66  fof(f15,conjecture,(
% 2.19/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_waybel_9)).
% 2.19/0.66  fof(f321,plain,(
% 2.19/0.66    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f318,f59])).
% 2.19/0.66  fof(f59,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.19/0.66    inference(cnf_transformation,[],[f29])).
% 2.19/0.66  fof(f29,plain,(
% 2.19/0.66    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.19/0.66    inference(ennf_transformation,[],[f6])).
% 2.19/0.66  fof(f6,axiom,(
% 2.19/0.66    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 2.19/0.66  fof(f82,plain,(
% 2.19/0.66    ~r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f70,f80])).
% 2.19/0.66  fof(f80,plain,(
% 2.19/0.66    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 2.19/0.66    inference(global_subsumption,[],[f47,f51])).
% 2.19/0.66  fof(f51,plain,(
% 2.19/0.66    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f23])).
% 2.19/0.66  fof(f23,plain,(
% 2.19/0.66    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 2.19/0.66    inference(ennf_transformation,[],[f5])).
% 2.19/0.66  fof(f5,axiom,(
% 2.19/0.66    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).
% 2.19/0.66  fof(f47,plain,(
% 2.19/0.66    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f1])).
% 2.19/0.66  fof(f1,axiom,(
% 2.19/0.66    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 2.19/0.66  fof(f70,plain,(
% 2.19/0.66    ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.19/0.66    inference(definition_unfolding,[],[f36,f48])).
% 2.19/0.66  fof(f36,plain,(
% 2.19/0.66    ~m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.19/0.66    inference(cnf_transformation,[],[f18])).
% 2.19/0.66  fof(f381,plain,(
% 2.19/0.66    r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f349,f79])).
% 2.19/0.66  fof(f79,plain,(
% 2.19/0.66    ( ! [X0,X3,X1] : (r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | ~sP7(X3,X1,X0)) )),
% 2.19/0.66    inference(equality_resolution,[],[f77])).
% 2.19/0.66  fof(f77,plain,(
% 2.19/0.66    ( ! [X2,X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 2.19/0.66    inference(definition_unfolding,[],[f66,f48])).
% 2.19/0.66  fof(f66,plain,(
% 2.19/0.66    ( ! [X2,X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 2.19/0.66    inference(cnf_transformation,[],[f3])).
% 2.19/0.66  fof(f3,axiom,(
% 2.19/0.66    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 2.19/0.66  fof(f349,plain,(
% 2.19/0.66    sP7(sK1,sK3,sK2)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f326,f333,f63])).
% 2.19/0.66  fof(f63,plain,(
% 2.19/0.66    ( ! [X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f3])).
% 2.19/0.66  fof(f333,plain,(
% 2.19/0.66    r2_hidden(sK1,sK2)),
% 2.19/0.66    inference(global_subsumption,[],[f41,f40,f39,f38,f319,f327])).
% 2.19/0.66  fof(f327,plain,(
% 2.19/0.66    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK2) | v2_struct_0(sK0)),
% 2.19/0.66    inference(resolution,[],[f42,f168])).
% 2.19/0.66  fof(f168,plain,(
% 2.19/0.66    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f37,f129,f52])).
% 2.19/0.66  fof(f52,plain,(
% 2.19/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f23])).
% 2.19/0.66  fof(f129,plain,(
% 2.19/0.66    ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f37,f125,f50])).
% 2.19/0.66  fof(f50,plain,(
% 2.19/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f23])).
% 2.19/0.66  fof(f125,plain,(
% 2.19/0.66    ~v1_xboole_0(sK2)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f119,f104])).
% 2.19/0.66  fof(f104,plain,(
% 2.19/0.66    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v1_xboole_0(X2)) )),
% 2.19/0.66    inference(resolution,[],[f57,f47])).
% 2.19/0.66  fof(f57,plain,(
% 2.19/0.66    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f28])).
% 2.19/0.66  fof(f28,plain,(
% 2.19/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.19/0.66    inference(ennf_transformation,[],[f2])).
% 2.19/0.66  fof(f2,axiom,(
% 2.19/0.66    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 2.19/0.66  fof(f119,plain,(
% 2.19/0.66    ~r1_tarski(sK2,sK3)),
% 2.19/0.66    inference(global_subsumption,[],[f37,f118])).
% 2.19/0.66  fof(f118,plain,(
% 2.19/0.66    ~m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~r1_tarski(sK2,sK3)),
% 2.19/0.66    inference(superposition,[],[f70,f71])).
% 2.19/0.66  fof(f71,plain,(
% 2.19/0.66    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 2.19/0.66    inference(definition_unfolding,[],[f53,f48])).
% 2.19/0.66  fof(f53,plain,(
% 2.19/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.19/0.66    inference(cnf_transformation,[],[f24])).
% 2.19/0.66  fof(f24,plain,(
% 2.19/0.66    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.19/0.66    inference(ennf_transformation,[],[f4])).
% 2.19/0.66  fof(f4,axiom,(
% 2.19/0.66    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.19/0.66  fof(f37,plain,(
% 2.19/0.66    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.19/0.66    inference(cnf_transformation,[],[f18])).
% 2.19/0.66  fof(f42,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X2) | v2_struct_0(X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f20])).
% 2.19/0.66  fof(f319,plain,(
% 2.19/0.66    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f39,f40,f41,f38,f312,f55])).
% 2.19/0.66  fof(f312,plain,(
% 2.19/0.66    m1_connsp_2(sK2,sK0,sK1)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f41,f39,f40,f38,f37,f45])).
% 2.19/0.66  fof(f326,plain,(
% 2.19/0.66    r2_hidden(sK1,sK3)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f39,f41,f40,f38,f318,f167,f42])).
% 2.19/0.66  fof(f167,plain,(
% 2.19/0.66    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f35,f129,f52])).
% 2.19/0.66  fof(f431,plain,(
% 2.19/0.66    v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f40,f41,f364,f357,f318,f319,f73])).
% 2.19/0.66  fof(f73,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 2.19/0.66    inference(definition_unfolding,[],[f61,f48])).
% 2.19/0.66  fof(f61,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k3_xboole_0(X1,X2),X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f32])).
% 2.19/0.66  fof(f32,plain,(
% 2.19/0.66    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.19/0.66    inference(flattening,[],[f31])).
% 2.19/0.66  fof(f31,plain,(
% 2.19/0.66    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.19/0.66    inference(ennf_transformation,[],[f11])).
% 2.19/0.66  fof(f11,axiom,(
% 2.19/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 2.19/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_tops_1)).
% 2.19/0.66  fof(f357,plain,(
% 2.19/0.66    v3_pre_topc(sK3,sK0)),
% 2.19/0.66    inference(unit_resulting_resolution,[],[f39,f41,f40,f38,f318,f167,f43])).
% 2.19/0.66  fof(f43,plain,(
% 2.19/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 2.19/0.66    inference(cnf_transformation,[],[f20])).
% 2.19/0.67  fof(f364,plain,(
% 2.19/0.67    v3_pre_topc(sK2,sK0)),
% 2.19/0.67    inference(global_subsumption,[],[f41,f40,f39,f38,f319,f358])).
% 2.19/0.67  fof(f358,plain,(
% 2.19/0.67    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2,sK0) | v2_struct_0(sK0)),
% 2.19/0.67    inference(resolution,[],[f43,f168])).
% 2.19/0.67  fof(f38,plain,(
% 2.19/0.67    m1_subset_1(sK1,u1_struct_0(sK0))),
% 2.19/0.67    inference(cnf_transformation,[],[f18])).
% 2.19/0.67  fof(f41,plain,(
% 2.19/0.67    l1_pre_topc(sK0)),
% 2.19/0.67    inference(cnf_transformation,[],[f18])).
% 2.19/0.67  fof(f40,plain,(
% 2.19/0.67    v2_pre_topc(sK0)),
% 2.19/0.67    inference(cnf_transformation,[],[f18])).
% 2.19/0.67  fof(f39,plain,(
% 2.19/0.67    ~v2_struct_0(sK0)),
% 2.19/0.67    inference(cnf_transformation,[],[f18])).
% 2.19/0.67  % SZS output end Proof for theBenchmark
% 2.19/0.67  % (1561)------------------------------
% 2.19/0.67  % (1561)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.19/0.67  % (1561)Termination reason: Refutation
% 2.19/0.67  
% 2.19/0.67  % (1561)Memory used [KB]: 7164
% 2.19/0.67  % (1561)Time elapsed: 0.223 s
% 2.19/0.67  % (1561)------------------------------
% 2.19/0.67  % (1561)------------------------------
% 2.19/0.67  % (1536)Success in time 0.295 s
%------------------------------------------------------------------------------
