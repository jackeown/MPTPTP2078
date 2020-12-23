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
% DateTime   : Thu Dec  3 13:23:09 EST 2020

% Result     : Theorem 1.79s
% Output     : Refutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 792 expanded)
%              Number of leaves         :   13 ( 166 expanded)
%              Depth                    :   15
%              Number of atoms          :  282 (4140 expanded)
%              Number of equality atoms :   15 (  42 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f615,plain,(
    $false ),
    inference(global_subsumption,[],[f431,f604])).

fof(f604,plain,(
    ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f44,f46,f45,f43,f407,f88,f368,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ v3_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).

fof(f368,plain,(
    ! [X0] : r2_hidden(sK1,k3_tarski(k2_tarski(X0,sK3))) ),
    inference(unit_resulting_resolution,[],[f330,f85])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k3_tarski(k2_tarski(X0,X1)))
      | ~ sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_tarski(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f72,f53])).

fof(f53,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f330,plain,(
    ! [X0] : sP7(sK1,sK3,X0) ),
    inference(unit_resulting_resolution,[],[f319,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f319,plain,(
    r2_hidden(sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f44,f46,f45,f43,f307,f163,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f163,plain,(
    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f40,f128,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f128,plain,(
    ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f42,f124,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f124,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(unit_resulting_resolution,[],[f121,f104])).

fof(f104,plain,(
    ! [X2,X3] :
      ( r1_tarski(X2,X3)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f63,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f121,plain,(
    ~ r1_tarski(sK2,sK3) ),
    inference(global_subsumption,[],[f40,f120])).

fof(f120,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | ~ r1_tarski(sK2,sK3) ),
    inference(superposition,[],[f76,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( k3_tarski(k2_tarski(X0,X1)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f53])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f76,plain,(
    ~ m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(definition_unfolding,[],[f41,f53])).

fof(f41,plain,(
    ~ m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))
                  & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) )
              & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
                   => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
                 => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).

fof(f42,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f19])).

fof(f307,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f44,f45,f46,f43,f299,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f299,plain,(
    m1_connsp_2(sK3,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f44,f45,f43,f40,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X2,X0,X1)
              | ~ m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))
             => m1_connsp_2(X2,X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f88,plain,(
    ~ r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f76,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f52,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f407,plain,(
    v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0) ),
    inference(unit_resulting_resolution,[],[f45,f46,f357,f349,f307,f308,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f65,f53])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k2_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).

fof(f308,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f44,f45,f46,f43,f300,f61])).

fof(f300,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f46,f44,f45,f43,f42,f50])).

fof(f349,plain,(
    v3_pre_topc(sK3,sK0) ),
    inference(unit_resulting_resolution,[],[f44,f46,f45,f43,f307,f163,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f357,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(global_subsumption,[],[f46,f45,f44,f43,f308,f352])).

fof(f352,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f48,f164])).

fof(f164,plain,(
    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f42,f128,f57])).

fof(f43,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f431,plain,(
    m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f415,f411])).

fof(f411,plain,(
    k3_tarski(k2_tarski(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f307,f308,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f68,f53])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f415,plain,(
    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f307,f308,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:54:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (3675)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (3683)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (3691)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (3664)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (3667)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (3666)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (3668)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (3674)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (3685)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (3665)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (3663)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (3674)Refutation not found, incomplete strategy% (3674)------------------------------
% 0.21/0.54  % (3674)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3674)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3674)Memory used [KB]: 10618
% 0.21/0.54  % (3674)Time elapsed: 0.132 s
% 0.21/0.54  % (3674)------------------------------
% 0.21/0.54  % (3674)------------------------------
% 0.21/0.54  % (3663)Refutation not found, incomplete strategy% (3663)------------------------------
% 0.21/0.54  % (3663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3663)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3663)Memory used [KB]: 1663
% 0.21/0.54  % (3663)Time elapsed: 0.120 s
% 0.21/0.54  % (3663)------------------------------
% 0.21/0.54  % (3663)------------------------------
% 0.21/0.54  % (3677)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (3680)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (3673)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.54  % (3670)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (3680)Refutation not found, incomplete strategy% (3680)------------------------------
% 0.21/0.54  % (3680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3680)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3680)Memory used [KB]: 10618
% 0.21/0.54  % (3680)Time elapsed: 0.128 s
% 0.21/0.54  % (3680)------------------------------
% 0.21/0.54  % (3680)------------------------------
% 0.21/0.54  % (3673)Refutation not found, incomplete strategy% (3673)------------------------------
% 0.21/0.54  % (3673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (3673)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (3673)Memory used [KB]: 10618
% 0.21/0.54  % (3673)Time elapsed: 0.128 s
% 0.21/0.54  % (3673)------------------------------
% 0.21/0.54  % (3673)------------------------------
% 0.21/0.54  % (3682)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (3692)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (3689)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (3679)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (3681)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (3669)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (3687)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (3684)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (3678)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.55  % (3688)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (3690)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.56  % (3685)Refutation not found, incomplete strategy% (3685)------------------------------
% 0.21/0.56  % (3685)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3685)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3685)Memory used [KB]: 10874
% 0.21/0.56  % (3685)Time elapsed: 0.103 s
% 0.21/0.56  % (3685)------------------------------
% 0.21/0.56  % (3685)------------------------------
% 0.21/0.56  % (3672)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (3686)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.56  % (3676)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.56  % (3671)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.56  % (3672)Refutation not found, incomplete strategy% (3672)------------------------------
% 0.21/0.56  % (3672)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3672)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3672)Memory used [KB]: 10618
% 0.21/0.56  % (3672)Time elapsed: 0.148 s
% 0.21/0.56  % (3672)------------------------------
% 0.21/0.56  % (3672)------------------------------
% 1.79/0.60  % (3687)Refutation found. Thanks to Tanya!
% 1.79/0.60  % SZS status Theorem for theBenchmark
% 1.79/0.60  % SZS output start Proof for theBenchmark
% 1.79/0.60  fof(f615,plain,(
% 1.79/0.60    $false),
% 1.79/0.60    inference(global_subsumption,[],[f431,f604])).
% 1.79/0.60  fof(f604,plain,(
% 1.79/0.60    ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f44,f46,f45,f43,f407,f88,f368,f49])).
% 1.79/0.60  fof(f49,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~v3_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f21])).
% 1.79/0.60  fof(f21,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.60    inference(flattening,[],[f20])).
% 1.79/0.60  fof(f20,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f14])).
% 1.79/0.60  fof(f14,axiom,(
% 1.79/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).
% 1.79/0.60  fof(f368,plain,(
% 1.79/0.60    ( ! [X0] : (r2_hidden(sK1,k3_tarski(k2_tarski(X0,sK3)))) )),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f330,f85])).
% 1.79/0.60  fof(f85,plain,(
% 1.79/0.60    ( ! [X0,X3,X1] : (r2_hidden(X3,k3_tarski(k2_tarski(X0,X1))) | ~sP7(X3,X1,X0)) )),
% 1.79/0.60    inference(equality_resolution,[],[f83])).
% 1.79/0.60  fof(f83,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k3_tarski(k2_tarski(X0,X1)) != X2) )),
% 1.79/0.60    inference(definition_unfolding,[],[f72,f53])).
% 1.79/0.60  fof(f53,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.79/0.60    inference(cnf_transformation,[],[f5])).
% 1.79/0.60  fof(f5,axiom,(
% 1.79/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.79/0.60  fof(f72,plain,(
% 1.79/0.60    ( ! [X2,X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 1.79/0.60    inference(cnf_transformation,[],[f3])).
% 1.79/0.60  fof(f3,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 1.79/0.60  fof(f330,plain,(
% 1.79/0.60    ( ! [X0] : (sP7(sK1,sK3,X0)) )),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f319,f70])).
% 1.79/0.60  fof(f70,plain,(
% 1.79/0.60    ( ! [X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f3])).
% 1.79/0.60  fof(f319,plain,(
% 1.79/0.60    r2_hidden(sK1,sK3)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f44,f46,f45,f43,f307,f163,f47])).
% 1.79/0.60  fof(f47,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X2) | v2_struct_0(X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f21])).
% 1.79/0.60  fof(f163,plain,(
% 1.79/0.60    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f40,f128,f57])).
% 1.79/0.60  fof(f57,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f24])).
% 1.79/0.60  fof(f24,plain,(
% 1.79/0.60    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f6])).
% 1.79/0.60  fof(f6,axiom,(
% 1.79/0.60    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 1.79/0.60  fof(f128,plain,(
% 1.79/0.60    ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f42,f124,f55])).
% 1.79/0.60  fof(f55,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f24])).
% 1.79/0.60  fof(f124,plain,(
% 1.79/0.60    ~v1_xboole_0(sK2)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f121,f104])).
% 1.79/0.60  fof(f104,plain,(
% 1.79/0.60    ( ! [X2,X3] : (r1_tarski(X2,X3) | ~v1_xboole_0(X2)) )),
% 1.79/0.60    inference(resolution,[],[f63,f52])).
% 1.79/0.60  fof(f52,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f1])).
% 1.79/0.60  fof(f1,axiom,(
% 1.79/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.79/0.60  fof(f63,plain,(
% 1.79/0.60    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f31])).
% 1.79/0.60  fof(f31,plain,(
% 1.79/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f2])).
% 1.79/0.60  fof(f2,axiom,(
% 1.79/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.79/0.60  fof(f121,plain,(
% 1.79/0.60    ~r1_tarski(sK2,sK3)),
% 1.79/0.60    inference(global_subsumption,[],[f40,f120])).
% 1.79/0.60  fof(f120,plain,(
% 1.79/0.60    ~m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | ~r1_tarski(sK2,sK3)),
% 1.79/0.60    inference(superposition,[],[f76,f77])).
% 1.79/0.60  fof(f77,plain,(
% 1.79/0.60    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = X1 | ~r1_tarski(X0,X1)) )),
% 1.79/0.60    inference(definition_unfolding,[],[f58,f53])).
% 1.79/0.60  fof(f58,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.79/0.60    inference(cnf_transformation,[],[f25])).
% 1.79/0.60  fof(f25,plain,(
% 1.79/0.60    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.79/0.60    inference(ennf_transformation,[],[f4])).
% 1.79/0.60  fof(f4,axiom,(
% 1.79/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.79/0.60  fof(f76,plain,(
% 1.79/0.60    ~m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.79/0.60    inference(definition_unfolding,[],[f41,f53])).
% 1.79/0.60  fof(f41,plain,(
% 1.79/0.60    ~m1_subset_1(k2_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.79/0.60    inference(cnf_transformation,[],[f19])).
% 1.79/0.60  fof(f19,plain,(
% 1.79/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.79/0.60    inference(flattening,[],[f18])).
% 1.79/0.60  fof(f18,plain,(
% 1.79/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f17])).
% 1.79/0.60  fof(f17,negated_conjecture,(
% 1.79/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.79/0.60    inference(negated_conjecture,[],[f16])).
% 1.79/0.60  fof(f16,conjecture,(
% 1.79/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k2_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_waybel_9)).
% 1.79/0.60  fof(f42,plain,(
% 1.79/0.60    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.79/0.60    inference(cnf_transformation,[],[f19])).
% 1.79/0.60  fof(f40,plain,(
% 1.79/0.60    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.79/0.60    inference(cnf_transformation,[],[f19])).
% 1.79/0.60  fof(f307,plain,(
% 1.79/0.60    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f44,f45,f46,f43,f299,f61])).
% 1.79/0.60  fof(f61,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f30])).
% 1.79/0.60  fof(f30,plain,(
% 1.79/0.60    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.60    inference(flattening,[],[f29])).
% 1.79/0.60  fof(f29,plain,(
% 1.79/0.60    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f13])).
% 1.79/0.60  fof(f13,axiom,(
% 1.79/0.60    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 1.79/0.60  fof(f299,plain,(
% 1.79/0.60    m1_connsp_2(sK3,sK0,sK1)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f46,f44,f45,f43,f40,f50])).
% 1.79/0.60  fof(f50,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_connsp_2(X2,X0,X1)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f23])).
% 1.79/0.60  fof(f23,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.79/0.60    inference(flattening,[],[f22])).
% 1.79/0.60  fof(f22,plain,(
% 1.79/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f15])).
% 1.79/0.60  fof(f15,axiom,(
% 1.79/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).
% 1.79/0.60  fof(f88,plain,(
% 1.79/0.60    ~r2_hidden(k3_tarski(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f76,f86])).
% 1.79/0.60  fof(f86,plain,(
% 1.79/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.79/0.60    inference(global_subsumption,[],[f52,f56])).
% 1.79/0.60  fof(f56,plain,(
% 1.79/0.60    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f24])).
% 1.79/0.60  fof(f407,plain,(
% 1.79/0.60    v3_pre_topc(k3_tarski(k2_tarski(sK2,sK3)),sK0)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f45,f46,f357,f349,f307,f308,f78])).
% 1.79/0.60  fof(f78,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (v3_pre_topc(k3_tarski(k2_tarski(X1,X2)),X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 1.79/0.60    inference(definition_unfolding,[],[f65,f53])).
% 1.79/0.60  fof(f65,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k2_xboole_0(X1,X2),X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f33])).
% 1.79/0.60  fof(f33,plain,(
% 1.79/0.60    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.79/0.60    inference(flattening,[],[f32])).
% 1.79/0.60  fof(f32,plain,(
% 1.79/0.60    ! [X0,X1,X2] : (v3_pre_topc(k2_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.79/0.60    inference(ennf_transformation,[],[f12])).
% 1.79/0.60  fof(f12,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_xboole_0(X1,X2),X0))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_tops_1)).
% 1.79/0.60  fof(f308,plain,(
% 1.79/0.60    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f44,f45,f46,f43,f300,f61])).
% 1.79/0.60  fof(f300,plain,(
% 1.79/0.60    m1_connsp_2(sK2,sK0,sK1)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f46,f44,f45,f43,f42,f50])).
% 1.79/0.60  fof(f349,plain,(
% 1.79/0.60    v3_pre_topc(sK3,sK0)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f44,f46,f45,f43,f307,f163,f48])).
% 1.79/0.60  fof(f48,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f21])).
% 1.79/0.60  fof(f357,plain,(
% 1.79/0.60    v3_pre_topc(sK2,sK0)),
% 1.79/0.60    inference(global_subsumption,[],[f46,f45,f44,f43,f308,f352])).
% 1.79/0.60  fof(f352,plain,(
% 1.79/0.60    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2,sK0) | v2_struct_0(sK0)),
% 1.79/0.60    inference(resolution,[],[f48,f164])).
% 1.79/0.60  fof(f164,plain,(
% 1.79/0.60    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f42,f128,f57])).
% 1.79/0.60  fof(f43,plain,(
% 1.79/0.60    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.79/0.60    inference(cnf_transformation,[],[f19])).
% 1.79/0.60  fof(f45,plain,(
% 1.79/0.60    v2_pre_topc(sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f19])).
% 1.79/0.60  fof(f46,plain,(
% 1.79/0.60    l1_pre_topc(sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f19])).
% 1.79/0.60  fof(f44,plain,(
% 1.79/0.60    ~v2_struct_0(sK0)),
% 1.79/0.60    inference(cnf_transformation,[],[f19])).
% 1.79/0.60  fof(f431,plain,(
% 1.79/0.60    m1_subset_1(k3_tarski(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.60    inference(backward_demodulation,[],[f415,f411])).
% 1.79/0.60  fof(f411,plain,(
% 1.79/0.60    k3_tarski(k2_tarski(sK2,sK3)) = k4_subset_1(u1_struct_0(sK0),sK2,sK3)),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f307,f308,f79])).
% 1.79/0.60  fof(f79,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k3_tarski(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.79/0.60    inference(definition_unfolding,[],[f68,f53])).
% 1.79/0.60  fof(f68,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 1.79/0.60    inference(cnf_transformation,[],[f39])).
% 1.79/0.60  fof(f39,plain,(
% 1.79/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.60    inference(flattening,[],[f38])).
% 1.79/0.60  fof(f38,plain,(
% 1.79/0.60    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.79/0.60    inference(ennf_transformation,[],[f8])).
% 1.79/0.60  fof(f8,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 1.79/0.60  fof(f415,plain,(
% 1.79/0.60    m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.79/0.60    inference(unit_resulting_resolution,[],[f307,f308,f67])).
% 1.79/0.60  fof(f67,plain,(
% 1.79/0.60    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.79/0.60    inference(cnf_transformation,[],[f37])).
% 1.79/0.60  fof(f37,plain,(
% 1.79/0.60    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.79/0.60    inference(flattening,[],[f36])).
% 1.79/0.60  fof(f36,plain,(
% 1.79/0.60    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 1.79/0.60    inference(ennf_transformation,[],[f7])).
% 1.79/0.60  fof(f7,axiom,(
% 1.79/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.79/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 1.79/0.60  % SZS output end Proof for theBenchmark
% 1.79/0.60  % (3687)------------------------------
% 1.79/0.60  % (3687)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.79/0.60  % (3687)Termination reason: Refutation
% 1.79/0.60  
% 1.79/0.60  % (3687)Memory used [KB]: 6780
% 1.79/0.60  % (3687)Time elapsed: 0.197 s
% 1.79/0.60  % (3687)------------------------------
% 1.79/0.60  % (3687)------------------------------
% 1.79/0.61  % (3662)Success in time 0.242 s
%------------------------------------------------------------------------------
