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
% DateTime   : Thu Dec  3 13:23:07 EST 2020

% Result     : Theorem 3.14s
% Output     : Refutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  120 (8376 expanded)
%              Number of leaves         :   12 (1721 expanded)
%              Depth                    :   25
%              Number of atoms          :  401 (45197 expanded)
%              Number of equality atoms :   15 ( 208 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2545,plain,(
    $false ),
    inference(global_subsumption,[],[f34,f2477])).

fof(f2477,plain,(
    ~ m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(backward_demodulation,[],[f2202,f2371])).

fof(f2371,plain,(
    ! [X0] : sK2 = k1_setfam_1(k2_tarski(sK2,X0)) ),
    inference(backward_demodulation,[],[f2115,f2200])).

fof(f2200,plain,(
    sK2 = sK3 ),
    inference(backward_demodulation,[],[f2116,f2115])).

fof(f2116,plain,(
    ! [X0] : sK3 = k1_setfam_1(k2_tarski(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f2010,f2010,f191])).

fof(f191,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK6(X6,X7,X8),X8)
      | k1_setfam_1(k2_tarski(X6,X7)) = X8
      | r2_hidden(sK6(X6,X7,X8),X6) ) ),
    inference(resolution,[],[f72,f62])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( sP7(sK6(X0,X1,X2),X1,X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k1_setfam_1(k2_tarski(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f66,f47])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sP7(sK6(X0,X1,X2),X1,X0)
      | r2_hidden(sK6(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f2010,plain,(
    ! [X0] : ~ r2_hidden(X0,sK3) ),
    inference(unit_resulting_resolution,[],[f2007,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f2007,plain,(
    v1_xboole_0(sK3) ),
    inference(global_subsumption,[],[f268,f286,f305,f2004])).

fof(f2004,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,sK2) ),
    inference(global_subsumption,[],[f975,f2003])).

fof(f2003,plain,
    ( ~ v3_pre_topc(sK3,sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f2000,f61])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f2000,plain,
    ( ~ sP7(sK1,sK3,sK2)
    | ~ v3_pre_topc(sK3,sK0)
    | ~ v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f1999,f76])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | ~ sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f64,f47])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1999,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ v3_pre_topc(sK2,sK0)
    | ~ v3_pre_topc(sK3,sK0) ),
    inference(global_subsumption,[],[f38,f37,f209,f210,f1996])).

fof(f1996,plain,
    ( ~ r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK3,sK0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f1060,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(definition_unfolding,[],[f59,f47])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v3_pre_topc(k3_xboole_0(X1,X2),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X2,X0)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k3_xboole_0(X1,X2),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).

fof(f1060,plain,
    ( ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0)
    | ~ r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) ),
    inference(resolution,[],[f1009,f258])).

fof(f258,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0) ),
    inference(global_subsumption,[],[f38,f37,f36,f35,f254])).

fof(f254,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f43,f79])).

fof(f79,plain,(
    ~ r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f68,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | m1_subset_1(X1,X0) ) ),
    inference(global_subsumption,[],[f46,f50])).

fof(f50,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

fof(f68,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(definition_unfolding,[],[f33,f47])).

fof(f33,plain,(
    ~ m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f35,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f1009,plain,(
    ! [X0] : m1_subset_1(k1_setfam_1(k2_tarski(X0,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f1000,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1000,plain,(
    ! [X2] : r1_tarski(k1_setfam_1(k2_tarski(X2,sK3)),u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f982])).

fof(f982,plain,(
    ! [X2] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X2,sK3)),u1_struct_0(sK0))
      | r1_tarski(k1_setfam_1(k2_tarski(X2,sK3)),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f291,f247])).

fof(f247,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK5(X2,u1_struct_0(sK0)),sK3)
      | r1_tarski(X2,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f225,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f225,plain,(
    ! [X1] :
      ( r2_hidden(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f211,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f211,plain,(
    r1_tarski(sK3,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f209,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f291,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK5(k1_setfam_1(k2_tarski(X0,X1)),X2),X1)
      | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2) ) ),
    inference(resolution,[],[f145,f63])).

fof(f63,plain,(
    ! [X0,X3,X1] :
      ( ~ sP7(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f145,plain,(
    ! [X4,X2,X3] :
      ( sP7(sK5(k1_setfam_1(k2_tarski(X2,X3)),X4),X3,X2)
      | r1_tarski(k1_setfam_1(k2_tarski(X2,X3)),X4) ) ),
    inference(resolution,[],[f75,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f75,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1)))
      | sP7(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k1_setfam_1(k2_tarski(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f65,f47])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f210,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f36,f37,f38,f35,f203,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_connsp_2(X2,X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f203,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f38,f36,f37,f35,f34,f44])).

fof(f44,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).

fof(f209,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f36,f37,f38,f35,f202,f53])).

fof(f202,plain,(
    m1_connsp_2(sK3,sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f38,f36,f37,f35,f32,f44])).

fof(f32,plain,(
    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f975,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | ~ r2_hidden(sK1,sK2)
    | v3_pre_topc(sK3,sK0) ),
    inference(resolution,[],[f542,f240])).

fof(f240,plain,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v3_pre_topc(sK3,sK0) ),
    inference(global_subsumption,[],[f38,f37,f36,f35,f209,f236])).

fof(f236,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK3,sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(resolution,[],[f42,f98])).

fof(f98,plain,
    ( r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(resolution,[],[f51,f32])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f542,plain,(
    ! [X10] :
      ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,X10)))
      | ~ v3_pre_topc(sK2,sK0)
      | ~ r2_hidden(X10,sK2) ) ),
    inference(global_subsumption,[],[f38,f37,f36,f227,f535])).

fof(f535,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | ~ v2_pre_topc(sK0)
      | ~ r2_hidden(X10,sK2)
      | ~ v3_pre_topc(sK2,sK0)
      | v2_struct_0(sK0)
      | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,X10))) ) ),
    inference(resolution,[],[f253,f210])).

fof(f253,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ l1_pre_topc(X9)
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ v2_pre_topc(X9)
      | ~ r2_hidden(X10,X11)
      | ~ v3_pre_topc(X11,X9)
      | v2_struct_0(X9)
      | ~ v1_xboole_0(u1_struct_0(k9_yellow_6(X9,X10))) ) ),
    inference(resolution,[],[f43,f46])).

fof(f227,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(resolution,[],[f210,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f305,plain,
    ( v3_pre_topc(sK2,sK0)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f239,f83])).

fof(f83,plain,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f49,f32])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f239,plain,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v3_pre_topc(sK2,sK0) ),
    inference(global_subsumption,[],[f38,f37,f36,f35,f210,f235])).

fof(f235,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(resolution,[],[f42,f99])).

fof(f99,plain,
    ( r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(resolution,[],[f51,f34])).

fof(f286,plain,
    ( r2_hidden(sK1,sK3)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f221,f83])).

fof(f221,plain,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | r2_hidden(sK1,sK3) ),
    inference(global_subsumption,[],[f38,f37,f36,f35,f209,f217])).

fof(f217,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK3)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(resolution,[],[f41,f98])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f268,plain,
    ( r2_hidden(sK1,sK2)
    | v1_xboole_0(sK3) ),
    inference(resolution,[],[f220,f83])).

fof(f220,plain,
    ( v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | r2_hidden(sK1,sK2) ),
    inference(global_subsumption,[],[f38,f37,f36,f35,f210,f216])).

fof(f216,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,sK2)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(resolution,[],[f41,f99])).

fof(f2115,plain,(
    ! [X0] : sK2 = k1_setfam_1(k2_tarski(sK3,X0)) ),
    inference(unit_resulting_resolution,[],[f2008,f2010,f323])).

fof(f323,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK6(X3,X4,X5),X3)
      | k1_setfam_1(k2_tarski(X3,X4)) = X5
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f191,f46])).

fof(f2008,plain,(
    v1_xboole_0(sK2) ),
    inference(global_subsumption,[],[f290,f2007])).

fof(f290,plain,
    ( ~ v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f285,f46])).

fof(f285,plain,
    ( r2_hidden(sK1,sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f221,f84])).

fof(f84,plain,
    ( ~ v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f49,f34])).

fof(f2202,plain,(
    ~ m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK2)),u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(backward_demodulation,[],[f68,f2200])).

fof(f34,plain,(
    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n004.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 16:14:08 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (3291)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.50  % (3307)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (3285)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (3284)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (3301)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (3287)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.56  % (3288)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (3286)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (3286)Refutation not found, incomplete strategy% (3286)------------------------------
% 0.21/0.56  % (3286)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (3286)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (3286)Memory used [KB]: 10874
% 0.21/0.56  % (3286)Time elapsed: 0.151 s
% 0.21/0.56  % (3286)------------------------------
% 0.21/0.56  % (3286)------------------------------
% 0.21/0.57  % (3289)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.57  % (3309)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.57  % (3310)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.57  % (3312)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.57  % (3301)Refutation not found, incomplete strategy% (3301)------------------------------
% 0.21/0.57  % (3301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (3301)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (3301)Memory used [KB]: 10618
% 0.21/0.57  % (3301)Time elapsed: 0.148 s
% 0.21/0.57  % (3301)------------------------------
% 0.21/0.57  % (3301)------------------------------
% 0.21/0.57  % (3295)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (3306)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.57  % (3298)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.57  % (3293)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.58  % (3292)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.58  % (3302)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.58  % (3304)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.58  % (3303)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.58  % (3297)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.58  % (3290)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.58  % (3294)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.58  % (3305)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.58  % (3294)Refutation not found, incomplete strategy% (3294)------------------------------
% 0.21/0.58  % (3294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (3294)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (3294)Memory used [KB]: 10618
% 0.21/0.58  % (3294)Time elapsed: 0.169 s
% 0.21/0.58  % (3294)------------------------------
% 0.21/0.58  % (3294)------------------------------
% 0.21/0.58  % (3299)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.58  % (3306)Refutation not found, incomplete strategy% (3306)------------------------------
% 0.21/0.58  % (3306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (3306)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (3306)Memory used [KB]: 10874
% 0.21/0.58  % (3306)Time elapsed: 0.111 s
% 0.21/0.58  % (3306)------------------------------
% 0.21/0.58  % (3306)------------------------------
% 0.21/0.59  % (3300)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.59  % (3313)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.59  % (3296)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.81/0.59  % (3308)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.81/0.60  % (3311)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 2.04/0.63  % (3304)Refutation not found, incomplete strategy% (3304)------------------------------
% 2.04/0.63  % (3304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.04/0.63  % (3304)Termination reason: Refutation not found, incomplete strategy
% 2.04/0.63  
% 2.04/0.63  % (3304)Memory used [KB]: 11001
% 2.04/0.63  % (3304)Time elapsed: 0.196 s
% 2.04/0.63  % (3304)------------------------------
% 2.04/0.63  % (3304)------------------------------
% 2.04/0.70  % (3346)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.04/0.71  % (3347)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.04/0.71  % (3345)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.63/0.74  % (3348)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.63/0.77  % (3349)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 3.14/0.79  % (3308)Refutation found. Thanks to Tanya!
% 3.14/0.79  % SZS status Theorem for theBenchmark
% 3.14/0.79  % SZS output start Proof for theBenchmark
% 3.14/0.81  fof(f2545,plain,(
% 3.14/0.81    $false),
% 3.14/0.81    inference(global_subsumption,[],[f34,f2477])).
% 3.14/0.81  fof(f2477,plain,(
% 3.14/0.81    ~m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.14/0.81    inference(backward_demodulation,[],[f2202,f2371])).
% 3.14/0.81  fof(f2371,plain,(
% 3.14/0.81    ( ! [X0] : (sK2 = k1_setfam_1(k2_tarski(sK2,X0))) )),
% 3.14/0.81    inference(backward_demodulation,[],[f2115,f2200])).
% 3.14/0.81  fof(f2200,plain,(
% 3.14/0.81    sK2 = sK3),
% 3.14/0.81    inference(backward_demodulation,[],[f2116,f2115])).
% 3.14/0.81  fof(f2116,plain,(
% 3.14/0.81    ( ! [X0] : (sK3 = k1_setfam_1(k2_tarski(sK3,X0))) )),
% 3.14/0.81    inference(unit_resulting_resolution,[],[f2010,f2010,f191])).
% 3.14/0.81  fof(f191,plain,(
% 3.14/0.81    ( ! [X6,X8,X7] : (r2_hidden(sK6(X6,X7,X8),X8) | k1_setfam_1(k2_tarski(X6,X7)) = X8 | r2_hidden(sK6(X6,X7,X8),X6)) )),
% 3.14/0.81    inference(resolution,[],[f72,f62])).
% 3.14/0.81  fof(f62,plain,(
% 3.14/0.81    ( ! [X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X0)) )),
% 3.14/0.81    inference(cnf_transformation,[],[f3])).
% 3.14/0.81  fof(f3,axiom,(
% 3.14/0.81    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 3.14/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 3.14/0.81  fof(f72,plain,(
% 3.14/0.81    ( ! [X2,X0,X1] : (sP7(sK6(X0,X1,X2),X1,X0) | r2_hidden(sK6(X0,X1,X2),X2) | k1_setfam_1(k2_tarski(X0,X1)) = X2) )),
% 3.14/0.81    inference(definition_unfolding,[],[f66,f47])).
% 3.14/0.81  fof(f47,plain,(
% 3.14/0.81    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.14/0.81    inference(cnf_transformation,[],[f5])).
% 3.14/0.81  fof(f5,axiom,(
% 3.14/0.81    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.14/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.14/0.81  fof(f66,plain,(
% 3.14/0.81    ( ! [X2,X0,X1] : (sP7(sK6(X0,X1,X2),X1,X0) | r2_hidden(sK6(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 3.14/0.81    inference(cnf_transformation,[],[f3])).
% 3.14/0.81  fof(f2010,plain,(
% 3.14/0.81    ( ! [X0] : (~r2_hidden(X0,sK3)) )),
% 3.14/0.81    inference(unit_resulting_resolution,[],[f2007,f46])).
% 3.14/0.81  fof(f46,plain,(
% 3.14/0.81    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 3.14/0.81    inference(cnf_transformation,[],[f1])).
% 3.14/0.81  fof(f1,axiom,(
% 3.14/0.81    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.14/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 3.14/0.81  fof(f2007,plain,(
% 3.14/0.81    v1_xboole_0(sK3)),
% 3.14/0.81    inference(global_subsumption,[],[f268,f286,f305,f2004])).
% 3.14/0.81  fof(f2004,plain,(
% 3.14/0.81    ~v3_pre_topc(sK2,sK0) | ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,sK2)),
% 3.14/0.81    inference(global_subsumption,[],[f975,f2003])).
% 3.14/0.81  fof(f2003,plain,(
% 3.14/0.81    ~v3_pre_topc(sK3,sK0) | ~v3_pre_topc(sK2,sK0) | ~r2_hidden(sK1,sK3) | ~r2_hidden(sK1,sK2)),
% 3.14/0.81    inference(resolution,[],[f2000,f61])).
% 3.14/0.81  fof(f61,plain,(
% 3.14/0.81    ( ! [X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) )),
% 3.14/0.81    inference(cnf_transformation,[],[f3])).
% 3.14/0.81  fof(f2000,plain,(
% 3.14/0.81    ~sP7(sK1,sK3,sK2) | ~v3_pre_topc(sK3,sK0) | ~v3_pre_topc(sK2,sK0)),
% 3.14/0.81    inference(resolution,[],[f1999,f76])).
% 3.14/0.81  fof(f76,plain,(
% 3.14/0.81    ( ! [X0,X3,X1] : (r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | ~sP7(X3,X1,X0)) )),
% 3.14/0.81    inference(equality_resolution,[],[f74])).
% 3.14/0.81  fof(f74,plain,(
% 3.14/0.81    ( ! [X2,X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 3.14/0.81    inference(definition_unfolding,[],[f64,f47])).
% 3.14/0.81  fof(f64,plain,(
% 3.14/0.81    ( ! [X2,X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.14/0.81    inference(cnf_transformation,[],[f3])).
% 3.14/0.81  fof(f1999,plain,(
% 3.14/0.81    ~r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) | ~v3_pre_topc(sK2,sK0) | ~v3_pre_topc(sK3,sK0)),
% 3.14/0.81    inference(global_subsumption,[],[f38,f37,f209,f210,f1996])).
% 3.14/0.81  fof(f1996,plain,(
% 3.14/0.81    ~r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) | ~l1_pre_topc(sK0) | ~v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK3,sK0) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)),
% 3.14/0.81    inference(resolution,[],[f1060,f70])).
% 3.14/0.81  fof(f70,plain,(
% 3.14/0.81    ( ! [X2,X0,X1] : (v3_pre_topc(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 3.14/0.81    inference(definition_unfolding,[],[f59,f47])).
% 3.14/0.81  fof(f59,plain,(
% 3.14/0.81    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k3_xboole_0(X1,X2),X0)) )),
% 3.14/0.81    inference(cnf_transformation,[],[f29])).
% 3.14/0.81  fof(f29,plain,(
% 3.14/0.81    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.14/0.81    inference(flattening,[],[f28])).
% 3.14/0.81  fof(f28,plain,(
% 3.14/0.81    ! [X0,X1,X2] : (v3_pre_topc(k3_xboole_0(X1,X2),X0) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.14/0.81    inference(ennf_transformation,[],[f10])).
% 3.14/0.81  fof(f10,axiom,(
% 3.14/0.81    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X2,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v3_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k3_xboole_0(X1,X2),X0))),
% 3.14/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_tops_1)).
% 3.14/0.81  fof(f1060,plain,(
% 3.14/0.81    ~v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0) | ~r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3)))),
% 3.14/0.81    inference(resolution,[],[f1009,f258])).
% 3.14/0.81  fof(f258,plain,(
% 3.14/0.81    ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) | ~v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0)),
% 3.14/0.81    inference(global_subsumption,[],[f38,f37,f36,f35,f254])).
% 3.14/0.81  fof(f254,plain,(
% 3.14/0.81    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_setfam_1(k2_tarski(sK2,sK3))) | ~v3_pre_topc(k1_setfam_1(k2_tarski(sK2,sK3)),sK0) | v2_struct_0(sK0)),
% 3.14/0.81    inference(resolution,[],[f43,f79])).
% 3.14/0.81  fof(f79,plain,(
% 3.14/0.81    ~r2_hidden(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.14/0.81    inference(unit_resulting_resolution,[],[f68,f77])).
% 3.14/0.81  fof(f77,plain,(
% 3.14/0.81    ( ! [X0,X1] : (~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 3.14/0.81    inference(global_subsumption,[],[f46,f50])).
% 3.14/0.81  fof(f50,plain,(
% 3.14/0.81    ( ! [X0,X1] : (v1_xboole_0(X0) | ~r2_hidden(X1,X0) | m1_subset_1(X1,X0)) )),
% 3.14/0.81    inference(cnf_transformation,[],[f23])).
% 3.14/0.81  fof(f23,plain,(
% 3.14/0.81    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 3.14/0.81    inference(ennf_transformation,[],[f4])).
% 3.14/0.81  fof(f4,axiom,(
% 3.14/0.81    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 3.14/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).
% 3.14/0.81  fof(f68,plain,(
% 3.14/0.81    ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK3)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.14/0.81    inference(definition_unfolding,[],[f33,f47])).
% 3.14/0.81  fof(f33,plain,(
% 3.14/0.81    ~m1_subset_1(k3_xboole_0(sK2,sK3),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.14/0.81    inference(cnf_transformation,[],[f18])).
% 3.14/0.81  fof(f18,plain,(
% 3.14/0.81    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 3.14/0.81    inference(flattening,[],[f17])).
% 3.14/0.81  fof(f17,plain,(
% 3.14/0.81    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1))) & m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 3.14/0.81    inference(ennf_transformation,[],[f16])).
% 3.14/0.81  fof(f16,negated_conjecture,(
% 3.14/0.81    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.14/0.81    inference(negated_conjecture,[],[f15])).
% 3.14/0.81  fof(f15,conjecture,(
% 3.14/0.81    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k9_yellow_6(X0,X1))) => m1_subset_1(k3_xboole_0(X2,X3),u1_struct_0(k9_yellow_6(X0,X1)))))))),
% 3.14/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_waybel_9)).
% 3.14/0.81  fof(f43,plain,(
% 3.14/0.81    ( ! [X2,X0,X1] : (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~v3_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 3.14/0.81    inference(cnf_transformation,[],[f20])).
% 3.14/0.81  fof(f20,plain,(
% 3.14/0.81    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.14/0.81    inference(flattening,[],[f19])).
% 3.14/0.81  fof(f19,plain,(
% 3.14/0.81    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.14/0.81    inference(ennf_transformation,[],[f12])).
% 3.14/0.81  fof(f12,axiom,(
% 3.14/0.81    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) <=> (v3_pre_topc(X2,X0) & r2_hidden(X1,X2))))))),
% 3.14/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_6)).
% 3.14/0.81  fof(f35,plain,(
% 3.14/0.81    m1_subset_1(sK1,u1_struct_0(sK0))),
% 3.14/0.81    inference(cnf_transformation,[],[f18])).
% 3.14/0.81  fof(f36,plain,(
% 3.14/0.81    ~v2_struct_0(sK0)),
% 3.14/0.81    inference(cnf_transformation,[],[f18])).
% 3.14/0.81  fof(f1009,plain,(
% 3.14/0.81    ( ! [X0] : (m1_subset_1(k1_setfam_1(k2_tarski(X0,sK3)),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 3.14/0.81    inference(unit_resulting_resolution,[],[f1000,f57])).
% 3.14/0.81  fof(f57,plain,(
% 3.14/0.81    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.14/0.81    inference(cnf_transformation,[],[f7])).
% 3.14/0.81  fof(f7,axiom,(
% 3.14/0.81    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.14/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.14/0.81  fof(f1000,plain,(
% 3.14/0.81    ( ! [X2] : (r1_tarski(k1_setfam_1(k2_tarski(X2,sK3)),u1_struct_0(sK0))) )),
% 3.14/0.81    inference(duplicate_literal_removal,[],[f982])).
% 3.14/0.81  fof(f982,plain,(
% 3.14/0.81    ( ! [X2] : (r1_tarski(k1_setfam_1(k2_tarski(X2,sK3)),u1_struct_0(sK0)) | r1_tarski(k1_setfam_1(k2_tarski(X2,sK3)),u1_struct_0(sK0))) )),
% 3.14/0.81    inference(resolution,[],[f291,f247])).
% 3.14/0.81  fof(f247,plain,(
% 3.14/0.81    ( ! [X2] : (~r2_hidden(sK5(X2,u1_struct_0(sK0)),sK3) | r1_tarski(X2,u1_struct_0(sK0))) )),
% 3.14/0.81    inference(resolution,[],[f225,f56])).
% 3.14/0.81  fof(f56,plain,(
% 3.14/0.81    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 3.14/0.81    inference(cnf_transformation,[],[f27])).
% 3.14/0.81  fof(f27,plain,(
% 3.14/0.81    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.14/0.81    inference(ennf_transformation,[],[f2])).
% 3.14/0.81  fof(f2,axiom,(
% 3.14/0.81    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.14/0.81    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 3.14/0.81  fof(f225,plain,(
% 3.14/0.81    ( ! [X1] : (r2_hidden(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,sK3)) )),
% 3.14/0.81    inference(resolution,[],[f211,f54])).
% 3.14/0.81  fof(f54,plain,(
% 3.14/0.81    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 3.14/0.81    inference(cnf_transformation,[],[f27])).
% 3.14/0.81  fof(f211,plain,(
% 3.14/0.81    r1_tarski(sK3,u1_struct_0(sK0))),
% 3.14/0.81    inference(unit_resulting_resolution,[],[f209,f58])).
% 3.14/0.81  fof(f58,plain,(
% 3.14/0.81    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.14/0.81    inference(cnf_transformation,[],[f7])).
% 3.14/0.81  fof(f291,plain,(
% 3.14/0.81    ( ! [X2,X0,X1] : (r2_hidden(sK5(k1_setfam_1(k2_tarski(X0,X1)),X2),X1) | r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X2)) )),
% 3.14/0.81    inference(resolution,[],[f145,f63])).
% 3.14/0.81  fof(f63,plain,(
% 3.14/0.81    ( ! [X0,X3,X1] : (~sP7(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 3.14/0.81    inference(cnf_transformation,[],[f3])).
% 3.14/0.81  fof(f145,plain,(
% 3.14/0.81    ( ! [X4,X2,X3] : (sP7(sK5(k1_setfam_1(k2_tarski(X2,X3)),X4),X3,X2) | r1_tarski(k1_setfam_1(k2_tarski(X2,X3)),X4)) )),
% 3.14/0.81    inference(resolution,[],[f75,f55])).
% 3.14/0.81  fof(f55,plain,(
% 3.14/0.81    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 3.14/0.81    inference(cnf_transformation,[],[f27])).
% 3.14/0.81  fof(f75,plain,(
% 3.14/0.81    ( ! [X0,X3,X1] : (~r2_hidden(X3,k1_setfam_1(k2_tarski(X0,X1))) | sP7(X3,X1,X0)) )),
% 3.14/0.81    inference(equality_resolution,[],[f73])).
% 3.14/0.81  fof(f73,plain,(
% 3.14/0.81    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k1_setfam_1(k2_tarski(X0,X1)) != X2) )),
% 3.14/0.81    inference(definition_unfolding,[],[f65,f47])).
% 3.14/0.81  fof(f65,plain,(
% 3.14/0.81    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 3.14/0.81    inference(cnf_transformation,[],[f3])).
% 3.14/0.81  fof(f210,plain,(
% 3.14/0.81    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.14/0.81    inference(unit_resulting_resolution,[],[f36,f37,f38,f35,f203,f53])).
% 3.14/0.81  fof(f53,plain,(
% 3.14/0.81    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_connsp_2(X2,X0,X1) | v2_struct_0(X0)) )),
% 3.14/0.81    inference(cnf_transformation,[],[f26])).
% 3.14/0.81  fof(f26,plain,(
% 3.14/0.81    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.14/0.81    inference(flattening,[],[f25])).
% 3.14/0.81  fof(f25,plain,(
% 3.14/0.81    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.14/0.81    inference(ennf_transformation,[],[f11])).
% 3.14/0.82  fof(f11,axiom,(
% 3.14/0.82    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.14/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 3.14/0.82  fof(f203,plain,(
% 3.14/0.82    m1_connsp_2(sK2,sK0,sK1)),
% 3.14/0.82    inference(unit_resulting_resolution,[],[f38,f36,f37,f35,f34,f44])).
% 3.14/0.82  fof(f44,plain,(
% 3.14/0.82    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_connsp_2(X2,X0,X1)) )),
% 3.14/0.82    inference(cnf_transformation,[],[f22])).
% 3.14/0.82  fof(f22,plain,(
% 3.14/0.82    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 3.14/0.82    inference(flattening,[],[f21])).
% 3.14/0.82  fof(f21,plain,(
% 3.14/0.82    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 3.14/0.82    inference(ennf_transformation,[],[f14])).
% 3.14/0.82  fof(f14,axiom,(
% 3.14/0.82    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(k9_yellow_6(X0,X1))) => m1_connsp_2(X2,X0,X1))))),
% 3.14/0.82    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_waybel_9)).
% 3.14/0.82  fof(f209,plain,(
% 3.14/0.82    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.14/0.82    inference(unit_resulting_resolution,[],[f36,f37,f38,f35,f202,f53])).
% 3.14/0.82  fof(f202,plain,(
% 3.14/0.82    m1_connsp_2(sK3,sK0,sK1)),
% 3.14/0.82    inference(unit_resulting_resolution,[],[f38,f36,f37,f35,f32,f44])).
% 3.14/0.82  fof(f32,plain,(
% 3.14/0.82    m1_subset_1(sK3,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.14/0.82    inference(cnf_transformation,[],[f18])).
% 3.14/0.82  fof(f37,plain,(
% 3.14/0.82    v2_pre_topc(sK0)),
% 3.14/0.82    inference(cnf_transformation,[],[f18])).
% 3.14/0.82  fof(f38,plain,(
% 3.14/0.82    l1_pre_topc(sK0)),
% 3.14/0.82    inference(cnf_transformation,[],[f18])).
% 3.14/0.82  fof(f975,plain,(
% 3.14/0.82    ~v3_pre_topc(sK2,sK0) | ~r2_hidden(sK1,sK2) | v3_pre_topc(sK3,sK0)),
% 3.14/0.82    inference(resolution,[],[f542,f240])).
% 3.14/0.82  fof(f240,plain,(
% 3.14/0.82    v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | v3_pre_topc(sK3,sK0)),
% 3.14/0.82    inference(global_subsumption,[],[f38,f37,f36,f35,f209,f236])).
% 3.14/0.82  fof(f236,plain,(
% 3.14/0.82    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK3,sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.14/0.82    inference(resolution,[],[f42,f98])).
% 3.14/0.82  fof(f98,plain,(
% 3.14/0.82    r2_hidden(sK3,u1_struct_0(k9_yellow_6(sK0,sK1))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.14/0.82    inference(resolution,[],[f51,f32])).
% 3.14/0.82  fof(f51,plain,(
% 3.14/0.82    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 3.14/0.82    inference(cnf_transformation,[],[f23])).
% 3.14/0.82  fof(f42,plain,(
% 3.14/0.82    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 3.14/0.82    inference(cnf_transformation,[],[f20])).
% 3.14/0.82  fof(f542,plain,(
% 3.14/0.82    ( ! [X10] : (~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,X10))) | ~v3_pre_topc(sK2,sK0) | ~r2_hidden(X10,sK2)) )),
% 3.14/0.82    inference(global_subsumption,[],[f38,f37,f36,f227,f535])).
% 3.14/0.82  fof(f535,plain,(
% 3.14/0.82    ( ! [X10] : (~l1_pre_topc(sK0) | ~m1_subset_1(X10,u1_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~r2_hidden(X10,sK2) | ~v3_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,X10)))) )),
% 3.14/0.82    inference(resolution,[],[f253,f210])).
% 3.14/0.82  fof(f253,plain,(
% 3.14/0.82    ( ! [X10,X11,X9] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(X9))) | ~l1_pre_topc(X9) | ~m1_subset_1(X10,u1_struct_0(X9)) | ~v2_pre_topc(X9) | ~r2_hidden(X10,X11) | ~v3_pre_topc(X11,X9) | v2_struct_0(X9) | ~v1_xboole_0(u1_struct_0(k9_yellow_6(X9,X10)))) )),
% 3.14/0.82    inference(resolution,[],[f43,f46])).
% 3.14/0.82  fof(f227,plain,(
% 3.14/0.82    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2)) )),
% 3.14/0.82    inference(resolution,[],[f210,f60])).
% 3.14/0.83  fof(f60,plain,(
% 3.14/0.83    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 3.14/0.83    inference(cnf_transformation,[],[f31])).
% 3.14/0.83  fof(f31,plain,(
% 3.14/0.83    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.14/0.83    inference(flattening,[],[f30])).
% 3.14/0.83  fof(f30,plain,(
% 3.14/0.83    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.14/0.83    inference(ennf_transformation,[],[f8])).
% 3.14/0.83  fof(f8,axiom,(
% 3.14/0.83    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.14/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 3.14/0.83  fof(f305,plain,(
% 3.14/0.83    v3_pre_topc(sK2,sK0) | v1_xboole_0(sK3)),
% 3.14/0.83    inference(resolution,[],[f239,f83])).
% 3.14/0.83  fof(f83,plain,(
% 3.14/0.83    ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | v1_xboole_0(sK3)),
% 3.14/0.83    inference(resolution,[],[f49,f32])).
% 3.14/0.83  fof(f49,plain,(
% 3.14/0.83    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 3.14/0.83    inference(cnf_transformation,[],[f23])).
% 3.14/0.83  fof(f239,plain,(
% 3.14/0.83    v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | v3_pre_topc(sK2,sK0)),
% 3.14/0.83    inference(global_subsumption,[],[f38,f37,f36,f35,f210,f235])).
% 3.14/0.83  fof(f235,plain,(
% 3.14/0.83    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2,sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.14/0.83    inference(resolution,[],[f42,f99])).
% 3.14/0.83  fof(f99,plain,(
% 3.14/0.83    r2_hidden(sK2,u1_struct_0(k9_yellow_6(sK0,sK1))) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.14/0.83    inference(resolution,[],[f51,f34])).
% 3.14/0.83  fof(f286,plain,(
% 3.14/0.83    r2_hidden(sK1,sK3) | v1_xboole_0(sK3)),
% 3.14/0.83    inference(resolution,[],[f221,f83])).
% 3.14/0.83  fof(f221,plain,(
% 3.14/0.83    v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | r2_hidden(sK1,sK3)),
% 3.14/0.83    inference(global_subsumption,[],[f38,f37,f36,f35,f209,f217])).
% 3.14/0.83  fof(f217,plain,(
% 3.14/0.83    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK3) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.14/0.83    inference(resolution,[],[f41,f98])).
% 3.14/0.83  fof(f41,plain,(
% 3.14/0.83    ( ! [X2,X0,X1] : (~r2_hidden(X2,u1_struct_0(k9_yellow_6(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X2) | v2_struct_0(X0)) )),
% 3.14/0.83    inference(cnf_transformation,[],[f20])).
% 3.14/0.83  fof(f268,plain,(
% 3.14/0.83    r2_hidden(sK1,sK2) | v1_xboole_0(sK3)),
% 3.14/0.83    inference(resolution,[],[f220,f83])).
% 3.14/0.83  fof(f220,plain,(
% 3.14/0.83    v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | r2_hidden(sK1,sK2)),
% 3.14/0.83    inference(global_subsumption,[],[f38,f37,f36,f35,f210,f216])).
% 3.14/0.83  fof(f216,plain,(
% 3.14/0.83    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,sK2) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.14/0.83    inference(resolution,[],[f41,f99])).
% 3.14/0.83  fof(f2115,plain,(
% 3.14/0.83    ( ! [X0] : (sK2 = k1_setfam_1(k2_tarski(sK3,X0))) )),
% 3.14/0.83    inference(unit_resulting_resolution,[],[f2008,f2010,f323])).
% 3.14/0.83  fof(f323,plain,(
% 3.14/0.83    ( ! [X4,X5,X3] : (r2_hidden(sK6(X3,X4,X5),X3) | k1_setfam_1(k2_tarski(X3,X4)) = X5 | ~v1_xboole_0(X5)) )),
% 3.14/0.83    inference(resolution,[],[f191,f46])).
% 3.14/0.83  fof(f2008,plain,(
% 3.14/0.83    v1_xboole_0(sK2)),
% 3.14/0.83    inference(global_subsumption,[],[f290,f2007])).
% 3.14/0.83  fof(f290,plain,(
% 3.14/0.83    ~v1_xboole_0(sK3) | v1_xboole_0(sK2)),
% 3.14/0.83    inference(resolution,[],[f285,f46])).
% 3.14/0.83  fof(f285,plain,(
% 3.14/0.83    r2_hidden(sK1,sK3) | v1_xboole_0(sK2)),
% 3.14/0.83    inference(resolution,[],[f221,f84])).
% 3.14/0.83  fof(f84,plain,(
% 3.14/0.83    ~v1_xboole_0(u1_struct_0(k9_yellow_6(sK0,sK1))) | v1_xboole_0(sK2)),
% 3.14/0.83    inference(resolution,[],[f49,f34])).
% 3.14/0.83  fof(f2202,plain,(
% 3.14/0.83    ~m1_subset_1(k1_setfam_1(k2_tarski(sK2,sK2)),u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.14/0.83    inference(backward_demodulation,[],[f68,f2200])).
% 3.14/0.83  fof(f34,plain,(
% 3.14/0.83    m1_subset_1(sK2,u1_struct_0(k9_yellow_6(sK0,sK1)))),
% 3.14/0.83    inference(cnf_transformation,[],[f18])).
% 3.14/0.83  % SZS output end Proof for theBenchmark
% 3.14/0.83  % (3308)------------------------------
% 3.14/0.83  % (3308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.14/0.83  % (3308)Termination reason: Refutation
% 3.14/0.83  
% 3.14/0.83  % (3308)Memory used [KB]: 9210
% 3.14/0.83  % (3308)Time elapsed: 0.361 s
% 3.14/0.83  % (3308)------------------------------
% 3.14/0.83  % (3308)------------------------------
% 3.14/0.83  % (3283)Success in time 0.465 s
%------------------------------------------------------------------------------
