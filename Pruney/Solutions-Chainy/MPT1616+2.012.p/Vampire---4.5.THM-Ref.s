%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:45 EST 2020

% Result     : Theorem 1.89s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 252 expanded)
%              Number of leaves         :   16 (  54 expanded)
%              Depth                    :   16
%              Number of atoms          :  224 ( 896 expanded)
%              Number of equality atoms :   20 ( 104 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1014,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f380,f987,f1013])).

fof(f1013,plain,(
    ~ spl10_6 ),
    inference(avatar_contradiction_clause,[],[f1006])).

fof(f1006,plain,
    ( $false
    | ~ spl10_6 ),
    inference(subsumption_resolution,[],[f278,f1000])).

fof(f1000,plain,
    ( ! [X0] : r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),X0)
    | ~ spl10_6 ),
    inference(forward_demodulation,[],[f993,f34])).

fof(f34,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f993,plain,
    ( ! [X0] : r1_tarski(k3_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))),X0)
    | ~ spl10_6 ),
    inference(resolution,[],[f989,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(k3_tarski(X0),X1)
      | ? [X2] :
          ( ~ r1_tarski(X2,X1)
          & r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => r1_tarski(X2,X1) )
     => r1_tarski(k3_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f989,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_6 ),
    inference(resolution,[],[f379,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f379,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f377])).

fof(f377,plain,
    ( spl10_6
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f278,plain,(
    ~ r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),sK4(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f179,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f179,plain,(
    r2_hidden(sK4(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f177,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f177,plain,(
    ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(global_subsumption,[],[f132,f174])).

fof(f174,plain,
    ( ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))
    | sP9(u1_pre_topc(sK0)) ),
    inference(resolution,[],[f87,f79])).

fof(f79,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | sP9(X1) ) ),
    inference(cnf_transformation,[],[f79_D])).

fof(f79_D,plain,(
    ! [X1] :
      ( ! [X2] :
          ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
          | ~ v1_xboole_0(X2) )
    <=> ~ sP9(X1) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).

fof(f87,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f32,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f132,plain,(
    ~ sP9(u1_pre_topc(sK0)) ),
    inference(resolution,[],[f86,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ sP9(X1) ) ),
    inference(general_splitting,[],[f73,f79_D])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f86,plain,(
    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(global_subsumption,[],[f32,f83])).

% (9904)Refutation not found, incomplete strategy% (9904)------------------------------
% (9904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (9904)Termination reason: Refutation not found, incomplete strategy

% (9904)Memory used [KB]: 6140
% (9904)Time elapsed: 0.184 s
% (9904)------------------------------
% (9904)------------------------------
fof(f83,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f31,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(rectify,[],[f11])).

fof(f11,axiom,(
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

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f987,plain,(
    ~ spl10_5 ),
    inference(avatar_contradiction_clause,[],[f980])).

fof(f980,plain,
    ( $false
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f188,f932])).

fof(f932,plain,
    ( r1_tarski(sK5(u1_pre_topc(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl10_5 ),
    inference(resolution,[],[f913,f187])).

fof(f187,plain,(
    r2_hidden(sK5(u1_pre_topc(sK0),u1_struct_0(sK0)),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f154,f59])).

fof(f154,plain,(
    ~ r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f143,f149])).

fof(f149,plain,
    ( ~ r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) ),
    inference(resolution,[],[f127,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f127,plain,(
    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) ),
    inference(resolution,[],[f86,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f143,plain,(
    u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0)) ),
    inference(global_subsumption,[],[f86,f142])).

fof(f142,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0)) ),
    inference(inner_rewriting,[],[f141])).

fof(f141,plain,
    ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0)) ),
    inference(global_subsumption,[],[f126,f140])).

fof(f140,plain,
    ( u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0))
    | v1_xboole_0(u1_pre_topc(sK0))
    | ~ r2_hidden(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0)) ),
    inference(superposition,[],[f33,f35])).

fof(f35,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f33,plain,(
    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f126,plain,(
    ~ v1_xboole_0(u1_pre_topc(sK0)) ),
    inference(resolution,[],[f86,f56])).

fof(f913,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK0))
        | r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl10_5 ),
    inference(forward_demodulation,[],[f894,f34])).

fof(f894,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK0))
        | r1_tarski(X1,k3_tarski(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl10_5 ),
    inference(resolution,[],[f400,f58])).

fof(f400,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,u1_pre_topc(sK0)) )
    | ~ spl10_5 ),
    inference(forward_demodulation,[],[f393,f34])).

fof(f393,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK0))
        | r2_hidden(X1,k3_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )
    | ~ spl10_5 ),
    inference(resolution,[],[f375,f76])).

fof(f76,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
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

fof(f375,plain,
    ( r2_hidden(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f373])).

fof(f373,plain,
    ( spl10_5
  <=> r2_hidden(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f188,plain,(
    ~ r1_tarski(sK5(u1_pre_topc(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f154,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK5(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f380,plain,
    ( spl10_5
    | spl10_6 ),
    inference(avatar_split_clause,[],[f175,f377,f373])).

fof(f175,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f87,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:43:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (9897)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (9898)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (9896)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (9896)Refutation not found, incomplete strategy% (9896)------------------------------
% 0.21/0.51  % (9896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9916)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (9904)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (9919)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.51  % (9903)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (9896)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (9896)Memory used [KB]: 10618
% 0.21/0.51  % (9896)Time elapsed: 0.093 s
% 0.21/0.51  % (9896)------------------------------
% 0.21/0.51  % (9896)------------------------------
% 0.21/0.52  % (9913)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (9914)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (9909)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (9907)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (9920)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (9899)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (9911)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (9905)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.53  % (9918)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (9910)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.53  % (9917)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (9906)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (9902)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.54  % (9895)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.54  % (9901)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (9895)Refutation not found, incomplete strategy% (9895)------------------------------
% 0.21/0.54  % (9895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9895)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9895)Memory used [KB]: 10618
% 0.21/0.54  % (9895)Time elapsed: 0.116 s
% 0.21/0.54  % (9895)------------------------------
% 0.21/0.54  % (9895)------------------------------
% 0.21/0.54  % (9900)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.54  % (9901)Refutation not found, incomplete strategy% (9901)------------------------------
% 0.21/0.54  % (9901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9901)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9901)Memory used [KB]: 10618
% 0.21/0.54  % (9901)Time elapsed: 0.090 s
% 0.21/0.54  % (9901)------------------------------
% 0.21/0.54  % (9901)------------------------------
% 0.21/0.55  % (9908)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.56  % (9912)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.56  % (9908)Refutation not found, incomplete strategy% (9908)------------------------------
% 0.21/0.56  % (9908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9908)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9908)Memory used [KB]: 6140
% 0.21/0.56  % (9908)Time elapsed: 0.133 s
% 0.21/0.56  % (9908)------------------------------
% 0.21/0.56  % (9908)------------------------------
% 0.21/0.57  % (9915)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.89/0.62  % (9915)Refutation found. Thanks to Tanya!
% 1.89/0.62  % SZS status Theorem for theBenchmark
% 1.89/0.62  % SZS output start Proof for theBenchmark
% 1.89/0.62  fof(f1014,plain,(
% 1.89/0.62    $false),
% 1.89/0.62    inference(avatar_sat_refutation,[],[f380,f987,f1013])).
% 1.89/0.62  fof(f1013,plain,(
% 1.89/0.62    ~spl10_6),
% 1.89/0.62    inference(avatar_contradiction_clause,[],[f1006])).
% 1.89/0.62  fof(f1006,plain,(
% 1.89/0.62    $false | ~spl10_6),
% 1.89/0.62    inference(subsumption_resolution,[],[f278,f1000])).
% 1.89/0.62  fof(f1000,plain,(
% 1.89/0.62    ( ! [X0] : (r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),X0)) ) | ~spl10_6),
% 1.89/0.62    inference(forward_demodulation,[],[f993,f34])).
% 1.89/0.62  fof(f34,plain,(
% 1.89/0.62    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 1.89/0.62    inference(cnf_transformation,[],[f6])).
% 1.89/0.62  fof(f6,axiom,(
% 1.89/0.62    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 1.89/0.62  fof(f993,plain,(
% 1.89/0.62    ( ! [X0] : (r1_tarski(k3_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))),X0)) ) | ~spl10_6),
% 1.89/0.62    inference(resolution,[],[f989,f59])).
% 1.89/0.62  fof(f59,plain,(
% 1.89/0.62    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f27])).
% 1.89/0.62  fof(f27,plain,(
% 1.89/0.62    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f5])).
% 1.89/0.62  fof(f5,axiom,(
% 1.89/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 1.89/0.62  fof(f989,plain,(
% 1.89/0.62    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl10_6),
% 1.89/0.62    inference(resolution,[],[f379,f56])).
% 1.89/0.62  fof(f56,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f1])).
% 1.89/0.62  fof(f1,axiom,(
% 1.89/0.62    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.89/0.62  fof(f379,plain,(
% 1.89/0.62    v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl10_6),
% 1.89/0.62    inference(avatar_component_clause,[],[f377])).
% 1.89/0.62  fof(f377,plain,(
% 1.89/0.62    spl10_6 <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.89/0.62    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 1.89/0.62  fof(f278,plain,(
% 1.89/0.62    ~r1_tarski(k1_zfmisc_1(u1_struct_0(sK0)),sK4(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.89/0.62    inference(resolution,[],[f179,f72])).
% 1.89/0.62  fof(f72,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f28])).
% 1.89/0.62  fof(f28,plain,(
% 1.89/0.62    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.89/0.62    inference(ennf_transformation,[],[f10])).
% 1.89/0.62  fof(f10,axiom,(
% 1.89/0.62    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.89/0.62  fof(f179,plain,(
% 1.89/0.62    r2_hidden(sK4(k1_zfmisc_1(u1_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.62    inference(resolution,[],[f177,f55])).
% 1.89/0.62  fof(f55,plain,(
% 1.89/0.62    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f1])).
% 1.89/0.62  fof(f177,plain,(
% 1.89/0.62    ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.89/0.62    inference(global_subsumption,[],[f132,f174])).
% 1.89/0.62  fof(f174,plain,(
% 1.89/0.62    ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(sK0))) | sP9(u1_pre_topc(sK0))),
% 1.89/0.62    inference(resolution,[],[f87,f79])).
% 1.89/0.62  fof(f79,plain,(
% 1.89/0.62    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | sP9(X1)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f79_D])).
% 1.89/0.62  fof(f79_D,plain,(
% 1.89/0.62    ( ! [X1] : (( ! [X2] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) ) <=> ~sP9(X1)) )),
% 1.89/0.62    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP9])])).
% 1.89/0.62  fof(f87,plain,(
% 1.89/0.62    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.89/0.62    inference(resolution,[],[f32,f36])).
% 1.89/0.62  fof(f36,plain,(
% 1.89/0.62    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 1.89/0.62    inference(cnf_transformation,[],[f21])).
% 1.89/0.62  fof(f21,plain,(
% 1.89/0.62    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.89/0.62    inference(ennf_transformation,[],[f12])).
% 1.89/0.62  fof(f12,axiom,(
% 1.89/0.62    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 1.89/0.62  fof(f32,plain,(
% 1.89/0.62    l1_pre_topc(sK0)),
% 1.89/0.62    inference(cnf_transformation,[],[f18])).
% 1.89/0.62  fof(f18,plain,(
% 1.89/0.62    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.89/0.62    inference(flattening,[],[f17])).
% 1.89/0.62  fof(f17,plain,(
% 1.89/0.62    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.89/0.62    inference(ennf_transformation,[],[f15])).
% 1.89/0.62  fof(f15,negated_conjecture,(
% 1.89/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.89/0.62    inference(negated_conjecture,[],[f14])).
% 1.89/0.62  fof(f14,conjecture,(
% 1.89/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_yellow_1)).
% 1.89/0.62  fof(f132,plain,(
% 1.89/0.62    ~sP9(u1_pre_topc(sK0))),
% 1.89/0.62    inference(resolution,[],[f86,f80])).
% 1.89/0.62  fof(f80,plain,(
% 1.89/0.62    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~sP9(X1)) )),
% 1.89/0.62    inference(general_splitting,[],[f73,f79_D])).
% 1.89/0.62  fof(f73,plain,(
% 1.89/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 1.89/0.62    inference(cnf_transformation,[],[f29])).
% 1.89/0.62  fof(f29,plain,(
% 1.89/0.62    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.89/0.62    inference(ennf_transformation,[],[f9])).
% 1.89/0.62  fof(f9,axiom,(
% 1.89/0.62    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.89/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.89/0.62  fof(f86,plain,(
% 1.89/0.62    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 1.89/0.62    inference(global_subsumption,[],[f32,f83])).
% 1.89/0.62  % (9904)Refutation not found, incomplete strategy% (9904)------------------------------
% 1.89/0.62  % (9904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.62  % (9904)Termination reason: Refutation not found, incomplete strategy
% 1.89/0.62  
% 1.89/0.62  % (9904)Memory used [KB]: 6140
% 1.89/0.62  % (9904)Time elapsed: 0.184 s
% 1.89/0.62  % (9904)------------------------------
% 1.89/0.62  % (9904)------------------------------
% 2.11/0.63  fof(f83,plain,(
% 2.11/0.63    ~l1_pre_topc(sK0) | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 2.11/0.63    inference(resolution,[],[f31,f54])).
% 2.11/0.63  fof(f54,plain,(
% 2.11/0.63    ( ! [X0] : (~l1_pre_topc(X0) | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0)) )),
% 2.11/0.63    inference(cnf_transformation,[],[f23])).
% 2.11/0.63  fof(f23,plain,(
% 2.11/0.63    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.63    inference(flattening,[],[f22])).
% 2.11/0.63  fof(f22,plain,(
% 2.11/0.63    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 2.11/0.63    inference(ennf_transformation,[],[f16])).
% 2.11/0.63  fof(f16,plain,(
% 2.11/0.63    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.11/0.63    inference(rectify,[],[f11])).
% 2.11/0.63  fof(f11,axiom,(
% 2.11/0.63    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 2.11/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_pre_topc)).
% 2.11/0.63  fof(f31,plain,(
% 2.11/0.63    v2_pre_topc(sK0)),
% 2.11/0.63    inference(cnf_transformation,[],[f18])).
% 2.11/0.63  fof(f987,plain,(
% 2.11/0.63    ~spl10_5),
% 2.11/0.63    inference(avatar_contradiction_clause,[],[f980])).
% 2.11/0.63  fof(f980,plain,(
% 2.11/0.63    $false | ~spl10_5),
% 2.11/0.63    inference(subsumption_resolution,[],[f188,f932])).
% 2.11/0.63  fof(f932,plain,(
% 2.11/0.63    r1_tarski(sK5(u1_pre_topc(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl10_5),
% 2.11/0.63    inference(resolution,[],[f913,f187])).
% 2.11/0.63  fof(f187,plain,(
% 2.11/0.63    r2_hidden(sK5(u1_pre_topc(sK0),u1_struct_0(sK0)),u1_pre_topc(sK0))),
% 2.11/0.63    inference(resolution,[],[f154,f59])).
% 2.11/0.63  fof(f154,plain,(
% 2.11/0.63    ~r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))),
% 2.11/0.63    inference(global_subsumption,[],[f143,f149])).
% 2.11/0.63  fof(f149,plain,(
% 2.11/0.63    ~r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) | u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))),
% 2.11/0.63    inference(resolution,[],[f127,f63])).
% 2.11/0.63  fof(f63,plain,(
% 2.11/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 2.11/0.63    inference(cnf_transformation,[],[f2])).
% 2.11/0.63  fof(f2,axiom,(
% 2.11/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.11/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.11/0.63  fof(f127,plain,(
% 2.11/0.63    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))),
% 2.11/0.63    inference(resolution,[],[f86,f58])).
% 2.11/0.63  fof(f58,plain,(
% 2.11/0.63    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 2.11/0.63    inference(cnf_transformation,[],[f26])).
% 2.11/0.63  fof(f26,plain,(
% 2.11/0.63    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 2.11/0.63    inference(ennf_transformation,[],[f4])).
% 2.11/0.63  fof(f4,axiom,(
% 2.11/0.63    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 2.11/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 2.11/0.63  fof(f143,plain,(
% 2.11/0.63    u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0))),
% 2.11/0.63    inference(global_subsumption,[],[f86,f142])).
% 2.11/0.63  fof(f142,plain,(
% 2.11/0.63    ~r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0))),
% 2.11/0.63    inference(inner_rewriting,[],[f141])).
% 2.11/0.63  fof(f141,plain,(
% 2.11/0.63    ~r2_hidden(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0)) | u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0))),
% 2.11/0.63    inference(global_subsumption,[],[f126,f140])).
% 2.11/0.63  fof(f140,plain,(
% 2.11/0.63    u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0)) | v1_xboole_0(u1_pre_topc(sK0)) | ~r2_hidden(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0))),
% 2.11/0.63    inference(superposition,[],[f33,f35])).
% 2.11/0.63  fof(f35,plain,(
% 2.11/0.63    ( ! [X0] : (v1_xboole_0(X0) | ~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))) )),
% 2.11/0.63    inference(cnf_transformation,[],[f20])).
% 2.11/0.63  fof(f20,plain,(
% 2.11/0.63    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 2.11/0.63    inference(flattening,[],[f19])).
% 2.11/0.63  fof(f19,plain,(
% 2.11/0.63    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 2.11/0.63    inference(ennf_transformation,[],[f13])).
% 2.11/0.63  fof(f13,axiom,(
% 2.11/0.63    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 2.11/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).
% 2.11/0.63  fof(f33,plain,(
% 2.11/0.63    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 2.11/0.63    inference(cnf_transformation,[],[f18])).
% 2.11/0.63  fof(f126,plain,(
% 2.11/0.63    ~v1_xboole_0(u1_pre_topc(sK0))),
% 2.11/0.63    inference(resolution,[],[f86,f56])).
% 2.11/0.63  fof(f913,plain,(
% 2.11/0.63    ( ! [X1] : (~r2_hidden(X1,u1_pre_topc(sK0)) | r1_tarski(X1,u1_struct_0(sK0))) ) | ~spl10_5),
% 2.11/0.63    inference(forward_demodulation,[],[f894,f34])).
% 2.11/0.63  fof(f894,plain,(
% 2.11/0.63    ( ! [X1] : (~r2_hidden(X1,u1_pre_topc(sK0)) | r1_tarski(X1,k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl10_5),
% 2.11/0.63    inference(resolution,[],[f400,f58])).
% 2.11/0.63  fof(f400,plain,(
% 2.11/0.63    ( ! [X1] : (r2_hidden(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,u1_pre_topc(sK0))) ) | ~spl10_5),
% 2.11/0.63    inference(forward_demodulation,[],[f393,f34])).
% 2.11/0.63  fof(f393,plain,(
% 2.11/0.63    ( ! [X1] : (~r2_hidden(X1,u1_pre_topc(sK0)) | r2_hidden(X1,k3_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ) | ~spl10_5),
% 2.11/0.63    inference(resolution,[],[f375,f76])).
% 2.11/0.63  fof(f76,plain,(
% 2.11/0.63    ( ! [X2,X0,X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,k3_tarski(X0))) )),
% 2.11/0.63    inference(equality_resolution,[],[f69])).
% 2.11/0.63  fof(f69,plain,(
% 2.11/0.63    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 2.11/0.63    inference(cnf_transformation,[],[f3])).
% 2.11/0.63  fof(f3,axiom,(
% 2.11/0.63    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 2.11/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 2.11/0.63  fof(f375,plain,(
% 2.11/0.63    r2_hidden(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl10_5),
% 2.11/0.63    inference(avatar_component_clause,[],[f373])).
% 2.14/0.63  fof(f373,plain,(
% 2.14/0.63    spl10_5 <=> r2_hidden(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 2.14/0.63  fof(f188,plain,(
% 2.14/0.63    ~r1_tarski(sK5(u1_pre_topc(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))),
% 2.14/0.63    inference(resolution,[],[f154,f60])).
% 2.14/0.63  fof(f60,plain,(
% 2.14/0.63    ( ! [X0,X1] : (~r1_tarski(sK5(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f27])).
% 2.14/0.63  fof(f380,plain,(
% 2.14/0.63    spl10_5 | spl10_6),
% 2.14/0.63    inference(avatar_split_clause,[],[f175,f377,f373])).
% 2.14/0.63  fof(f175,plain,(
% 2.14/0.63    v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.14/0.63    inference(resolution,[],[f87,f57])).
% 2.14/0.63  fof(f57,plain,(
% 2.14/0.63    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f25])).
% 2.14/0.63  fof(f25,plain,(
% 2.14/0.63    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.14/0.63    inference(flattening,[],[f24])).
% 2.14/0.63  fof(f24,plain,(
% 2.14/0.63    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.14/0.63    inference(ennf_transformation,[],[f7])).
% 2.14/0.63  fof(f7,axiom,(
% 2.14/0.63    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 2.14/0.64  % SZS output end Proof for theBenchmark
% 2.14/0.64  % (9915)------------------------------
% 2.14/0.64  % (9915)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.64  % (9915)Termination reason: Refutation
% 2.14/0.64  
% 2.14/0.64  % (9915)Memory used [KB]: 11385
% 2.14/0.64  % (9915)Time elapsed: 0.210 s
% 2.14/0.64  % (9915)------------------------------
% 2.14/0.64  % (9915)------------------------------
% 2.14/0.64  % (9894)Success in time 0.27 s
%------------------------------------------------------------------------------
