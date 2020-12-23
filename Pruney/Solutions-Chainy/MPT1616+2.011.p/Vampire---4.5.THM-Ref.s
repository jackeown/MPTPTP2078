%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:45 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 243 expanded)
%              Number of leaves         :   16 (  52 expanded)
%              Depth                    :   16
%              Number of atoms          :  235 ( 835 expanded)
%              Number of equality atoms :   21 ( 104 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f650,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f402,f615,f649])).

fof(f649,plain,(
    ~ spl9_4 ),
    inference(avatar_contradiction_clause,[],[f644])).

fof(f644,plain,
    ( $false
    | ~ spl9_4 ),
    inference(subsumption_resolution,[],[f172,f640])).

fof(f640,plain,
    ( ! [X0] : r1_tarski(u1_struct_0(sK0),X0)
    | ~ spl9_4 ),
    inference(forward_demodulation,[],[f633,f41])).

fof(f41,plain,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

fof(f633,plain,
    ( ! [X0] : r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))),X0)
    | ~ spl9_4 ),
    inference(resolution,[],[f626,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X0)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).

fof(f626,plain,
    ( ! [X1] : ~ r2_hidden(X1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_4 ),
    inference(forward_demodulation,[],[f619,f41])).

fof(f619,plain,
    ( ! [X1] : ~ r2_hidden(X1,k3_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))
    | ~ spl9_4 ),
    inference(resolution,[],[f616,f84])).

fof(f84,plain,(
    ! [X2,X0] :
      ( r2_hidden(sK7(X0,X2),X0)
      | ~ r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK7(X0,X2),X0)
      | ~ r2_hidden(X2,X1)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f616,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_4 ),
    inference(resolution,[],[f401,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f401,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f399])).

fof(f399,plain,
    ( spl9_4
  <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f172,plain,(
    ~ r1_tarski(u1_struct_0(sK0),sK4(u1_struct_0(sK0))) ),
    inference(resolution,[],[f119,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f119,plain,(
    r2_hidden(sK4(u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f117,f64])).

fof(f64,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f117,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f86,f93])).

fof(f93,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f38,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).

fof(f86,plain,
    ( ~ l1_struct_0(sK0)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f36,f63])).

fof(f63,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f615,plain,(
    ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f610])).

fof(f610,plain,
    ( $false
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f193,f588])).

fof(f588,plain,
    ( r1_tarski(sK5(u1_pre_topc(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl9_3 ),
    inference(resolution,[],[f578,f192])).

fof(f192,plain,(
    r2_hidden(sK5(u1_pre_topc(sK0),u1_struct_0(sK0)),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f163,f68])).

fof(f163,plain,(
    ~ r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) ),
    inference(global_subsumption,[],[f150,f158])).

fof(f158,plain,
    ( ~ r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))
    | u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0)) ),
    inference(resolution,[],[f139,f72])).

fof(f72,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f139,plain,(
    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0))) ),
    inference(resolution,[],[f92,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(X0,k3_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f92,plain,(
    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(global_subsumption,[],[f38,f89])).

fof(f89,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f37,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).

fof(f37,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f150,plain,(
    u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0)) ),
    inference(global_subsumption,[],[f92,f149])).

fof(f149,plain,
    ( ~ r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0)) ),
    inference(inner_rewriting,[],[f148])).

fof(f148,plain,
    ( ~ r2_hidden(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0))
    | u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0)) ),
    inference(global_subsumption,[],[f138,f147])).

fof(f147,plain,
    ( u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0))
    | v1_xboole_0(u1_pre_topc(sK0))
    | ~ r2_hidden(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0)) ),
    inference(superposition,[],[f39,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ r2_hidden(k3_tarski(X0),X0)
      | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k3_tarski(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k3_tarski(X0),X0)
       => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

fof(f39,plain,(
    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f138,plain,(
    ~ v1_xboole_0(u1_pre_topc(sK0)) ),
    inference(resolution,[],[f92,f65])).

fof(f578,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK0))
        | r1_tarski(X1,u1_struct_0(sK0)) )
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f566,f41])).

fof(f566,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,u1_pre_topc(sK0))
        | r1_tarski(X1,k3_tarski(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl9_3 ),
    inference(resolution,[],[f421,f66])).

fof(f421,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,u1_pre_topc(sK0)) )
    | ~ spl9_3 ),
    inference(forward_demodulation,[],[f416,f41])).

fof(f416,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,u1_pre_topc(sK0))
        | r2_hidden(X2,k3_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )
    | ~ spl9_3 ),
    inference(resolution,[],[f397,f83])).

fof(f83,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,k3_tarski(X0)) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X3,X0)
      | r2_hidden(X2,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f397,plain,
    ( r2_hidden(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl9_3
  <=> r2_hidden(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f193,plain,(
    ~ r1_tarski(sK5(u1_pre_topc(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    inference(resolution,[],[f163,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(sK5(X0,X1),X1)
      | r1_tarski(k3_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f402,plain,
    ( spl9_3
    | spl9_4 ),
    inference(avatar_split_clause,[],[f167,f399,f395])).

fof(f167,plain,
    ( v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | r2_hidden(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f94,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f94,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f38,f44])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 16:35:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (15427)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.45  % (15420)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.49  % (15419)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.49  % (15421)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.49  % (15410)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.50  % (15412)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.50  % (15413)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.50  % (15411)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.50  % (15433)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.50  % (15429)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.50  % (15408)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.51  % (15423)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.51  % (15417)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.51  % (15409)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.51  % (15422)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.51  % (15431)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.51  % (15409)Refutation not found, incomplete strategy% (15409)------------------------------
% 0.19/0.51  % (15409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (15409)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (15409)Memory used [KB]: 10618
% 0.19/0.51  % (15409)Time elapsed: 0.084 s
% 0.19/0.51  % (15409)------------------------------
% 0.19/0.51  % (15409)------------------------------
% 0.19/0.51  % (15424)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.52  % (15414)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.52  % (15418)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.52  % (15415)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.52  % (15430)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.52  % (15428)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.52  % (15426)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.53  % (15432)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.54  % (15425)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.54  % (15416)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.56  % (15428)Refutation found. Thanks to Tanya!
% 0.19/0.56  % SZS status Theorem for theBenchmark
% 0.19/0.56  % SZS output start Proof for theBenchmark
% 0.19/0.56  fof(f650,plain,(
% 0.19/0.56    $false),
% 0.19/0.56    inference(avatar_sat_refutation,[],[f402,f615,f649])).
% 0.19/0.56  fof(f649,plain,(
% 0.19/0.56    ~spl9_4),
% 0.19/0.56    inference(avatar_contradiction_clause,[],[f644])).
% 0.19/0.56  fof(f644,plain,(
% 0.19/0.56    $false | ~spl9_4),
% 0.19/0.56    inference(subsumption_resolution,[],[f172,f640])).
% 0.19/0.56  fof(f640,plain,(
% 0.19/0.56    ( ! [X0] : (r1_tarski(u1_struct_0(sK0),X0)) ) | ~spl9_4),
% 0.19/0.56    inference(forward_demodulation,[],[f633,f41])).
% 0.19/0.56  fof(f41,plain,(
% 0.19/0.56    ( ! [X0] : (k3_tarski(k1_zfmisc_1(X0)) = X0) )),
% 0.19/0.56    inference(cnf_transformation,[],[f6])).
% 0.19/0.56  fof(f6,axiom,(
% 0.19/0.56    ! [X0] : k3_tarski(k1_zfmisc_1(X0)) = X0),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).
% 0.19/0.56  fof(f633,plain,(
% 0.19/0.56    ( ! [X0] : (r1_tarski(k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))),X0)) ) | ~spl9_4),
% 0.19/0.56    inference(resolution,[],[f626,f68])).
% 0.19/0.56  fof(f68,plain,(
% 0.19/0.56    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X0) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.19/0.56    inference(cnf_transformation,[],[f32])).
% 0.19/0.56  fof(f32,plain,(
% 0.19/0.56    ! [X0,X1] : (r1_tarski(k3_tarski(X0),X1) | ? [X2] : (~r1_tarski(X2,X1) & r2_hidden(X2,X0)))),
% 0.19/0.56    inference(ennf_transformation,[],[f5])).
% 0.19/0.56  fof(f5,axiom,(
% 0.19/0.56    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) => r1_tarski(X2,X1)) => r1_tarski(k3_tarski(X0),X1))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_zfmisc_1)).
% 0.19/0.56  fof(f626,plain,(
% 0.19/0.56    ( ! [X1] : (~r2_hidden(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl9_4),
% 0.19/0.56    inference(forward_demodulation,[],[f619,f41])).
% 0.19/0.56  fof(f619,plain,(
% 0.19/0.56    ( ! [X1] : (~r2_hidden(X1,k3_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ) | ~spl9_4),
% 0.19/0.56    inference(resolution,[],[f616,f84])).
% 0.19/0.56  fof(f84,plain,(
% 0.19/0.56    ( ! [X2,X0] : (r2_hidden(sK7(X0,X2),X0) | ~r2_hidden(X2,k3_tarski(X0))) )),
% 0.19/0.56    inference(equality_resolution,[],[f77])).
% 0.19/0.56  fof(f77,plain,(
% 0.19/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK7(X0,X2),X0) | ~r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 0.19/0.56    inference(cnf_transformation,[],[f3])).
% 0.19/0.56  fof(f3,axiom,(
% 0.19/0.56    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.19/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 0.19/0.56  fof(f616,plain,(
% 0.19/0.56    ( ! [X0] : (~r2_hidden(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl9_4),
% 0.19/0.56    inference(resolution,[],[f401,f65])).
% 0.19/0.57  fof(f65,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f1])).
% 0.19/0.57  fof(f1,axiom,(
% 0.19/0.57    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.57  fof(f401,plain,(
% 0.19/0.57    v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl9_4),
% 0.19/0.57    inference(avatar_component_clause,[],[f399])).
% 0.19/0.57  fof(f399,plain,(
% 0.19/0.57    spl9_4 <=> v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.19/0.57  fof(f172,plain,(
% 0.19/0.57    ~r1_tarski(u1_struct_0(sK0),sK4(u1_struct_0(sK0)))),
% 0.19/0.57    inference(resolution,[],[f119,f79])).
% 0.19/0.57  fof(f79,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f33])).
% 0.19/0.57  fof(f33,plain,(
% 0.19/0.57    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.19/0.57    inference(ennf_transformation,[],[f10])).
% 0.19/0.57  fof(f10,axiom,(
% 0.19/0.57    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.19/0.57  fof(f119,plain,(
% 0.19/0.57    r2_hidden(sK4(u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.19/0.57    inference(resolution,[],[f117,f64])).
% 0.19/0.57  fof(f64,plain,(
% 0.19/0.57    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f1])).
% 0.19/0.57  fof(f117,plain,(
% 0.19/0.57    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.57    inference(global_subsumption,[],[f86,f93])).
% 0.19/0.57  fof(f93,plain,(
% 0.19/0.57    l1_struct_0(sK0)),
% 0.19/0.57    inference(resolution,[],[f38,f43])).
% 0.19/0.57  fof(f43,plain,(
% 0.19/0.57    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f23])).
% 0.19/0.57  fof(f23,plain,(
% 0.19/0.57    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.19/0.57    inference(ennf_transformation,[],[f12])).
% 0.19/0.57  fof(f12,axiom,(
% 0.19/0.57    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.19/0.57  fof(f38,plain,(
% 0.19/0.57    l1_pre_topc(sK0)),
% 0.19/0.57    inference(cnf_transformation,[],[f20])).
% 0.19/0.57  fof(f20,plain,(
% 0.19/0.57    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.57    inference(flattening,[],[f19])).
% 0.19/0.57  fof(f19,plain,(
% 0.19/0.57    ? [X0] : (u1_struct_0(X0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.57    inference(ennf_transformation,[],[f17])).
% 0.19/0.57  fof(f17,negated_conjecture,(
% 0.19/0.57    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.19/0.57    inference(negated_conjecture,[],[f16])).
% 0.19/0.57  fof(f16,conjecture,(
% 0.19/0.57    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => u1_struct_0(X0) = k4_yellow_0(k2_yellow_1(u1_pre_topc(X0))))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_yellow_1)).
% 0.19/0.57  fof(f86,plain,(
% 0.19/0.57    ~l1_struct_0(sK0) | ~v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.57    inference(resolution,[],[f36,f63])).
% 0.19/0.57  fof(f63,plain,(
% 0.19/0.57    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 0.19/0.57    inference(cnf_transformation,[],[f28])).
% 0.19/0.57  fof(f28,plain,(
% 0.19/0.57    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.19/0.57    inference(flattening,[],[f27])).
% 0.19/0.57  fof(f27,plain,(
% 0.19/0.57    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.19/0.57    inference(ennf_transformation,[],[f14])).
% 0.19/0.57  fof(f14,axiom,(
% 0.19/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.19/0.57  fof(f36,plain,(
% 0.19/0.57    ~v2_struct_0(sK0)),
% 0.19/0.57    inference(cnf_transformation,[],[f20])).
% 0.19/0.57  fof(f615,plain,(
% 0.19/0.57    ~spl9_3),
% 0.19/0.57    inference(avatar_contradiction_clause,[],[f610])).
% 0.19/0.57  fof(f610,plain,(
% 0.19/0.57    $false | ~spl9_3),
% 0.19/0.57    inference(subsumption_resolution,[],[f193,f588])).
% 0.19/0.57  fof(f588,plain,(
% 0.19/0.57    r1_tarski(sK5(u1_pre_topc(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) | ~spl9_3),
% 0.19/0.57    inference(resolution,[],[f578,f192])).
% 0.19/0.57  fof(f192,plain,(
% 0.19/0.57    r2_hidden(sK5(u1_pre_topc(sK0),u1_struct_0(sK0)),u1_pre_topc(sK0))),
% 0.19/0.57    inference(resolution,[],[f163,f68])).
% 0.19/0.57  fof(f163,plain,(
% 0.19/0.57    ~r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0))),
% 0.19/0.57    inference(global_subsumption,[],[f150,f158])).
% 0.19/0.57  fof(f158,plain,(
% 0.19/0.57    ~r1_tarski(k3_tarski(u1_pre_topc(sK0)),u1_struct_0(sK0)) | u1_struct_0(sK0) = k3_tarski(u1_pre_topc(sK0))),
% 0.19/0.57    inference(resolution,[],[f139,f72])).
% 0.19/0.57  fof(f72,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.19/0.57    inference(cnf_transformation,[],[f2])).
% 0.19/0.57  fof(f2,axiom,(
% 0.19/0.57    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.57  fof(f139,plain,(
% 0.19/0.57    r1_tarski(u1_struct_0(sK0),k3_tarski(u1_pre_topc(sK0)))),
% 0.19/0.57    inference(resolution,[],[f92,f66])).
% 0.19/0.57  fof(f66,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(X0,k3_tarski(X1))) )),
% 0.19/0.57    inference(cnf_transformation,[],[f29])).
% 0.19/0.57  fof(f29,plain,(
% 0.19/0.57    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.19/0.57    inference(ennf_transformation,[],[f4])).
% 0.19/0.57  fof(f4,axiom,(
% 0.19/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.19/0.57  fof(f92,plain,(
% 0.19/0.57    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 0.19/0.57    inference(global_subsumption,[],[f38,f89])).
% 0.19/0.57  fof(f89,plain,(
% 0.19/0.57    ~l1_pre_topc(sK0) | r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 0.19/0.57    inference(resolution,[],[f37,f62])).
% 0.19/0.57  fof(f62,plain,(
% 0.19/0.57    ( ! [X0] : (~l1_pre_topc(X0) | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~v2_pre_topc(X0)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f26])).
% 0.19/0.57  fof(f26,plain,(
% 0.19/0.57    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : (r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | ~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : (r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.57    inference(flattening,[],[f25])).
% 0.19/0.57  fof(f25,plain,(
% 0.19/0.57    ! [X0] : ((v2_pre_topc(X0) <=> (! [X1] : (! [X2] : ((r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0)) | (~r2_hidden(X2,u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & ! [X3] : ((r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)) | ~r1_tarski(X3,u1_pre_topc(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.57    inference(ennf_transformation,[],[f18])).
% 0.19/0.57  fof(f18,plain,(
% 0.19/0.57    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X3,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X3),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.19/0.57    inference(rectify,[],[f11])).
% 0.19/0.57  fof(f11,axiom,(
% 0.19/0.57    ! [X0] : (l1_pre_topc(X0) => (v2_pre_topc(X0) <=> (! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r2_hidden(X2,u1_pre_topc(X0)) & r2_hidden(X1,u1_pre_topc(X0))) => r2_hidden(k9_subset_1(u1_struct_0(X0),X1,X2),u1_pre_topc(X0))))) & ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (r1_tarski(X1,u1_pre_topc(X0)) => r2_hidden(k5_setfam_1(u1_struct_0(X0),X1),u1_pre_topc(X0)))) & r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_pre_topc)).
% 0.19/0.57  fof(f37,plain,(
% 0.19/0.57    v2_pre_topc(sK0)),
% 0.19/0.57    inference(cnf_transformation,[],[f20])).
% 0.19/0.57  fof(f150,plain,(
% 0.19/0.57    u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0))),
% 0.19/0.57    inference(global_subsumption,[],[f92,f149])).
% 0.19/0.57  fof(f149,plain,(
% 0.19/0.57    ~r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0))),
% 0.19/0.57    inference(inner_rewriting,[],[f148])).
% 0.19/0.57  fof(f148,plain,(
% 0.19/0.57    ~r2_hidden(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0)) | u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0))),
% 0.19/0.57    inference(global_subsumption,[],[f138,f147])).
% 0.19/0.57  fof(f147,plain,(
% 0.19/0.57    u1_struct_0(sK0) != k3_tarski(u1_pre_topc(sK0)) | v1_xboole_0(u1_pre_topc(sK0)) | ~r2_hidden(k3_tarski(u1_pre_topc(sK0)),u1_pre_topc(sK0))),
% 0.19/0.57    inference(superposition,[],[f39,f42])).
% 0.19/0.57  fof(f42,plain,(
% 0.19/0.57    ( ! [X0] : (v1_xboole_0(X0) | ~r2_hidden(k3_tarski(X0),X0) | k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))) )),
% 0.19/0.57    inference(cnf_transformation,[],[f22])).
% 0.19/0.57  fof(f22,plain,(
% 0.19/0.57    ! [X0] : (k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0) | v1_xboole_0(X0))),
% 0.19/0.57    inference(flattening,[],[f21])).
% 0.19/0.57  fof(f21,plain,(
% 0.19/0.57    ! [X0] : ((k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0)) | ~r2_hidden(k3_tarski(X0),X0)) | v1_xboole_0(X0))),
% 0.19/0.57    inference(ennf_transformation,[],[f15])).
% 0.19/0.57  fof(f15,axiom,(
% 0.19/0.57    ! [X0] : (~v1_xboole_0(X0) => (r2_hidden(k3_tarski(X0),X0) => k3_tarski(X0) = k4_yellow_0(k2_yellow_1(X0))))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).
% 0.19/0.57  fof(f39,plain,(
% 0.19/0.57    u1_struct_0(sK0) != k4_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))),
% 0.19/0.57    inference(cnf_transformation,[],[f20])).
% 0.19/0.57  fof(f138,plain,(
% 0.19/0.57    ~v1_xboole_0(u1_pre_topc(sK0))),
% 0.19/0.57    inference(resolution,[],[f92,f65])).
% 0.19/0.57  fof(f578,plain,(
% 0.19/0.57    ( ! [X1] : (~r2_hidden(X1,u1_pre_topc(sK0)) | r1_tarski(X1,u1_struct_0(sK0))) ) | ~spl9_3),
% 0.19/0.57    inference(forward_demodulation,[],[f566,f41])).
% 0.19/0.57  fof(f566,plain,(
% 0.19/0.57    ( ! [X1] : (~r2_hidden(X1,u1_pre_topc(sK0)) | r1_tarski(X1,k3_tarski(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl9_3),
% 0.19/0.57    inference(resolution,[],[f421,f66])).
% 0.19/0.57  fof(f421,plain,(
% 0.19/0.57    ( ! [X2] : (r2_hidden(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,u1_pre_topc(sK0))) ) | ~spl9_3),
% 0.19/0.57    inference(forward_demodulation,[],[f416,f41])).
% 0.19/0.57  fof(f416,plain,(
% 0.19/0.57    ( ! [X2] : (~r2_hidden(X2,u1_pre_topc(sK0)) | r2_hidden(X2,k3_tarski(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))) ) | ~spl9_3),
% 0.19/0.57    inference(resolution,[],[f397,f83])).
% 0.19/0.57  fof(f83,plain,(
% 0.19/0.57    ( ! [X2,X0,X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,k3_tarski(X0))) )),
% 0.19/0.57    inference(equality_resolution,[],[f78])).
% 0.19/0.57  fof(f78,plain,(
% 0.19/0.57    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,X3) | ~r2_hidden(X3,X0) | r2_hidden(X2,X1) | k3_tarski(X0) != X1) )),
% 0.19/0.57    inference(cnf_transformation,[],[f3])).
% 0.19/0.57  fof(f397,plain,(
% 0.19/0.57    r2_hidden(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl9_3),
% 0.19/0.57    inference(avatar_component_clause,[],[f395])).
% 0.19/0.57  fof(f395,plain,(
% 0.19/0.57    spl9_3 <=> r2_hidden(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.19/0.57  fof(f193,plain,(
% 0.19/0.57    ~r1_tarski(sK5(u1_pre_topc(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))),
% 0.19/0.57    inference(resolution,[],[f163,f69])).
% 0.19/0.57  fof(f69,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~r1_tarski(sK5(X0,X1),X1) | r1_tarski(k3_tarski(X0),X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f32])).
% 0.19/0.57  fof(f402,plain,(
% 0.19/0.57    spl9_3 | spl9_4),
% 0.19/0.57    inference(avatar_split_clause,[],[f167,f399,f395])).
% 0.19/0.57  fof(f167,plain,(
% 0.19/0.57    v1_xboole_0(k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.57    inference(resolution,[],[f94,f67])).
% 0.19/0.57  fof(f67,plain,(
% 0.19/0.57    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.19/0.57    inference(cnf_transformation,[],[f31])).
% 0.19/0.57  fof(f31,plain,(
% 0.19/0.57    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.19/0.57    inference(flattening,[],[f30])).
% 0.19/0.57  fof(f30,plain,(
% 0.19/0.57    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.19/0.57    inference(ennf_transformation,[],[f8])).
% 0.19/0.57  fof(f8,axiom,(
% 0.19/0.57    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).
% 0.19/0.57  fof(f94,plain,(
% 0.19/0.57    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.57    inference(resolution,[],[f38,f44])).
% 0.19/0.57  fof(f44,plain,(
% 0.19/0.57    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.19/0.57    inference(cnf_transformation,[],[f24])).
% 0.19/0.57  fof(f24,plain,(
% 0.19/0.57    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.57    inference(ennf_transformation,[],[f13])).
% 0.19/0.57  fof(f13,axiom,(
% 0.19/0.57    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.19/0.57  % SZS output end Proof for theBenchmark
% 0.19/0.57  % (15428)------------------------------
% 0.19/0.57  % (15428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.57  % (15428)Termination reason: Refutation
% 0.19/0.57  
% 0.19/0.57  % (15428)Memory used [KB]: 11129
% 0.19/0.57  % (15428)Time elapsed: 0.163 s
% 0.19/0.57  % (15428)------------------------------
% 0.19/0.57  % (15428)------------------------------
% 0.19/0.57  % (15407)Success in time 0.219 s
%------------------------------------------------------------------------------
