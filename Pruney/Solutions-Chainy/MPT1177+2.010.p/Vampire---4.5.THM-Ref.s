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
% DateTime   : Thu Dec  3 13:10:18 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  109 (1626 expanded)
%              Number of leaves         :   10 ( 285 expanded)
%              Depth                    :   31
%              Number of atoms          :  489 (11892 expanded)
%              Number of equality atoms :   43 ( 136 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f775,plain,(
    $false ),
    inference(subsumption_resolution,[],[f772,f58])).

fof(f58,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
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

fof(f772,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f732,f761])).

fof(f761,plain,(
    k1_xboole_0 = k1_funct_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f732,f62])).

fof(f62,plain,(
    ! [X0] :
      ( r1_tarski(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f50,f39])).

fof(f39,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( r2_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( k1_xboole_0 != X0
     => r2_xboole_0(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f732,plain,(
    ~ r1_tarski(k1_xboole_0,k1_funct_1(sK1,u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f498,f726])).

fof(f726,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f399,f720])).

fof(f720,plain,(
    m1_orders_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f719,f60])).

fof(f60,plain,(
    ! [X1] : ~ r2_xboole_0(X1,X1) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f719,plain,
    ( r2_xboole_0(sK2,sK2)
    | m1_orders_2(sK2,sK0,sK2) ),
    inference(forward_demodulation,[],[f645,f644])).

fof(f644,plain,(
    sK2 = sK3 ),
    inference(subsumption_resolution,[],[f643,f407])).

fof(f407,plain,
    ( ~ r1_tarski(sK3,sK2)
    | sK2 = sK3 ),
    inference(resolution,[],[f401,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f401,plain,(
    r1_tarski(sK2,sK3) ),
    inference(subsumption_resolution,[],[f400,f50])).

fof(f400,plain,
    ( r1_tarski(sK2,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f382,f29])).

fof(f29,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).

fof(f382,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK3)
      | r1_tarski(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f381,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f381,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_orders_2(X0,sK0,sK3)
      | r1_tarski(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f380,f38])).

fof(f38,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f380,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_2(X0,sK0,sK3)
      | r1_tarski(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f379,f37])).

fof(f37,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f379,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_2(X0,sK0,sK3)
      | r1_tarski(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f378,f36])).

fof(f36,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f378,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_2(X0,sK0,sK3)
      | r1_tarski(X0,sK3) ) ),
    inference(subsumption_resolution,[],[f376,f35])).

fof(f35,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f376,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_2(X0,sK0,sK3)
      | r1_tarski(X0,sK3) ) ),
    inference(resolution,[],[f374,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f374,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f373,f31])).

fof(f31,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f373,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f372,f33])).

fof(f33,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f372,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f371,f34])).

fof(f371,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f370,f37])).

fof(f370,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f369,f36])).

fof(f369,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f368,f35])).

fof(f368,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f46,f38])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f643,plain,
    ( sK2 = sK3
    | r1_tarski(sK3,sK2) ),
    inference(resolution,[],[f642,f394])).

fof(f394,plain,(
    ! [X0] :
      ( ~ m1_orders_2(X0,sK0,sK2)
      | r1_tarski(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f393,f34])).

fof(f393,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_orders_2(X0,sK0,sK2)
      | r1_tarski(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f392,f38])).

fof(f392,plain,(
    ! [X0] :
      ( ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_2(X0,sK0,sK2)
      | r1_tarski(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f391,f37])).

fof(f391,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_2(X0,sK0,sK2)
      | r1_tarski(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f390,f36])).

fof(f390,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_2(X0,sK0,sK2)
      | r1_tarski(X0,sK2) ) ),
    inference(subsumption_resolution,[],[f388,f35])).

fof(f388,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_2(X0,sK0,sK2)
      | r1_tarski(X0,sK2) ) ),
    inference(resolution,[],[f375,f42])).

fof(f375,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f373,f32])).

fof(f32,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f642,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | sK2 = sK3 ),
    inference(subsumption_resolution,[],[f640,f402])).

fof(f402,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3 ),
    inference(resolution,[],[f401,f78])).

fof(f78,plain,
    ( ~ r1_tarski(sK2,sK3)
    | sK2 = sK3
    | ~ m1_orders_2(sK2,sK0,sK3) ),
    inference(resolution,[],[f52,f30])).

fof(f30,plain,
    ( ~ r2_xboole_0(sK2,sK3)
    | ~ m1_orders_2(sK2,sK0,sK3) ),
    inference(cnf_transformation,[],[f15])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f640,plain,
    ( sK2 = sK3
    | m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3) ),
    inference(resolution,[],[f637,f32])).

fof(f637,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | sK3 = X0
      | m1_orders_2(sK3,sK0,X0)
      | m1_orders_2(X0,sK0,sK3) ) ),
    inference(resolution,[],[f622,f31])).

fof(f622,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(X1,sK0,sK1)
      | ~ m2_orders_2(X0,sK0,sK1)
      | X0 = X1
      | m1_orders_2(X1,sK0,X0)
      | m1_orders_2(X0,sK0,X1) ) ),
    inference(resolution,[],[f494,f33])).

fof(f494,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | ~ m2_orders_2(X2,sK0,X0)
      | X1 = X2
      | m1_orders_2(X2,sK0,X1)
      | m1_orders_2(X1,sK0,X2) ) ),
    inference(subsumption_resolution,[],[f493,f34])).

fof(f493,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | ~ m2_orders_2(X2,sK0,X0)
      | X1 = X2
      | m1_orders_2(X2,sK0,X1)
      | m1_orders_2(X1,sK0,X2) ) ),
    inference(subsumption_resolution,[],[f492,f37])).

fof(f492,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | ~ m2_orders_2(X2,sK0,X0)
      | X1 = X2
      | m1_orders_2(X2,sK0,X1)
      | m1_orders_2(X1,sK0,X2) ) ),
    inference(subsumption_resolution,[],[f491,f36])).

fof(f491,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | ~ m2_orders_2(X2,sK0,X0)
      | X1 = X2
      | m1_orders_2(X2,sK0,X1)
      | m1_orders_2(X1,sK0,X2) ) ),
    inference(subsumption_resolution,[],[f490,f35])).

fof(f490,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | ~ m2_orders_2(X2,sK0,X0)
      | X1 = X2
      | m1_orders_2(X2,sK0,X1)
      | m1_orders_2(X1,sK0,X2) ) ),
    inference(resolution,[],[f44,f38])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m2_orders_2(X3,X0,X1)
      | X2 = X3
      | m1_orders_2(X3,X0,X2)
      | m1_orders_2(X2,X0,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).

fof(f645,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | r2_xboole_0(sK2,sK3) ),
    inference(backward_demodulation,[],[f29,f644])).

fof(f399,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f398,f34])).

fof(f398,plain,
    ( v2_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f397,f38])).

fof(f397,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f396,f37])).

fof(f396,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f395,f36])).

fof(f395,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2) ),
    inference(subsumption_resolution,[],[f389,f35])).

fof(f389,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k1_xboole_0 = sK2
    | ~ m1_orders_2(sK2,sK0,sK2) ),
    inference(resolution,[],[f375,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k1_xboole_0 = X1
      | ~ m1_orders_2(X1,X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k1_xboole_0 != X1
              | m1_orders_2(X1,X0,X1) )
            & ( ~ m1_orders_2(X1,X0,X1)
              | k1_xboole_0 = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k1_xboole_0 != X1
              | m1_orders_2(X1,X0,X1) )
            & ( ~ m1_orders_2(X1,X0,X1)
              | k1_xboole_0 = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
            & ~ ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).

fof(f498,plain,(
    ~ r1_tarski(sK2,k1_funct_1(sK1,u1_struct_0(sK0))) ),
    inference(resolution,[],[f489,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f489,plain,(
    r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2) ),
    inference(resolution,[],[f487,f32])).

fof(f487,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0) ) ),
    inference(resolution,[],[f434,f33])).

fof(f434,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(subsumption_resolution,[],[f433,f34])).

fof(f433,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(subsumption_resolution,[],[f432,f37])).

fof(f432,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(subsumption_resolution,[],[f431,f36])).

fof(f431,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(subsumption_resolution,[],[f430,f35])).

fof(f430,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(resolution,[],[f43,f38])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:44:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (1677)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (1694)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (1685)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (1694)Refutation not found, incomplete strategy% (1694)------------------------------
% 0.21/0.54  % (1694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (1694)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.56  
% 1.42/0.56  % (1694)Memory used [KB]: 10746
% 1.42/0.56  % (1694)Time elapsed: 0.122 s
% 1.42/0.56  % (1694)------------------------------
% 1.42/0.56  % (1694)------------------------------
% 1.42/0.56  % (1673)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.59/0.57  % (1690)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.59/0.57  % (1697)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.59/0.57  % (1681)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.59/0.57  % (1680)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.59/0.57  % (1689)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.59/0.58  % (1673)Refutation not found, incomplete strategy% (1673)------------------------------
% 1.59/0.58  % (1673)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (1680)Refutation not found, incomplete strategy% (1680)------------------------------
% 1.59/0.58  % (1680)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (1689)Refutation not found, incomplete strategy% (1689)------------------------------
% 1.59/0.58  % (1689)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (1689)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (1689)Memory used [KB]: 10618
% 1.59/0.58  % (1689)Time elapsed: 0.139 s
% 1.59/0.58  % (1689)------------------------------
% 1.59/0.58  % (1689)------------------------------
% 1.59/0.58  % (1679)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.59/0.58  % (1681)Refutation not found, incomplete strategy% (1681)------------------------------
% 1.59/0.58  % (1681)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.58  % (1680)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.58  
% 1.59/0.58  % (1680)Memory used [KB]: 10746
% 1.59/0.58  % (1680)Time elapsed: 0.144 s
% 1.59/0.58  % (1680)------------------------------
% 1.59/0.58  % (1680)------------------------------
% 1.59/0.59  % (1681)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.59  
% 1.59/0.59  % (1681)Memory used [KB]: 10746
% 1.59/0.59  % (1681)Time elapsed: 0.148 s
% 1.59/0.59  % (1681)------------------------------
% 1.59/0.59  % (1681)------------------------------
% 1.59/0.59  % (1672)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.59/0.59  % (1673)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.59  
% 1.59/0.59  % (1673)Memory used [KB]: 10874
% 1.59/0.59  % (1673)Time elapsed: 0.145 s
% 1.59/0.59  % (1673)------------------------------
% 1.59/0.59  % (1673)------------------------------
% 1.59/0.59  % (1700)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.59/0.60  % (1688)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.59/0.60  % (1677)Refutation found. Thanks to Tanya!
% 1.59/0.60  % SZS status Theorem for theBenchmark
% 1.59/0.60  % SZS output start Proof for theBenchmark
% 1.59/0.60  fof(f775,plain,(
% 1.59/0.60    $false),
% 1.59/0.60    inference(subsumption_resolution,[],[f772,f58])).
% 1.59/0.60  fof(f58,plain,(
% 1.59/0.60    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.59/0.60    inference(equality_resolution,[],[f48])).
% 1.59/0.60  fof(f48,plain,(
% 1.59/0.60    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.59/0.60    inference(cnf_transformation,[],[f3])).
% 1.59/0.60  fof(f3,axiom,(
% 1.59/0.60    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.59/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.59/0.60  fof(f772,plain,(
% 1.59/0.60    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.59/0.60    inference(backward_demodulation,[],[f732,f761])).
% 1.59/0.60  fof(f761,plain,(
% 1.59/0.60    k1_xboole_0 = k1_funct_1(sK1,u1_struct_0(sK0))),
% 1.59/0.60    inference(resolution,[],[f732,f62])).
% 1.59/0.60  fof(f62,plain,(
% 1.59/0.60    ( ! [X0] : (r1_tarski(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 1.59/0.60    inference(resolution,[],[f50,f39])).
% 1.59/0.60  fof(f39,plain,(
% 1.59/0.60    ( ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0) )),
% 1.59/0.60    inference(cnf_transformation,[],[f16])).
% 1.59/0.60  fof(f16,plain,(
% 1.59/0.60    ! [X0] : (r2_xboole_0(k1_xboole_0,X0) | k1_xboole_0 = X0)),
% 1.59/0.60    inference(ennf_transformation,[],[f4])).
% 1.59/0.60  fof(f4,axiom,(
% 1.59/0.60    ! [X0] : (k1_xboole_0 != X0 => r2_xboole_0(k1_xboole_0,X0))),
% 1.59/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_xboole_1)).
% 1.59/0.60  fof(f50,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f2])).
% 1.59/0.60  fof(f2,axiom,(
% 1.59/0.60    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.59/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.59/0.60  fof(f732,plain,(
% 1.59/0.60    ~r1_tarski(k1_xboole_0,k1_funct_1(sK1,u1_struct_0(sK0)))),
% 1.59/0.60    inference(backward_demodulation,[],[f498,f726])).
% 1.59/0.60  fof(f726,plain,(
% 1.59/0.60    k1_xboole_0 = sK2),
% 1.59/0.60    inference(global_subsumption,[],[f399,f720])).
% 1.59/0.60  fof(f720,plain,(
% 1.59/0.60    m1_orders_2(sK2,sK0,sK2)),
% 1.59/0.60    inference(subsumption_resolution,[],[f719,f60])).
% 1.59/0.60  fof(f60,plain,(
% 1.59/0.60    ( ! [X1] : (~r2_xboole_0(X1,X1)) )),
% 1.59/0.60    inference(equality_resolution,[],[f51])).
% 1.59/0.60  fof(f51,plain,(
% 1.59/0.60    ( ! [X0,X1] : (X0 != X1 | ~r2_xboole_0(X0,X1)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f2])).
% 1.59/0.60  fof(f719,plain,(
% 1.59/0.60    r2_xboole_0(sK2,sK2) | m1_orders_2(sK2,sK0,sK2)),
% 1.59/0.60    inference(forward_demodulation,[],[f645,f644])).
% 1.59/0.60  fof(f644,plain,(
% 1.59/0.60    sK2 = sK3),
% 1.59/0.60    inference(subsumption_resolution,[],[f643,f407])).
% 1.59/0.60  fof(f407,plain,(
% 1.59/0.60    ~r1_tarski(sK3,sK2) | sK2 = sK3),
% 1.59/0.60    inference(resolution,[],[f401,f49])).
% 1.59/0.60  fof(f49,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.59/0.60    inference(cnf_transformation,[],[f3])).
% 1.59/0.60  fof(f401,plain,(
% 1.59/0.60    r1_tarski(sK2,sK3)),
% 1.59/0.60    inference(subsumption_resolution,[],[f400,f50])).
% 1.59/0.60  fof(f400,plain,(
% 1.59/0.60    r1_tarski(sK2,sK3) | r2_xboole_0(sK2,sK3)),
% 1.59/0.60    inference(resolution,[],[f382,f29])).
% 1.59/0.60  fof(f29,plain,(
% 1.59/0.60    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 1.59/0.60    inference(cnf_transformation,[],[f15])).
% 1.59/0.60  fof(f15,plain,(
% 1.59/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.59/0.60    inference(flattening,[],[f14])).
% 1.59/0.60  fof(f14,plain,(
% 1.59/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.59/0.60    inference(ennf_transformation,[],[f12])).
% 1.59/0.60  fof(f12,negated_conjecture,(
% 1.59/0.60    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.59/0.60    inference(negated_conjecture,[],[f11])).
% 1.59/0.60  fof(f11,conjecture,(
% 1.59/0.60    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 1.59/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).
% 1.59/0.60  fof(f382,plain,(
% 1.59/0.60    ( ! [X0] : (~m1_orders_2(X0,sK0,sK3) | r1_tarski(X0,sK3)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f381,f34])).
% 1.59/0.60  fof(f34,plain,(
% 1.59/0.60    ~v2_struct_0(sK0)),
% 1.59/0.60    inference(cnf_transformation,[],[f15])).
% 1.59/0.60  fof(f381,plain,(
% 1.59/0.60    ( ! [X0] : (v2_struct_0(sK0) | ~m1_orders_2(X0,sK0,sK3) | r1_tarski(X0,sK3)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f380,f38])).
% 1.59/0.60  fof(f38,plain,(
% 1.59/0.60    l1_orders_2(sK0)),
% 1.59/0.60    inference(cnf_transformation,[],[f15])).
% 1.59/0.60  fof(f380,plain,(
% 1.59/0.60    ( ! [X0] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_2(X0,sK0,sK3) | r1_tarski(X0,sK3)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f379,f37])).
% 1.59/0.60  fof(f37,plain,(
% 1.59/0.60    v5_orders_2(sK0)),
% 1.59/0.60    inference(cnf_transformation,[],[f15])).
% 1.59/0.60  fof(f379,plain,(
% 1.59/0.60    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_2(X0,sK0,sK3) | r1_tarski(X0,sK3)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f378,f36])).
% 1.59/0.60  fof(f36,plain,(
% 1.59/0.60    v4_orders_2(sK0)),
% 1.59/0.60    inference(cnf_transformation,[],[f15])).
% 1.59/0.60  fof(f378,plain,(
% 1.59/0.60    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_2(X0,sK0,sK3) | r1_tarski(X0,sK3)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f376,f35])).
% 1.59/0.60  fof(f35,plain,(
% 1.59/0.60    v3_orders_2(sK0)),
% 1.59/0.60    inference(cnf_transformation,[],[f15])).
% 1.59/0.60  fof(f376,plain,(
% 1.59/0.60    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_2(X0,sK0,sK3) | r1_tarski(X0,sK3)) )),
% 1.59/0.60    inference(resolution,[],[f374,f42])).
% 1.59/0.60  fof(f42,plain,(
% 1.59/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f20])).
% 1.59/0.60  fof(f20,plain,(
% 1.59/0.60    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.59/0.60    inference(flattening,[],[f19])).
% 1.59/0.60  fof(f19,plain,(
% 1.59/0.60    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.59/0.60    inference(ennf_transformation,[],[f7])).
% 1.59/0.60  fof(f7,axiom,(
% 1.59/0.60    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 1.59/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).
% 1.59/0.60  fof(f374,plain,(
% 1.59/0.60    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/0.60    inference(resolution,[],[f373,f31])).
% 1.59/0.60  fof(f31,plain,(
% 1.59/0.60    m2_orders_2(sK3,sK0,sK1)),
% 1.59/0.60    inference(cnf_transformation,[],[f15])).
% 1.59/0.60  fof(f373,plain,(
% 1.59/0.60    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.59/0.60    inference(resolution,[],[f372,f33])).
% 1.59/0.60  fof(f33,plain,(
% 1.59/0.60    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 1.59/0.60    inference(cnf_transformation,[],[f15])).
% 1.59/0.60  fof(f372,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f371,f34])).
% 1.59/0.60  fof(f371,plain,(
% 1.59/0.60    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f370,f37])).
% 1.59/0.60  fof(f370,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f369,f36])).
% 1.59/0.60  fof(f369,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f368,f35])).
% 1.59/0.60  fof(f368,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.59/0.60    inference(resolution,[],[f46,f38])).
% 1.59/0.60  fof(f46,plain,(
% 1.59/0.60    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.59/0.60    inference(cnf_transformation,[],[f26])).
% 1.59/0.60  fof(f26,plain,(
% 1.59/0.60    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.59/0.60    inference(flattening,[],[f25])).
% 1.59/0.60  fof(f25,plain,(
% 1.59/0.60    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.59/0.60    inference(ennf_transformation,[],[f13])).
% 1.59/0.60  fof(f13,plain,(
% 1.59/0.60    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.59/0.60    inference(pure_predicate_removal,[],[f6])).
% 1.59/0.60  fof(f6,axiom,(
% 1.59/0.60    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 1.59/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 1.59/0.60  fof(f643,plain,(
% 1.59/0.60    sK2 = sK3 | r1_tarski(sK3,sK2)),
% 1.59/0.60    inference(resolution,[],[f642,f394])).
% 1.59/0.60  fof(f394,plain,(
% 1.59/0.60    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | r1_tarski(X0,sK2)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f393,f34])).
% 1.59/0.60  fof(f393,plain,(
% 1.59/0.60    ( ! [X0] : (v2_struct_0(sK0) | ~m1_orders_2(X0,sK0,sK2) | r1_tarski(X0,sK2)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f392,f38])).
% 1.59/0.60  fof(f392,plain,(
% 1.59/0.60    ( ! [X0] : (~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_2(X0,sK0,sK2) | r1_tarski(X0,sK2)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f391,f37])).
% 1.59/0.60  fof(f391,plain,(
% 1.59/0.60    ( ! [X0] : (~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_2(X0,sK0,sK2) | r1_tarski(X0,sK2)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f390,f36])).
% 1.59/0.60  fof(f390,plain,(
% 1.59/0.60    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_2(X0,sK0,sK2) | r1_tarski(X0,sK2)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f388,f35])).
% 1.59/0.60  fof(f388,plain,(
% 1.59/0.60    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_2(X0,sK0,sK2) | r1_tarski(X0,sK2)) )),
% 1.59/0.60    inference(resolution,[],[f375,f42])).
% 1.59/0.60  fof(f375,plain,(
% 1.59/0.60    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.59/0.60    inference(resolution,[],[f373,f32])).
% 1.59/0.60  fof(f32,plain,(
% 1.59/0.60    m2_orders_2(sK2,sK0,sK1)),
% 1.59/0.60    inference(cnf_transformation,[],[f15])).
% 1.59/0.60  fof(f642,plain,(
% 1.59/0.60    m1_orders_2(sK3,sK0,sK2) | sK2 = sK3),
% 1.59/0.60    inference(subsumption_resolution,[],[f640,f402])).
% 1.59/0.60  fof(f402,plain,(
% 1.59/0.60    ~m1_orders_2(sK2,sK0,sK3) | sK2 = sK3),
% 1.59/0.60    inference(resolution,[],[f401,f78])).
% 1.59/0.60  fof(f78,plain,(
% 1.59/0.60    ~r1_tarski(sK2,sK3) | sK2 = sK3 | ~m1_orders_2(sK2,sK0,sK3)),
% 1.59/0.60    inference(resolution,[],[f52,f30])).
% 1.59/0.60  fof(f30,plain,(
% 1.59/0.60    ~r2_xboole_0(sK2,sK3) | ~m1_orders_2(sK2,sK0,sK3)),
% 1.59/0.60    inference(cnf_transformation,[],[f15])).
% 1.59/0.60  fof(f52,plain,(
% 1.59/0.60    ( ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f2])).
% 1.59/0.60  fof(f640,plain,(
% 1.59/0.60    sK2 = sK3 | m1_orders_2(sK3,sK0,sK2) | m1_orders_2(sK2,sK0,sK3)),
% 1.59/0.60    inference(resolution,[],[f637,f32])).
% 1.59/0.60  fof(f637,plain,(
% 1.59/0.60    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | sK3 = X0 | m1_orders_2(sK3,sK0,X0) | m1_orders_2(X0,sK0,sK3)) )),
% 1.59/0.60    inference(resolution,[],[f622,f31])).
% 1.59/0.60  fof(f622,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~m2_orders_2(X1,sK0,sK1) | ~m2_orders_2(X0,sK0,sK1) | X0 = X1 | m1_orders_2(X1,sK0,X0) | m1_orders_2(X0,sK0,X1)) )),
% 1.59/0.60    inference(resolution,[],[f494,f33])).
% 1.59/0.60  fof(f494,plain,(
% 1.59/0.60    ( ! [X2,X0,X1] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | ~m2_orders_2(X2,sK0,X0) | X1 = X2 | m1_orders_2(X2,sK0,X1) | m1_orders_2(X1,sK0,X2)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f493,f34])).
% 1.59/0.60  fof(f493,plain,(
% 1.59/0.60    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | ~m2_orders_2(X2,sK0,X0) | X1 = X2 | m1_orders_2(X2,sK0,X1) | m1_orders_2(X1,sK0,X2)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f492,f37])).
% 1.59/0.60  fof(f492,plain,(
% 1.59/0.60    ( ! [X2,X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | ~m2_orders_2(X2,sK0,X0) | X1 = X2 | m1_orders_2(X2,sK0,X1) | m1_orders_2(X1,sK0,X2)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f491,f36])).
% 1.59/0.60  fof(f491,plain,(
% 1.59/0.60    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | ~m2_orders_2(X2,sK0,X0) | X1 = X2 | m1_orders_2(X2,sK0,X1) | m1_orders_2(X1,sK0,X2)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f490,f35])).
% 1.59/0.60  fof(f490,plain,(
% 1.59/0.60    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | ~m2_orders_2(X2,sK0,X0) | X1 = X2 | m1_orders_2(X2,sK0,X1) | m1_orders_2(X1,sK0,X2)) )),
% 1.59/0.60    inference(resolution,[],[f44,f38])).
% 1.59/0.60  fof(f44,plain,(
% 1.59/0.60    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | ~m2_orders_2(X3,X0,X1) | X2 = X3 | m1_orders_2(X3,X0,X2) | m1_orders_2(X2,X0,X3)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f24])).
% 1.59/0.60  fof(f24,plain,(
% 1.59/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.59/0.60    inference(flattening,[],[f23])).
% 1.59/0.60  fof(f23,plain,(
% 1.59/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.59/0.60    inference(ennf_transformation,[],[f10])).
% 1.59/0.60  fof(f10,axiom,(
% 1.59/0.60    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 1.59/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).
% 1.59/0.60  fof(f645,plain,(
% 1.59/0.60    m1_orders_2(sK2,sK0,sK2) | r2_xboole_0(sK2,sK3)),
% 1.59/0.60    inference(backward_demodulation,[],[f29,f644])).
% 1.59/0.60  fof(f399,plain,(
% 1.59/0.60    ~m1_orders_2(sK2,sK0,sK2) | k1_xboole_0 = sK2),
% 1.59/0.60    inference(subsumption_resolution,[],[f398,f34])).
% 1.59/0.60  fof(f398,plain,(
% 1.59/0.60    v2_struct_0(sK0) | k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2)),
% 1.59/0.60    inference(subsumption_resolution,[],[f397,f38])).
% 1.59/0.60  fof(f397,plain,(
% 1.59/0.60    ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2)),
% 1.59/0.60    inference(subsumption_resolution,[],[f396,f37])).
% 1.59/0.60  fof(f396,plain,(
% 1.59/0.60    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2)),
% 1.59/0.60    inference(subsumption_resolution,[],[f395,f36])).
% 1.59/0.60  fof(f395,plain,(
% 1.59/0.60    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2)),
% 1.59/0.60    inference(subsumption_resolution,[],[f389,f35])).
% 1.59/0.60  fof(f389,plain,(
% 1.59/0.60    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0) | k1_xboole_0 = sK2 | ~m1_orders_2(sK2,sK0,sK2)),
% 1.59/0.60    inference(resolution,[],[f375,f41])).
% 1.59/0.60  fof(f41,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | v2_struct_0(X0) | k1_xboole_0 = X1 | ~m1_orders_2(X1,X0,X1)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f18])).
% 1.59/0.60  fof(f18,plain,(
% 1.59/0.60    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.59/0.60    inference(flattening,[],[f17])).
% 1.59/0.60  fof(f17,plain,(
% 1.59/0.60    ! [X0] : (! [X1] : (((k1_xboole_0 != X1 | m1_orders_2(X1,X0,X1)) & (~m1_orders_2(X1,X0,X1) | k1_xboole_0 = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.59/0.60    inference(ennf_transformation,[],[f8])).
% 1.59/0.60  fof(f8,axiom,(
% 1.59/0.60    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 1.59/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).
% 1.59/0.60  fof(f498,plain,(
% 1.59/0.60    ~r1_tarski(sK2,k1_funct_1(sK1,u1_struct_0(sK0)))),
% 1.59/0.60    inference(resolution,[],[f489,f56])).
% 1.59/0.60  fof(f56,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 1.59/0.60    inference(cnf_transformation,[],[f28])).
% 1.59/0.60  fof(f28,plain,(
% 1.59/0.60    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 1.59/0.60    inference(ennf_transformation,[],[f5])).
% 1.59/0.60  fof(f5,axiom,(
% 1.59/0.60    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 1.59/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 1.59/0.60  fof(f489,plain,(
% 1.59/0.60    r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK2)),
% 1.59/0.60    inference(resolution,[],[f487,f32])).
% 1.59/0.60  fof(f487,plain,(
% 1.59/0.60    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0)) )),
% 1.59/0.60    inference(resolution,[],[f434,f33])).
% 1.59/0.60  fof(f434,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f433,f34])).
% 1.59/0.60  fof(f433,plain,(
% 1.59/0.60    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f432,f37])).
% 1.59/0.60  fof(f432,plain,(
% 1.59/0.60    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 1.59/0.60    inference(subsumption_resolution,[],[f431,f36])).
% 1.59/0.61  fof(f431,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 1.59/0.61    inference(subsumption_resolution,[],[f430,f35])).
% 1.59/0.61  fof(f430,plain,(
% 1.59/0.61    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 1.59/0.61    inference(resolution,[],[f43,f38])).
% 1.59/0.61  fof(f43,plain,(
% 1.59/0.61    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)) )),
% 1.59/0.61    inference(cnf_transformation,[],[f22])).
% 1.59/0.61  fof(f22,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.59/0.61    inference(flattening,[],[f21])).
% 1.59/0.61  fof(f21,plain,(
% 1.59/0.61    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.59/0.61    inference(ennf_transformation,[],[f9])).
% 1.59/0.61  fof(f9,axiom,(
% 1.59/0.61    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 1.59/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).
% 1.59/0.61  % SZS output end Proof for theBenchmark
% 1.59/0.61  % (1677)------------------------------
% 1.59/0.61  % (1677)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.61  % (1677)Termination reason: Refutation
% 1.59/0.61  
% 1.59/0.61  % (1677)Memory used [KB]: 6652
% 1.59/0.61  % (1677)Time elapsed: 0.190 s
% 1.59/0.61  % (1677)------------------------------
% 1.59/0.61  % (1677)------------------------------
% 1.59/0.61  % (1696)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.59/0.61  % (1664)Success in time 0.245 s
%------------------------------------------------------------------------------
