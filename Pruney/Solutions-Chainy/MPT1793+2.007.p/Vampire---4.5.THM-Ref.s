%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:27 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 293 expanded)
%              Number of leaves         :   15 (  53 expanded)
%              Depth                    :   34
%              Number of atoms          :  599 (1849 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :   23 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f543,plain,(
    $false ),
    inference(subsumption_resolution,[],[f542,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
                  & m1_subset_1(X3,u1_struct_0(X2)) )
              & r1_xboole_0(u1_struct_0(X2),X1)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( r1_xboole_0(u1_struct_0(X2),X1)
                 => ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X2))
                     => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( r1_xboole_0(u1_struct_0(X2),X1)
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X2))
                   => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tmap_1)).

fof(f542,plain,(
    v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f541,f87])).

fof(f87,plain,(
    l1_pre_topc(sK2) ),
    inference(resolution,[],[f86,f48])).

fof(f48,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f54,f53])).

fof(f53,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f541,plain,
    ( ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f539,f98])).

fof(f98,plain,(
    v2_pre_topc(sK2) ),
    inference(resolution,[],[f97,f48])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f96,f53])).

fof(f96,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X0,sK0)
      | v2_pre_topc(X0) ) ),
    inference(resolution,[],[f60,f52])).

fof(f52,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f539,plain,
    ( ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f531,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(sK4(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X1] :
          ( v2_compts_1(X1,X0)
          & ~ v1_xboole_0(X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_compts_1)).

fof(f531,plain,(
    v1_xboole_0(sK4(sK2)) ),
    inference(resolution,[],[f529,f133])).

fof(f133,plain,
    ( r2_hidden(sK5(sK4(sK2)),u1_struct_0(sK2))
    | v1_xboole_0(sK4(sK2)) ),
    inference(resolution,[],[f128,f61])).

fof(f61,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f128,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK4(sK2))
      | r2_hidden(X1,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f127,f98])).

fof(f127,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK2)
      | r2_hidden(X1,u1_struct_0(sK2))
      | ~ r2_hidden(X1,sK4(sK2)) ) ),
    inference(subsumption_resolution,[],[f124,f47])).

fof(f124,plain,(
    ! [X1] :
      ( v2_struct_0(sK2)
      | ~ v2_pre_topc(sK2)
      | r2_hidden(X1,u1_struct_0(sK2))
      | ~ r2_hidden(X1,sK4(sK2)) ) ),
    inference(resolution,[],[f121,f87])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X1,u1_struct_0(X0))
      | ~ r2_hidden(X1,sK4(X0)) ) ),
    inference(resolution,[],[f119,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    ! [X0] :
      ( r1_tarski(sK4(X0),u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f58,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f529,plain,(
    ! [X0] : ~ r2_hidden(X0,u1_struct_0(sK2)) ),
    inference(resolution,[],[f528,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f528,plain,(
    v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f527,f91])).

fof(f91,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f66,f45])).

fof(f45,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f527,plain,(
    ~ r2_hidden(sK3,u1_struct_0(sK2)) ),
    inference(resolution,[],[f526,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r2_hidden(X0,u1_struct_0(sK2)) ) ),
    inference(resolution,[],[f63,f49])).

fof(f49,plain,(
    r1_xboole_0(u1_struct_0(sK2),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f526,plain,(
    r2_hidden(sK3,sK1) ),
    inference(subsumption_resolution,[],[f525,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f525,plain,
    ( r2_hidden(sK3,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f524,f273])).

fof(f273,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f272,f51])).

fof(f272,plain,
    ( v2_struct_0(sK0)
    | m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f271,f53])).

fof(f271,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(resolution,[],[f244,f48])).

fof(f244,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK2,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(sK3,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f243,f47])).

fof(f243,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(sK2)
      | ~ m1_pre_topc(sK2,X0)
      | v2_struct_0(X0)
      | m1_subset_1(sK3,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f55,f45])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f524,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK3,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f523,f50])).

fof(f50,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f523,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK3,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f522,f53])).

fof(f522,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK3,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f521,f52])).

fof(f521,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | r2_hidden(sK3,sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f520,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)
              | r2_hidden(X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ r2_hidden(X2,X1)
               => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_tmap_1)).

% (14198)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
fof(f520,plain,(
    ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) ),
    inference(subsumption_resolution,[],[f519,f50])).

% (14191)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f519,plain,
    ( ~ r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f518,f46])).

fof(f46,plain,(
    ~ r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f518,plain,(
    ! [X0] :
      ( r1_tmap_1(sK2,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),sK3)
      | ~ r1_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f498,f45])).

fof(f498,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0)
      | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f497,f51])).

fof(f497,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0)
      | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f496,f47])).

fof(f496,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK2)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0)
      | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f495,f53])).

fof(f495,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0)
      | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f494,f52])).

fof(f494,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK2)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0)
      | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f399,f48])).

fof(f399,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
      | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f398,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f398,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
      | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f397,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | l1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f397,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
      | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f396,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f396,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
      | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f395,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(k6_tmap_1(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

% (14197)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
fof(f19,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(f395,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
      | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(subsumption_resolution,[],[f394,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f394,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
      | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f393])).

fof(f393,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(k6_tmap_1(X0,X1))
      | ~ l1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(k7_tmap_1(X0,X1))
      | v2_struct_0(k6_tmap_1(X0,X1))
      | ~ m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3)
      | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f85,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f85,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(subsumption_resolution,[],[f82,f55])).

fof(f82,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ r1_tmap_1(X1,X0,X2,X5)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X3,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | X4 != X5
      | ~ r1_tmap_1(X1,X0,X2,X4)
      | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)
                          | ~ r1_tmap_1(X1,X0,X2,X4)
                          | X4 != X5
                          | ~ m1_subset_1(X5,u1_struct_0(X3)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X1)) )
                  | ~ m1_pre_topc(X3,X1)
                  | v2_struct_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
              | ~ v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
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
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
                & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X1)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X1))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X3))
                         => ( ( r1_tmap_1(X1,X0,X2,X4)
                              & X4 = X5 )
                           => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:46:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.19/0.55  % (14195)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.19/0.55  % (14192)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.49/0.55  % (14196)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.49/0.56  % (14212)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.49/0.57  % (14213)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.49/0.57  % (14192)Refutation not found, incomplete strategy% (14192)------------------------------
% 1.49/0.57  % (14192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (14203)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.49/0.57  % (14204)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.49/0.58  % (14212)Refutation not found, incomplete strategy% (14212)------------------------------
% 1.49/0.58  % (14212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.58  % (14192)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.58  
% 1.49/0.58  % (14192)Memory used [KB]: 10746
% 1.49/0.58  % (14192)Time elapsed: 0.135 s
% 1.49/0.58  % (14192)------------------------------
% 1.49/0.58  % (14192)------------------------------
% 1.49/0.58  % (14200)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.49/0.59  % (14200)Refutation not found, incomplete strategy% (14200)------------------------------
% 1.49/0.59  % (14200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.59  % (14200)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.59  
% 1.49/0.59  % (14200)Memory used [KB]: 10746
% 1.49/0.59  % (14200)Time elapsed: 0.155 s
% 1.49/0.59  % (14200)------------------------------
% 1.49/0.59  % (14200)------------------------------
% 1.49/0.59  % (14216)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.49/0.59  % (14194)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.49/0.60  % (14212)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.60  
% 1.49/0.60  % (14212)Memory used [KB]: 11001
% 1.49/0.60  % (14212)Time elapsed: 0.141 s
% 1.49/0.60  % (14212)------------------------------
% 1.49/0.60  % (14212)------------------------------
% 1.49/0.60  % (14196)Refutation found. Thanks to Tanya!
% 1.49/0.60  % SZS status Theorem for theBenchmark
% 1.49/0.60  % SZS output start Proof for theBenchmark
% 1.49/0.60  fof(f543,plain,(
% 1.49/0.60    $false),
% 1.49/0.60    inference(subsumption_resolution,[],[f542,f47])).
% 1.49/0.60  fof(f47,plain,(
% 1.49/0.60    ~v2_struct_0(sK2)),
% 1.49/0.60    inference(cnf_transformation,[],[f23])).
% 1.49/0.60  fof(f23,plain,(
% 1.49/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.49/0.60    inference(flattening,[],[f22])).
% 1.49/0.60  fof(f22,plain,(
% 1.49/0.60    ? [X0] : (? [X1] : (? [X2] : ((? [X3] : (~r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) & m1_subset_1(X3,u1_struct_0(X2))) & r1_xboole_0(u1_struct_0(X2),X1)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.49/0.60    inference(ennf_transformation,[],[f17])).
% 1.49/0.60  fof(f17,negated_conjecture,(
% 1.49/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.49/0.60    inference(negated_conjecture,[],[f16])).
% 1.49/0.60  fof(f16,conjecture,(
% 1.49/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (r1_xboole_0(u1_struct_0(X2),X1) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X2)) => r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3))))))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tmap_1)).
% 1.49/0.60  fof(f542,plain,(
% 1.49/0.60    v2_struct_0(sK2)),
% 1.49/0.60    inference(subsumption_resolution,[],[f541,f87])).
% 1.49/0.60  fof(f87,plain,(
% 1.49/0.60    l1_pre_topc(sK2)),
% 1.49/0.60    inference(resolution,[],[f86,f48])).
% 1.49/0.60  fof(f48,plain,(
% 1.49/0.60    m1_pre_topc(sK2,sK0)),
% 1.49/0.60    inference(cnf_transformation,[],[f23])).
% 1.49/0.60  fof(f86,plain,(
% 1.49/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 1.49/0.60    inference(resolution,[],[f54,f53])).
% 1.49/0.60  fof(f53,plain,(
% 1.49/0.60    l1_pre_topc(sK0)),
% 1.49/0.60    inference(cnf_transformation,[],[f23])).
% 1.49/0.60  fof(f54,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f24])).
% 1.49/0.60  fof(f24,plain,(
% 1.49/0.60    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.49/0.60    inference(ennf_transformation,[],[f8])).
% 1.49/0.60  fof(f8,axiom,(
% 1.49/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.49/0.60  fof(f541,plain,(
% 1.49/0.60    ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.49/0.60    inference(subsumption_resolution,[],[f539,f98])).
% 1.49/0.60  fof(f98,plain,(
% 1.49/0.60    v2_pre_topc(sK2)),
% 1.49/0.60    inference(resolution,[],[f97,f48])).
% 1.49/0.60  fof(f97,plain,(
% 1.49/0.60    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f96,f53])).
% 1.49/0.60  fof(f96,plain,(
% 1.49/0.60    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X0,sK0) | v2_pre_topc(X0)) )),
% 1.49/0.60    inference(resolution,[],[f60,f52])).
% 1.49/0.60  fof(f52,plain,(
% 1.49/0.60    v2_pre_topc(sK0)),
% 1.49/0.60    inference(cnf_transformation,[],[f23])).
% 1.49/0.60  fof(f60,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_pre_topc(X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f34])).
% 1.49/0.60  fof(f34,plain,(
% 1.49/0.60    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.49/0.60    inference(flattening,[],[f33])).
% 1.49/0.60  fof(f33,plain,(
% 1.49/0.60    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.49/0.60    inference(ennf_transformation,[],[f7])).
% 1.49/0.60  fof(f7,axiom,(
% 1.49/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.49/0.60  fof(f539,plain,(
% 1.49/0.60    ~v2_pre_topc(sK2) | ~l1_pre_topc(sK2) | v2_struct_0(sK2)),
% 1.49/0.60    inference(resolution,[],[f531,f59])).
% 1.49/0.60  fof(f59,plain,(
% 1.49/0.60    ( ! [X0] : (~v1_xboole_0(sK4(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f32])).
% 1.49/0.60  fof(f32,plain,(
% 1.49/0.60    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.60    inference(flattening,[],[f31])).
% 1.49/0.60  fof(f31,plain,(
% 1.49/0.60    ! [X0] : (? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.60    inference(ennf_transformation,[],[f21])).
% 1.49/0.60  fof(f21,plain,(
% 1.49/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.49/0.60    inference(pure_predicate_removal,[],[f10])).
% 1.49/0.60  fof(f10,axiom,(
% 1.49/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X1] : (v2_compts_1(X1,X0) & ~v1_xboole_0(X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_compts_1)).
% 1.49/0.60  fof(f531,plain,(
% 1.49/0.60    v1_xboole_0(sK4(sK2))),
% 1.49/0.60    inference(resolution,[],[f529,f133])).
% 1.49/0.60  fof(f133,plain,(
% 1.49/0.60    r2_hidden(sK5(sK4(sK2)),u1_struct_0(sK2)) | v1_xboole_0(sK4(sK2))),
% 1.49/0.60    inference(resolution,[],[f128,f61])).
% 1.49/0.60  fof(f61,plain,(
% 1.49/0.60    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f1])).
% 1.49/0.60  fof(f1,axiom,(
% 1.49/0.60    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.49/0.60  fof(f128,plain,(
% 1.49/0.60    ( ! [X1] : (~r2_hidden(X1,sK4(sK2)) | r2_hidden(X1,u1_struct_0(sK2))) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f127,f98])).
% 1.49/0.60  fof(f127,plain,(
% 1.49/0.60    ( ! [X1] : (~v2_pre_topc(sK2) | r2_hidden(X1,u1_struct_0(sK2)) | ~r2_hidden(X1,sK4(sK2))) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f124,f47])).
% 1.49/0.60  fof(f124,plain,(
% 1.49/0.60    ( ! [X1] : (v2_struct_0(sK2) | ~v2_pre_topc(sK2) | r2_hidden(X1,u1_struct_0(sK2)) | ~r2_hidden(X1,sK4(sK2))) )),
% 1.49/0.60    inference(resolution,[],[f121,f87])).
% 1.49/0.60  fof(f121,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | r2_hidden(X1,u1_struct_0(X0)) | ~r2_hidden(X1,sK4(X0))) )),
% 1.49/0.60    inference(resolution,[],[f119,f77])).
% 1.49/0.60  fof(f77,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f44])).
% 1.49/0.60  fof(f44,plain,(
% 1.49/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.49/0.60    inference(ennf_transformation,[],[f2])).
% 1.49/0.60  fof(f2,axiom,(
% 1.49/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.49/0.60  fof(f119,plain,(
% 1.49/0.60    ( ! [X0] : (r1_tarski(sK4(X0),u1_struct_0(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0)) )),
% 1.49/0.60    inference(resolution,[],[f58,f81])).
% 1.49/0.60  fof(f81,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f6])).
% 1.49/0.60  fof(f6,axiom,(
% 1.49/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.49/0.60  fof(f58,plain,(
% 1.49/0.60    ( ! [X0] : (m1_subset_1(sK4(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f32])).
% 1.49/0.60  fof(f529,plain,(
% 1.49/0.60    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(sK2))) )),
% 1.49/0.60    inference(resolution,[],[f528,f62])).
% 1.49/0.60  fof(f62,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f1])).
% 1.49/0.60  fof(f528,plain,(
% 1.49/0.60    v1_xboole_0(u1_struct_0(sK2))),
% 1.49/0.60    inference(resolution,[],[f527,f91])).
% 1.49/0.60  fof(f91,plain,(
% 1.49/0.60    r2_hidden(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2))),
% 1.49/0.60    inference(resolution,[],[f66,f45])).
% 1.49/0.60  fof(f45,plain,(
% 1.49/0.60    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.49/0.60    inference(cnf_transformation,[],[f23])).
% 1.49/0.60  fof(f66,plain,(
% 1.49/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f37])).
% 1.49/0.60  fof(f37,plain,(
% 1.49/0.60    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.49/0.60    inference(flattening,[],[f36])).
% 1.49/0.60  fof(f36,plain,(
% 1.49/0.60    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.49/0.60    inference(ennf_transformation,[],[f5])).
% 1.49/0.60  fof(f5,axiom,(
% 1.49/0.60    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.49/0.60  fof(f527,plain,(
% 1.49/0.60    ~r2_hidden(sK3,u1_struct_0(sK2))),
% 1.49/0.60    inference(resolution,[],[f526,f101])).
% 1.49/0.60  fof(f101,plain,(
% 1.49/0.60    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r2_hidden(X0,u1_struct_0(sK2))) )),
% 1.49/0.60    inference(resolution,[],[f63,f49])).
% 1.49/0.60  fof(f49,plain,(
% 1.49/0.60    r1_xboole_0(u1_struct_0(sK2),sK1)),
% 1.49/0.60    inference(cnf_transformation,[],[f23])).
% 1.49/0.60  fof(f63,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f35])).
% 1.49/0.60  fof(f35,plain,(
% 1.49/0.60    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.49/0.60    inference(ennf_transformation,[],[f18])).
% 1.49/0.60  fof(f18,plain,(
% 1.49/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.49/0.60    inference(rectify,[],[f3])).
% 1.49/0.60  fof(f3,axiom,(
% 1.49/0.60    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.49/0.60  fof(f526,plain,(
% 1.49/0.60    r2_hidden(sK3,sK1)),
% 1.49/0.60    inference(subsumption_resolution,[],[f525,f51])).
% 1.49/0.60  fof(f51,plain,(
% 1.49/0.60    ~v2_struct_0(sK0)),
% 1.49/0.60    inference(cnf_transformation,[],[f23])).
% 1.49/0.60  fof(f525,plain,(
% 1.49/0.60    r2_hidden(sK3,sK1) | v2_struct_0(sK0)),
% 1.49/0.60    inference(subsumption_resolution,[],[f524,f273])).
% 1.49/0.60  fof(f273,plain,(
% 1.49/0.60    m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.49/0.60    inference(subsumption_resolution,[],[f272,f51])).
% 1.49/0.60  fof(f272,plain,(
% 1.49/0.60    v2_struct_0(sK0) | m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.49/0.60    inference(subsumption_resolution,[],[f271,f53])).
% 1.49/0.60  fof(f271,plain,(
% 1.49/0.60    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(sK3,u1_struct_0(sK0))),
% 1.49/0.60    inference(resolution,[],[f244,f48])).
% 1.49/0.60  fof(f244,plain,(
% 1.49/0.60    ( ! [X0] : (~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(sK3,u1_struct_0(X0))) )),
% 1.49/0.60    inference(subsumption_resolution,[],[f243,f47])).
% 1.49/0.60  fof(f243,plain,(
% 1.49/0.60    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,X0) | v2_struct_0(X0) | m1_subset_1(sK3,u1_struct_0(X0))) )),
% 1.49/0.60    inference(resolution,[],[f55,f45])).
% 1.49/0.60  fof(f55,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.49/0.60    inference(cnf_transformation,[],[f26])).
% 1.49/0.60  fof(f26,plain,(
% 1.49/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.60    inference(flattening,[],[f25])).
% 1.49/0.60  fof(f25,plain,(
% 1.49/0.60    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.60    inference(ennf_transformation,[],[f9])).
% 1.49/0.60  fof(f9,axiom,(
% 1.49/0.60    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.49/0.60  fof(f524,plain,(
% 1.49/0.60    ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK3,sK1) | v2_struct_0(sK0)),
% 1.49/0.60    inference(subsumption_resolution,[],[f523,f50])).
% 1.49/0.60  fof(f50,plain,(
% 1.49/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.60    inference(cnf_transformation,[],[f23])).
% 1.49/0.60  fof(f523,plain,(
% 1.49/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK3,sK1) | v2_struct_0(sK0)),
% 1.49/0.60    inference(subsumption_resolution,[],[f522,f53])).
% 1.49/0.60  fof(f522,plain,(
% 1.49/0.60    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK3,sK1) | v2_struct_0(sK0)),
% 1.49/0.60    inference(subsumption_resolution,[],[f521,f52])).
% 1.49/0.60  fof(f521,plain,(
% 1.49/0.60    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,u1_struct_0(sK0)) | r2_hidden(sK3,sK1) | v2_struct_0(sK0)),
% 1.49/0.60    inference(resolution,[],[f520,f56])).
% 1.49/0.60  fof(f56,plain,(
% 1.49/0.60    ( ! [X2,X0,X1] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | r2_hidden(X2,X1) | v2_struct_0(X0)) )),
% 1.49/0.60    inference(cnf_transformation,[],[f28])).
% 1.49/0.60  fof(f28,plain,(
% 1.49/0.60    ! [X0] : (! [X1] : (! [X2] : (r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.60    inference(flattening,[],[f27])).
% 1.49/0.60  fof(f27,plain,(
% 1.49/0.60    ! [X0] : (! [X1] : (! [X2] : ((r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2) | r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.60    inference(ennf_transformation,[],[f14])).
% 1.49/0.60  fof(f14,axiom,(
% 1.49/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~r2_hidden(X2,X1) => r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2)))))),
% 1.49/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_tmap_1)).
% 1.49/0.60  % (14198)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.49/0.61  fof(f520,plain,(
% 1.49/0.61    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3)),
% 1.49/0.61    inference(subsumption_resolution,[],[f519,f50])).
% 1.49/0.61  % (14191)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.49/0.61  fof(f519,plain,(
% 1.49/0.61    ~r1_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK3) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.49/0.61    inference(resolution,[],[f518,f46])).
% 1.49/0.61  fof(f46,plain,(
% 1.49/0.61    ~r1_tmap_1(sK2,k6_tmap_1(sK0,sK1),k2_tmap_1(sK0,k6_tmap_1(sK0,sK1),k7_tmap_1(sK0,sK1),sK2),sK3)),
% 1.49/0.61    inference(cnf_transformation,[],[f23])).
% 1.49/0.61  fof(f518,plain,(
% 1.49/0.61    ( ! [X0] : (r1_tmap_1(sK2,k6_tmap_1(sK0,X0),k2_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK2),sK3) | ~r1_tmap_1(sK0,k6_tmap_1(sK0,X0),k7_tmap_1(sK0,X0),sK3) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.49/0.61    inference(resolution,[],[f498,f45])).
% 1.49/0.61  fof(f498,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0) | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.49/0.61    inference(subsumption_resolution,[],[f497,f51])).
% 1.49/0.61  fof(f497,plain,(
% 1.49/0.61    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0) | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.49/0.61    inference(subsumption_resolution,[],[f496,f47])).
% 1.49/0.61  fof(f496,plain,(
% 1.49/0.61    ( ! [X0,X1] : (v2_struct_0(sK2) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0) | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.49/0.61    inference(subsumption_resolution,[],[f495,f53])).
% 1.49/0.61  fof(f495,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0) | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.49/0.61    inference(subsumption_resolution,[],[f494,f52])).
% 1.49/0.61  fof(f494,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK2) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~r1_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),X0) | r1_tmap_1(sK2,k6_tmap_1(sK0,X1),k2_tmap_1(sK0,k6_tmap_1(sK0,X1),k7_tmap_1(sK0,X1),sK2),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.49/0.61    inference(resolution,[],[f399,f48])).
% 1.49/0.61  fof(f399,plain,(
% 1.49/0.61    ( ! [X2,X0,X3,X1] : (~m1_pre_topc(X2,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X2) | v2_struct_0(X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.49/0.61    inference(subsumption_resolution,[],[f398,f71])).
% 1.49/0.61  fof(f71,plain,(
% 1.49/0.61    ( ! [X0,X1] : (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f41])).
% 1.49/0.61  fof(f41,plain,(
% 1.49/0.61    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.61    inference(flattening,[],[f40])).
% 1.49/0.61  fof(f40,plain,(
% 1.49/0.61    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.61    inference(ennf_transformation,[],[f12])).
% 1.49/0.61  fof(f12,axiom,(
% 1.49/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 1.49/0.61  fof(f398,plain,(
% 1.49/0.61    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.49/0.61    inference(subsumption_resolution,[],[f397,f73])).
% 1.49/0.61  fof(f73,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1))) )),
% 1.49/0.61    inference(cnf_transformation,[],[f43])).
% 1.49/0.61  fof(f43,plain,(
% 1.49/0.61    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.61    inference(flattening,[],[f42])).
% 1.49/0.61  fof(f42,plain,(
% 1.49/0.61    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.61    inference(ennf_transformation,[],[f20])).
% 1.49/0.61  fof(f20,plain,(
% 1.49/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 1.49/0.61    inference(pure_predicate_removal,[],[f11])).
% 1.49/0.61  fof(f11,axiom,(
% 1.49/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 1.49/0.61  fof(f397,plain,(
% 1.49/0.61    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.49/0.61    inference(subsumption_resolution,[],[f396,f69])).
% 1.49/0.61  fof(f69,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1))) )),
% 1.49/0.61    inference(cnf_transformation,[],[f41])).
% 1.49/0.61  fof(f396,plain,(
% 1.49/0.61    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(k7_tmap_1(X0,X1)) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.49/0.61    inference(subsumption_resolution,[],[f395,f67])).
% 1.49/0.61  fof(f67,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~v2_struct_0(k6_tmap_1(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f39])).
% 1.49/0.61  fof(f39,plain,(
% 1.49/0.61    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.61    inference(flattening,[],[f38])).
% 1.49/0.61  fof(f38,plain,(
% 1.49/0.61    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.61    inference(ennf_transformation,[],[f19])).
% 1.49/0.61  % (14197)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.49/0.61  fof(f19,plain,(
% 1.49/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 1.49/0.61    inference(pure_predicate_removal,[],[f13])).
% 1.49/0.61  fof(f13,axiom,(
% 1.49/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_tmap_1)).
% 1.49/0.61  fof(f395,plain,(
% 1.49/0.61    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(k7_tmap_1(X0,X1)) | v2_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.49/0.61    inference(subsumption_resolution,[],[f394,f68])).
% 1.49/0.61  fof(f68,plain,(
% 1.49/0.61    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_pre_topc(k6_tmap_1(X0,X1))) )),
% 1.49/0.61    inference(cnf_transformation,[],[f39])).
% 1.49/0.61  fof(f394,plain,(
% 1.49/0.61    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(k6_tmap_1(X0,X1)) | ~l1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(k7_tmap_1(X0,X1)) | v2_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.49/0.61    inference(duplicate_literal_removal,[],[f393])).
% 1.49/0.61  fof(f393,plain,(
% 1.49/0.61    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(k6_tmap_1(X0,X1)) | ~l1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(k7_tmap_1(X0,X1)) | v2_struct_0(k6_tmap_1(X0,X1)) | ~m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~r1_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X3) | r1_tmap_1(X2,k6_tmap_1(X0,X1),k2_tmap_1(X0,k6_tmap_1(X0,X1),k7_tmap_1(X0,X1),X2),X3) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 1.49/0.61    inference(resolution,[],[f85,f70])).
% 1.49/0.61  fof(f70,plain,(
% 1.49/0.61    ( ! [X0,X1] : (v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f41])).
% 1.49/0.61  fof(f85,plain,(
% 1.49/0.61    ( ! [X2,X0,X5,X3,X1] : (~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | v2_struct_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 1.49/0.61    inference(subsumption_resolution,[],[f82,f55])).
% 1.49/0.61  fof(f82,plain,(
% 1.49/0.61    ( ! [X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~r1_tmap_1(X1,X0,X2,X5) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 1.49/0.61    inference(equality_resolution,[],[f57])).
% 1.49/0.61  fof(f57,plain,(
% 1.49/0.61    ( ! [X4,X2,X0,X5,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | v2_struct_0(X3) | ~m1_pre_topc(X3,X1) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X5,u1_struct_0(X3)) | X4 != X5 | ~r1_tmap_1(X1,X0,X2,X4) | r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5)) )),
% 1.49/0.61    inference(cnf_transformation,[],[f30])).
% 1.49/0.61  fof(f30,plain,(
% 1.49/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | ~r1_tmap_1(X1,X0,X2,X4) | X4 != X5 | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~m1_pre_topc(X3,X1) | v2_struct_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.49/0.61    inference(flattening,[],[f29])).
% 1.49/0.61  fof(f29,plain,(
% 1.49/0.61    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5) | (~r1_tmap_1(X1,X0,X2,X4) | X4 != X5)) | ~m1_subset_1(X5,u1_struct_0(X3))) | ~m1_subset_1(X4,u1_struct_0(X1))) | (~m1_pre_topc(X3,X1) | v2_struct_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | ~v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.49/0.61    inference(ennf_transformation,[],[f15])).
% 1.49/0.61  fof(f15,axiom,(
% 1.49/0.61    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) & v1_funct_2(X2,u1_struct_0(X1),u1_struct_0(X0)) & v1_funct_1(X2)) => ! [X3] : ((m1_pre_topc(X3,X1) & ~v2_struct_0(X3)) => ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => ! [X5] : (m1_subset_1(X5,u1_struct_0(X3)) => ((r1_tmap_1(X1,X0,X2,X4) & X4 = X5) => r1_tmap_1(X3,X0,k2_tmap_1(X1,X0,X2,X3),X5))))))))),
% 1.49/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).
% 1.49/0.61  % SZS output end Proof for theBenchmark
% 1.49/0.61  % (14196)------------------------------
% 1.49/0.61  % (14196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.61  % (14196)Termination reason: Refutation
% 1.49/0.61  
% 1.49/0.61  % (14196)Memory used [KB]: 6780
% 1.49/0.61  % (14196)Time elapsed: 0.166 s
% 1.49/0.61  % (14196)------------------------------
% 1.49/0.61  % (14196)------------------------------
% 1.49/0.61  % (14210)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.49/0.62  % (14189)Success in time 0.253 s
%------------------------------------------------------------------------------
