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
% DateTime   : Thu Dec  3 13:11:11 EST 2020

% Result     : Theorem 6.20s
% Output     : Refutation 6.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 444 expanded)
%              Number of leaves         :   24 ( 136 expanded)
%              Depth                    :   33
%              Number of atoms          :  299 (1474 expanded)
%              Number of equality atoms :   28 (  48 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10496,plain,(
    $false ),
    inference(subsumption_resolution,[],[f10495,f152])).

fof(f152,plain,(
    ! [X6] : m1_subset_1(k4_xboole_0(sK1,X6),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f102,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f102,plain,(
    ! [X2] : r1_tarski(k4_xboole_0(sK1,X2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f91,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f91,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f52,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

fof(f10495,plain,(
    ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f10485,f60])).

fof(f60,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f10485,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f6591,f93])).

fof(f93,plain,(
    ! [X1] :
      ( r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f88,f51])).

fof(f51,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f88,plain,(
    ! [X1] :
      ( r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f52,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f6591,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f6584,f1505])).

fof(f1505,plain,(
    ! [X2] : r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X2)),X2) ),
    inference(resolution,[],[f344,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f344,plain,(
    ! [X4] : r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X4)),k4_xboole_0(sK1,X4)) ),
    inference(subsumption_resolution,[],[f338,f51])).

fof(f338,plain,(
    ! [X4] :
      ( r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X4)),k4_xboole_0(sK1,X4))
      | ~ l1_pre_topc(sK0) ) ),
    inference(resolution,[],[f152,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f6584,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2) ),
    inference(resolution,[],[f1310,f3724])).

fof(f3724,plain,(
    ! [X3] :
      ( r1_xboole_0(X3,k1_tops_1(sK0,sK2))
      | ~ r1_xboole_0(X3,sK2) ) ),
    inference(superposition,[],[f75,f3633])).

fof(f3633,plain,(
    sK2 = k2_xboole_0(sK2,k1_tops_1(sK0,sK2)) ),
    inference(forward_demodulation,[],[f3612,f56])).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f3612,plain,(
    k2_xboole_0(sK2,k1_tops_1(sK0,sK2)) = k2_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f61,f3236])).

fof(f3236,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f2242,f114])).

fof(f114,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f109,f51])).

fof(f109,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f53,f57])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f41])).

fof(f2242,plain,(
    ! [X8,X9] :
      ( ~ r1_tarski(X8,X9)
      | k1_xboole_0 = k4_xboole_0(X8,X9) ) ),
    inference(forward_demodulation,[],[f2225,f56])).

fof(f2225,plain,(
    ! [X8,X9] :
      ( k1_xboole_0 = k4_xboole_0(X8,X9)
      | ~ r1_tarski(X8,k2_xboole_0(X9,k1_xboole_0)) ) ),
    inference(resolution,[],[f2152,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f2152,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k1_xboole_0 = X3 ) ),
    inference(forward_demodulation,[],[f2141,f2129])).

fof(f2129,plain,(
    ! [X7] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X7) ),
    inference(resolution,[],[f2124,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f2124,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f2118,f55])).

fof(f55,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2118,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k1_xboole_0,X0)
      | ~ r1_tarski(k1_xboole_0,k4_xboole_0(X1,X2)) ) ),
    inference(resolution,[],[f2101,f80])).

fof(f2101,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_xboole_0,X0)
      | r1_xboole_0(k1_xboole_0,X1) ) ),
    inference(superposition,[],[f2075,f65])).

fof(f2075,plain,(
    ! [X28,X29] : r1_xboole_0(k4_xboole_0(k1_xboole_0,X28),X29) ),
    inference(resolution,[],[f2061,f80])).

fof(f2061,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(resolution,[],[f2043,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f2043,plain,(
    ! [X14,X15] : ~ r2_hidden(X14,k4_xboole_0(k1_xboole_0,X15)) ),
    inference(resolution,[],[f2026,f60])).

fof(f2026,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k1_xboole_0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f2014,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f2014,plain,(
    ! [X36] : ~ r2_hidden(X36,k1_xboole_0) ),
    inference(resolution,[],[f232,f55])).

fof(f232,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X2,k4_xboole_0(sK1,u1_struct_0(sK0)))
      | ~ r2_hidden(X1,X2) ) ),
    inference(resolution,[],[f219,f67])).

fof(f219,plain,(
    ! [X7] : ~ r2_hidden(X7,k4_xboole_0(sK1,u1_struct_0(sK0))) ),
    inference(resolution,[],[f201,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f201,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,u1_struct_0(sK0)),X0) ),
    inference(resolution,[],[f199,f78])).

fof(f199,plain,(
    ! [X9] : r1_tarski(sK1,k2_xboole_0(u1_struct_0(sK0),X9)) ),
    inference(resolution,[],[f105,f59])).

fof(f59,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f105,plain,(
    ! [X5] :
      ( ~ r1_tarski(u1_struct_0(sK0),X5)
      | r1_tarski(sK1,X5) ) ),
    inference(resolution,[],[f91,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f2141,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(X3,k1_xboole_0)
      | k4_xboole_0(k1_xboole_0,X4) = X3 ) ),
    inference(backward_demodulation,[],[f2065,f2129])).

fof(f2065,plain,(
    ! [X4,X3] :
      ( k4_xboole_0(k1_xboole_0,X4) = X3
      | ~ r1_tarski(X3,k4_xboole_0(k1_xboole_0,X4)) ) ),
    inference(resolution,[],[f2061,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f61,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f1310,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f1175,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f1175,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f95,f1171])).

fof(f1171,plain,(
    ! [X2] : k4_xboole_0(k1_tops_1(sK0,sK1),X2) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X2) ),
    inference(resolution,[],[f1160,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1160,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f1153,f71])).

fof(f1153,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(superposition,[],[f1138,f56])).

fof(f1138,plain,(
    ! [X36] : r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(u1_struct_0(sK0),X36)) ),
    inference(resolution,[],[f210,f94])).

fof(f94,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f89,f51])).

fof(f89,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f52,f57])).

fof(f210,plain,(
    ! [X14,X13] :
      ( ~ r1_tarski(X13,sK1)
      | r1_tarski(X13,k2_xboole_0(u1_struct_0(sK0),X14)) ) ),
    inference(resolution,[],[f199,f82])).

fof(f95,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f54,f90])).

fof(f90,plain,(
    ! [X2] : k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2) ),
    inference(resolution,[],[f52,f77])).

fof(f54,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:37:36 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.51  % (4311)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.53  % (4328)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.25/0.53  % (4310)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.25/0.53  % (4308)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.25/0.53  % (4317)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.53  % (4326)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.54  % (4305)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.25/0.54  % (4323)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.25/0.54  % (4318)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.54  % (4315)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.25/0.54  % (4309)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.25/0.54  % (4324)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.25/0.54  % (4330)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.25/0.55  % (4306)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.37/0.55  % (4307)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.37/0.55  % (4304)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.37/0.55  % (4325)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.37/0.55  % (4316)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.37/0.55  % (4331)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.37/0.55  % (4327)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.37/0.55  % (4312)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.37/0.56  % (4333)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.37/0.56  % (4321)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.37/0.56  % (4332)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.37/0.56  % (4319)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.37/0.56  % (4320)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.37/0.56  % (4322)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.37/0.57  % (4313)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.37/0.57  % (4314)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.37/0.57  % (4329)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 3.48/0.82  % (4309)Time limit reached!
% 3.48/0.82  % (4309)------------------------------
% 3.48/0.82  % (4309)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.48/0.82  % (4309)Termination reason: Time limit
% 3.48/0.82  
% 3.48/0.82  % (4309)Memory used [KB]: 8187
% 3.48/0.82  % (4309)Time elapsed: 0.403 s
% 3.48/0.82  % (4309)------------------------------
% 3.48/0.82  % (4309)------------------------------
% 3.69/0.91  % (4316)Time limit reached!
% 3.69/0.91  % (4316)------------------------------
% 3.69/0.91  % (4316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/0.91  % (4316)Termination reason: Time limit
% 3.69/0.91  % (4316)Termination phase: Saturation
% 3.69/0.91  
% 3.69/0.91  % (4316)Memory used [KB]: 8443
% 3.69/0.91  % (4316)Time elapsed: 0.502 s
% 3.69/0.91  % (4316)------------------------------
% 3.69/0.91  % (4316)------------------------------
% 3.69/0.92  % (4321)Time limit reached!
% 3.69/0.92  % (4321)------------------------------
% 3.69/0.92  % (4321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.93  % (4321)Termination reason: Time limit
% 4.35/0.93  
% 4.35/0.93  % (4321)Memory used [KB]: 13432
% 4.35/0.93  % (4321)Time elapsed: 0.509 s
% 4.35/0.93  % (4321)------------------------------
% 4.35/0.93  % (4321)------------------------------
% 4.35/0.94  % (4304)Time limit reached!
% 4.35/0.94  % (4304)------------------------------
% 4.35/0.94  % (4304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.95  % (4304)Termination reason: Time limit
% 4.35/0.95  
% 4.35/0.95  % (4304)Memory used [KB]: 3965
% 4.35/0.95  % (4304)Time elapsed: 0.524 s
% 4.35/0.95  % (4304)------------------------------
% 4.35/0.95  % (4304)------------------------------
% 4.35/0.95  % (4335)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.35/0.96  % (4314)Time limit reached!
% 4.35/0.96  % (4314)------------------------------
% 4.35/0.96  % (4314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.96  % (4314)Termination reason: Time limit
% 4.35/0.96  % (4314)Termination phase: Saturation
% 4.35/0.96  
% 4.35/0.96  % (4314)Memory used [KB]: 11769
% 4.35/0.96  % (4314)Time elapsed: 0.500 s
% 4.35/0.96  % (4314)------------------------------
% 4.35/0.96  % (4314)------------------------------
% 4.35/0.96  % (4305)Time limit reached!
% 4.35/0.96  % (4305)------------------------------
% 4.35/0.96  % (4305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.35/0.96  % (4305)Termination reason: Time limit
% 4.35/0.96  
% 4.35/0.96  % (4305)Memory used [KB]: 8187
% 4.35/0.96  % (4305)Time elapsed: 0.526 s
% 4.35/0.96  % (4305)------------------------------
% 4.35/0.96  % (4305)------------------------------
% 4.72/1.01  % (4320)Time limit reached!
% 4.72/1.01  % (4320)------------------------------
% 4.72/1.01  % (4320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.72/1.01  % (4320)Termination reason: Time limit
% 4.72/1.01  % (4320)Termination phase: Saturation
% 4.72/1.01  
% 4.72/1.01  % (4320)Memory used [KB]: 16630
% 4.72/1.01  % (4320)Time elapsed: 0.600 s
% 4.72/1.01  % (4320)------------------------------
% 4.72/1.01  % (4320)------------------------------
% 4.72/1.02  % (4332)Time limit reached!
% 4.72/1.02  % (4332)------------------------------
% 4.72/1.02  % (4332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.72/1.02  % (4332)Termination reason: Time limit
% 4.72/1.02  
% 4.72/1.02  % (4332)Memory used [KB]: 8571
% 4.72/1.02  % (4332)Time elapsed: 0.609 s
% 4.72/1.02  % (4332)------------------------------
% 4.72/1.02  % (4332)------------------------------
% 4.72/1.03  % (4311)Time limit reached!
% 4.72/1.03  % (4311)------------------------------
% 4.72/1.03  % (4311)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.72/1.03  % (4311)Termination reason: Time limit
% 4.72/1.03  
% 4.72/1.03  % (4311)Memory used [KB]: 10746
% 4.72/1.03  % (4311)Time elapsed: 0.614 s
% 4.72/1.03  % (4311)------------------------------
% 4.72/1.03  % (4311)------------------------------
% 4.72/1.04  % (4336)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 5.19/1.05  % (4338)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 5.19/1.06  % (4337)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 5.56/1.09  % (4339)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 5.56/1.10  % (4340)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.94/1.14  % (4341)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.20/1.17  % (4342)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.20/1.18  % (4327)Refutation found. Thanks to Tanya!
% 6.20/1.18  % SZS status Theorem for theBenchmark
% 6.20/1.18  % SZS output start Proof for theBenchmark
% 6.20/1.18  fof(f10496,plain,(
% 6.20/1.18    $false),
% 6.20/1.18    inference(subsumption_resolution,[],[f10495,f152])).
% 6.20/1.18  fof(f152,plain,(
% 6.20/1.18    ( ! [X6] : (m1_subset_1(k4_xboole_0(sK1,X6),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 6.20/1.18    inference(resolution,[],[f102,f71])).
% 6.20/1.18  fof(f71,plain,(
% 6.20/1.18    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f49])).
% 6.20/1.18  fof(f49,plain,(
% 6.20/1.18    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 6.20/1.18    inference(nnf_transformation,[],[f16])).
% 6.20/1.18  fof(f16,axiom,(
% 6.20/1.18    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 6.20/1.18  fof(f102,plain,(
% 6.20/1.18    ( ! [X2] : (r1_tarski(k4_xboole_0(sK1,X2),u1_struct_0(sK0))) )),
% 6.20/1.18    inference(resolution,[],[f91,f76])).
% 6.20/1.18  fof(f76,plain,(
% 6.20/1.18    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f30])).
% 6.20/1.18  fof(f30,plain,(
% 6.20/1.18    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 6.20/1.18    inference(ennf_transformation,[],[f4])).
% 6.20/1.18  fof(f4,axiom,(
% 6.20/1.18    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 6.20/1.18  fof(f91,plain,(
% 6.20/1.18    r1_tarski(sK1,u1_struct_0(sK0))),
% 6.20/1.18    inference(resolution,[],[f52,f70])).
% 6.20/1.18  fof(f70,plain,(
% 6.20/1.18    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 6.20/1.18    inference(cnf_transformation,[],[f49])).
% 6.20/1.18  fof(f52,plain,(
% 6.20/1.18    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.20/1.18    inference(cnf_transformation,[],[f41])).
% 6.20/1.18  fof(f41,plain,(
% 6.20/1.18    ((~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 6.20/1.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f40,f39,f38])).
% 6.20/1.18  fof(f38,plain,(
% 6.20/1.18    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 6.20/1.18    introduced(choice_axiom,[])).
% 6.20/1.18  fof(f39,plain,(
% 6.20/1.18    ? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),X1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 6.20/1.18    introduced(choice_axiom,[])).
% 6.20/1.18  fof(f40,plain,(
% 6.20/1.18    ? [X2] : (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,X2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 6.20/1.18    introduced(choice_axiom,[])).
% 6.20/1.18  fof(f23,plain,(
% 6.20/1.18    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 6.20/1.18    inference(flattening,[],[f22])).
% 6.20/1.18  fof(f22,plain,(
% 6.20/1.18    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 6.20/1.18    inference(ennf_transformation,[],[f21])).
% 6.20/1.18  fof(f21,negated_conjecture,(
% 6.20/1.18    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 6.20/1.18    inference(negated_conjecture,[],[f20])).
% 6.20/1.18  fof(f20,conjecture,(
% 6.20/1.18    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).
% 6.20/1.18  fof(f10495,plain,(
% 6.20/1.18    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.20/1.18    inference(subsumption_resolution,[],[f10485,f60])).
% 6.20/1.18  fof(f60,plain,(
% 6.20/1.18    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f8])).
% 6.20/1.18  fof(f8,axiom,(
% 6.20/1.18    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 6.20/1.18  fof(f10485,plain,(
% 6.20/1.18    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.20/1.18    inference(resolution,[],[f6591,f93])).
% 6.20/1.18  fof(f93,plain,(
% 6.20/1.18    ( ! [X1] : (r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,sK1)) | ~r1_tarski(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 6.20/1.18    inference(subsumption_resolution,[],[f88,f51])).
% 6.20/1.18  fof(f51,plain,(
% 6.20/1.18    l1_pre_topc(sK0)),
% 6.20/1.18    inference(cnf_transformation,[],[f41])).
% 6.20/1.18  fof(f88,plain,(
% 6.20/1.18    ( ! [X1] : (r1_tarski(k1_tops_1(sK0,X1),k1_tops_1(sK0,sK1)) | ~r1_tarski(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) )),
% 6.20/1.18    inference(resolution,[],[f52,f58])).
% 6.20/1.18  fof(f58,plain,(
% 6.20/1.18    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f26])).
% 6.20/1.18  fof(f26,plain,(
% 6.20/1.18    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.20/1.18    inference(flattening,[],[f25])).
% 6.20/1.18  fof(f25,plain,(
% 6.20/1.18    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.20/1.18    inference(ennf_transformation,[],[f19])).
% 6.20/1.18  fof(f19,axiom,(
% 6.20/1.18    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 6.20/1.18  fof(f6591,plain,(
% 6.20/1.18    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 6.20/1.18    inference(subsumption_resolution,[],[f6584,f1505])).
% 6.20/1.18  fof(f1505,plain,(
% 6.20/1.18    ( ! [X2] : (r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X2)),X2)) )),
% 6.20/1.18    inference(resolution,[],[f344,f80])).
% 6.20/1.18  fof(f80,plain,(
% 6.20/1.18    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 6.20/1.18    inference(cnf_transformation,[],[f33])).
% 6.20/1.18  fof(f33,plain,(
% 6.20/1.18    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 6.20/1.18    inference(ennf_transformation,[],[f3])).
% 6.20/1.18  fof(f3,axiom,(
% 6.20/1.18    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 6.20/1.18  fof(f344,plain,(
% 6.20/1.18    ( ! [X4] : (r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X4)),k4_xboole_0(sK1,X4))) )),
% 6.20/1.18    inference(subsumption_resolution,[],[f338,f51])).
% 6.20/1.18  fof(f338,plain,(
% 6.20/1.18    ( ! [X4] : (r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X4)),k4_xboole_0(sK1,X4)) | ~l1_pre_topc(sK0)) )),
% 6.20/1.18    inference(resolution,[],[f152,f57])).
% 6.20/1.18  fof(f57,plain,(
% 6.20/1.18    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f24])).
% 6.20/1.18  fof(f24,plain,(
% 6.20/1.18    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 6.20/1.18    inference(ennf_transformation,[],[f18])).
% 6.20/1.18  fof(f18,axiom,(
% 6.20/1.18    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 6.20/1.18  fof(f6584,plain,(
% 6.20/1.18    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) | ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),sK2)),
% 6.20/1.18    inference(resolution,[],[f1310,f3724])).
% 6.20/1.18  fof(f3724,plain,(
% 6.20/1.18    ( ! [X3] : (r1_xboole_0(X3,k1_tops_1(sK0,sK2)) | ~r1_xboole_0(X3,sK2)) )),
% 6.20/1.18    inference(superposition,[],[f75,f3633])).
% 6.20/1.18  fof(f3633,plain,(
% 6.20/1.18    sK2 = k2_xboole_0(sK2,k1_tops_1(sK0,sK2))),
% 6.20/1.18    inference(forward_demodulation,[],[f3612,f56])).
% 6.20/1.18  fof(f56,plain,(
% 6.20/1.18    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.20/1.18    inference(cnf_transformation,[],[f5])).
% 6.20/1.18  fof(f5,axiom,(
% 6.20/1.18    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 6.20/1.18  fof(f3612,plain,(
% 6.20/1.18    k2_xboole_0(sK2,k1_tops_1(sK0,sK2)) = k2_xboole_0(sK2,k1_xboole_0)),
% 6.20/1.18    inference(superposition,[],[f61,f3236])).
% 6.20/1.18  fof(f3236,plain,(
% 6.20/1.18    k1_xboole_0 = k4_xboole_0(k1_tops_1(sK0,sK2),sK2)),
% 6.20/1.18    inference(resolution,[],[f2242,f114])).
% 6.20/1.18  fof(f114,plain,(
% 6.20/1.18    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 6.20/1.18    inference(subsumption_resolution,[],[f109,f51])).
% 6.20/1.18  fof(f109,plain,(
% 6.20/1.18    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~l1_pre_topc(sK0)),
% 6.20/1.18    inference(resolution,[],[f53,f57])).
% 6.20/1.18  fof(f53,plain,(
% 6.20/1.18    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.20/1.18    inference(cnf_transformation,[],[f41])).
% 6.20/1.18  fof(f2242,plain,(
% 6.20/1.18    ( ! [X8,X9] : (~r1_tarski(X8,X9) | k1_xboole_0 = k4_xboole_0(X8,X9)) )),
% 6.20/1.18    inference(forward_demodulation,[],[f2225,f56])).
% 6.20/1.18  fof(f2225,plain,(
% 6.20/1.18    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(X8,X9) | ~r1_tarski(X8,k2_xboole_0(X9,k1_xboole_0))) )),
% 6.20/1.18    inference(resolution,[],[f2152,f78])).
% 6.20/1.18  fof(f78,plain,(
% 6.20/1.18    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 6.20/1.18    inference(cnf_transformation,[],[f32])).
% 6.20/1.18  fof(f32,plain,(
% 6.20/1.18    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 6.20/1.18    inference(ennf_transformation,[],[f10])).
% 6.20/1.18  fof(f10,axiom,(
% 6.20/1.18    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 6.20/1.18  fof(f2152,plain,(
% 6.20/1.18    ( ! [X3] : (~r1_tarski(X3,k1_xboole_0) | k1_xboole_0 = X3) )),
% 6.20/1.18    inference(forward_demodulation,[],[f2141,f2129])).
% 6.20/1.18  fof(f2129,plain,(
% 6.20/1.18    ( ! [X7] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X7)) )),
% 6.20/1.18    inference(resolution,[],[f2124,f65])).
% 6.20/1.18  fof(f65,plain,(
% 6.20/1.18    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f44])).
% 6.20/1.18  fof(f44,plain,(
% 6.20/1.18    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 6.20/1.18    inference(nnf_transformation,[],[f13])).
% 6.20/1.18  fof(f13,axiom,(
% 6.20/1.18    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 6.20/1.18  fof(f2124,plain,(
% 6.20/1.18    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 6.20/1.18    inference(subsumption_resolution,[],[f2118,f55])).
% 6.20/1.18  fof(f55,plain,(
% 6.20/1.18    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f7])).
% 6.20/1.18  fof(f7,axiom,(
% 6.20/1.18    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 6.20/1.18  fof(f2118,plain,(
% 6.20/1.18    ( ! [X2,X0,X1] : (r1_xboole_0(k1_xboole_0,X0) | ~r1_tarski(k1_xboole_0,k4_xboole_0(X1,X2))) )),
% 6.20/1.18    inference(resolution,[],[f2101,f80])).
% 6.20/1.18  fof(f2101,plain,(
% 6.20/1.18    ( ! [X0,X1] : (~r1_xboole_0(k1_xboole_0,X0) | r1_xboole_0(k1_xboole_0,X1)) )),
% 6.20/1.18    inference(superposition,[],[f2075,f65])).
% 6.20/1.18  fof(f2075,plain,(
% 6.20/1.18    ( ! [X28,X29] : (r1_xboole_0(k4_xboole_0(k1_xboole_0,X28),X29)) )),
% 6.20/1.18    inference(resolution,[],[f2061,f80])).
% 6.20/1.18  fof(f2061,plain,(
% 6.20/1.18    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k1_xboole_0,X0),X1)) )),
% 6.20/1.18    inference(resolution,[],[f2043,f68])).
% 6.20/1.18  fof(f68,plain,(
% 6.20/1.18    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK3(X0,X1),X0)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f48])).
% 6.20/1.18  fof(f48,plain,(
% 6.20/1.18    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.20/1.18    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f46,f47])).
% 6.20/1.18  fof(f47,plain,(
% 6.20/1.18    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 6.20/1.18    introduced(choice_axiom,[])).
% 6.20/1.18  fof(f46,plain,(
% 6.20/1.18    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 6.20/1.18    inference(rectify,[],[f45])).
% 6.20/1.18  fof(f45,plain,(
% 6.20/1.18    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 6.20/1.18    inference(nnf_transformation,[],[f27])).
% 6.20/1.18  fof(f27,plain,(
% 6.20/1.18    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.20/1.18    inference(ennf_transformation,[],[f1])).
% 6.20/1.18  fof(f1,axiom,(
% 6.20/1.18    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 6.20/1.18  fof(f2043,plain,(
% 6.20/1.18    ( ! [X14,X15] : (~r2_hidden(X14,k4_xboole_0(k1_xboole_0,X15))) )),
% 6.20/1.18    inference(resolution,[],[f2026,f60])).
% 6.20/1.18  fof(f2026,plain,(
% 6.20/1.18    ( ! [X2,X1] : (~r1_tarski(X2,k1_xboole_0) | ~r2_hidden(X1,X2)) )),
% 6.20/1.18    inference(resolution,[],[f2014,f67])).
% 6.20/1.18  fof(f67,plain,(
% 6.20/1.18    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f48])).
% 6.20/1.18  fof(f2014,plain,(
% 6.20/1.18    ( ! [X36] : (~r2_hidden(X36,k1_xboole_0)) )),
% 6.20/1.18    inference(resolution,[],[f232,f55])).
% 6.20/1.18  fof(f232,plain,(
% 6.20/1.18    ( ! [X2,X1] : (~r1_tarski(X2,k4_xboole_0(sK1,u1_struct_0(sK0))) | ~r2_hidden(X1,X2)) )),
% 6.20/1.18    inference(resolution,[],[f219,f67])).
% 6.20/1.18  fof(f219,plain,(
% 6.20/1.18    ( ! [X7] : (~r2_hidden(X7,k4_xboole_0(sK1,u1_struct_0(sK0)))) )),
% 6.20/1.18    inference(resolution,[],[f201,f72])).
% 6.20/1.18  fof(f72,plain,(
% 6.20/1.18    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f28])).
% 6.20/1.18  fof(f28,plain,(
% 6.20/1.18    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 6.20/1.18    inference(ennf_transformation,[],[f17])).
% 6.20/1.18  fof(f17,axiom,(
% 6.20/1.18    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 6.20/1.18  fof(f201,plain,(
% 6.20/1.18    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,u1_struct_0(sK0)),X0)) )),
% 6.20/1.18    inference(resolution,[],[f199,f78])).
% 6.20/1.18  fof(f199,plain,(
% 6.20/1.18    ( ! [X9] : (r1_tarski(sK1,k2_xboole_0(u1_struct_0(sK0),X9))) )),
% 6.20/1.18    inference(resolution,[],[f105,f59])).
% 6.20/1.18  fof(f59,plain,(
% 6.20/1.18    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 6.20/1.18    inference(cnf_transformation,[],[f12])).
% 6.20/1.18  fof(f12,axiom,(
% 6.20/1.18    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 6.20/1.18  fof(f105,plain,(
% 6.20/1.18    ( ! [X5] : (~r1_tarski(u1_struct_0(sK0),X5) | r1_tarski(sK1,X5)) )),
% 6.20/1.18    inference(resolution,[],[f91,f82])).
% 6.20/1.18  fof(f82,plain,(
% 6.20/1.18    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f37])).
% 6.20/1.18  fof(f37,plain,(
% 6.20/1.18    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 6.20/1.18    inference(flattening,[],[f36])).
% 6.20/1.18  fof(f36,plain,(
% 6.20/1.18    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 6.20/1.18    inference(ennf_transformation,[],[f6])).
% 6.20/1.18  fof(f6,axiom,(
% 6.20/1.18    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 6.20/1.18  fof(f2141,plain,(
% 6.20/1.18    ( ! [X4,X3] : (~r1_tarski(X3,k1_xboole_0) | k4_xboole_0(k1_xboole_0,X4) = X3) )),
% 6.20/1.18    inference(backward_demodulation,[],[f2065,f2129])).
% 6.20/1.18  fof(f2065,plain,(
% 6.20/1.18    ( ! [X4,X3] : (k4_xboole_0(k1_xboole_0,X4) = X3 | ~r1_tarski(X3,k4_xboole_0(k1_xboole_0,X4))) )),
% 6.20/1.18    inference(resolution,[],[f2061,f64])).
% 6.20/1.18  fof(f64,plain,(
% 6.20/1.18    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f43])).
% 6.20/1.18  fof(f43,plain,(
% 6.20/1.18    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.20/1.18    inference(flattening,[],[f42])).
% 6.20/1.18  fof(f42,plain,(
% 6.20/1.18    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 6.20/1.18    inference(nnf_transformation,[],[f2])).
% 6.20/1.18  fof(f2,axiom,(
% 6.20/1.18    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.20/1.18  fof(f61,plain,(
% 6.20/1.18    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f9])).
% 6.20/1.18  fof(f9,axiom,(
% 6.20/1.18    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 6.20/1.18  fof(f75,plain,(
% 6.20/1.18    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f29])).
% 6.20/1.18  fof(f29,plain,(
% 6.20/1.18    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 6.20/1.18    inference(ennf_transformation,[],[f11])).
% 6.20/1.18  fof(f11,axiom,(
% 6.20/1.18    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 6.20/1.18  fof(f1310,plain,(
% 6.20/1.18    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 6.20/1.18    inference(resolution,[],[f1175,f81])).
% 6.20/1.18  fof(f81,plain,(
% 6.20/1.18    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 6.20/1.18    inference(cnf_transformation,[],[f35])).
% 6.20/1.18  fof(f35,plain,(
% 6.20/1.18    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 6.20/1.18    inference(flattening,[],[f34])).
% 6.20/1.18  fof(f34,plain,(
% 6.20/1.18    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 6.20/1.18    inference(ennf_transformation,[],[f14])).
% 6.20/1.18  fof(f14,axiom,(
% 6.20/1.18    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 6.20/1.18  fof(f1175,plain,(
% 6.20/1.18    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 6.20/1.18    inference(backward_demodulation,[],[f95,f1171])).
% 6.20/1.18  fof(f1171,plain,(
% 6.20/1.18    ( ! [X2] : (k4_xboole_0(k1_tops_1(sK0,sK1),X2) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X2)) )),
% 6.20/1.18    inference(resolution,[],[f1160,f77])).
% 6.20/1.18  fof(f77,plain,(
% 6.20/1.18    ( ! [X2,X0,X1] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 6.20/1.18    inference(cnf_transformation,[],[f31])).
% 6.20/1.18  fof(f31,plain,(
% 6.20/1.18    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 6.20/1.18    inference(ennf_transformation,[],[f15])).
% 6.20/1.18  fof(f15,axiom,(
% 6.20/1.18    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 6.20/1.18    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 6.20/1.18  fof(f1160,plain,(
% 6.20/1.18    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 6.20/1.18    inference(resolution,[],[f1153,f71])).
% 6.20/1.18  fof(f1153,plain,(
% 6.20/1.18    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 6.20/1.18    inference(superposition,[],[f1138,f56])).
% 6.20/1.18  fof(f1138,plain,(
% 6.20/1.18    ( ! [X36] : (r1_tarski(k1_tops_1(sK0,sK1),k2_xboole_0(u1_struct_0(sK0),X36))) )),
% 6.20/1.18    inference(resolution,[],[f210,f94])).
% 6.20/1.18  fof(f94,plain,(
% 6.20/1.18    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 6.20/1.18    inference(subsumption_resolution,[],[f89,f51])).
% 6.20/1.18  fof(f89,plain,(
% 6.20/1.18    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0)),
% 6.20/1.18    inference(resolution,[],[f52,f57])).
% 6.20/1.18  fof(f210,plain,(
% 6.20/1.18    ( ! [X14,X13] : (~r1_tarski(X13,sK1) | r1_tarski(X13,k2_xboole_0(u1_struct_0(sK0),X14))) )),
% 6.20/1.18    inference(resolution,[],[f199,f82])).
% 6.20/1.18  fof(f95,plain,(
% 6.20/1.18    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 6.20/1.18    inference(backward_demodulation,[],[f54,f90])).
% 6.20/1.18  fof(f90,plain,(
% 6.20/1.18    ( ! [X2] : (k7_subset_1(u1_struct_0(sK0),sK1,X2) = k4_xboole_0(sK1,X2)) )),
% 6.20/1.18    inference(resolution,[],[f52,f77])).
% 6.20/1.18  fof(f54,plain,(
% 6.20/1.18    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 6.20/1.18    inference(cnf_transformation,[],[f41])).
% 6.20/1.18  % SZS output end Proof for theBenchmark
% 6.20/1.18  % (4327)------------------------------
% 6.20/1.18  % (4327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.20/1.18  % (4327)Termination reason: Refutation
% 6.20/1.18  
% 6.20/1.18  % (4327)Memory used [KB]: 5245
% 6.20/1.18  % (4327)Time elapsed: 0.739 s
% 6.20/1.18  % (4327)------------------------------
% 6.20/1.18  % (4327)------------------------------
% 6.20/1.18  % (4303)Success in time 0.804 s
%------------------------------------------------------------------------------
