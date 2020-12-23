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
% DateTime   : Thu Dec  3 13:11:14 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.39s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 193 expanded)
%              Number of leaves         :   10 (  43 expanded)
%              Depth                    :   19
%              Number of atoms          :  159 ( 553 expanded)
%              Number of equality atoms :   14 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1080,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1079,f81])).

fof(f81,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f78,f40])).

fof(f40,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f78,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k4_xboole_0(sK1,X2))
      | r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f55,f30])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(X1,X0)
      | r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f52,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f52,plain,(
    ! [X6] :
      ( r1_tarski(X6,u1_struct_0(sK0))
      | ~ r1_tarski(X6,sK1) ) ),
    inference(resolution,[],[f39,f43])).

fof(f43,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f35,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f1079,plain,(
    ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f1078,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1078,plain,(
    ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1077,f27])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1077,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1076,f30])).

fof(f1076,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1075,f25])).

fof(f1075,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f1074,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).

fof(f1074,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1073,f780])).

fof(f780,plain,(
    r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f750,f353])).

fof(f353,plain,(
    ! [X13] : r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X13)),k4_xboole_0(sK1,X13)) ),
    inference(resolution,[],[f311,f81])).

fof(f311,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f222,f34])).

fof(f222,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f28,f27])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f750,plain,(
    ! [X12,X11] :
      ( ~ r1_tarski(X12,k4_xboole_0(X11,sK2))
      | r1_xboole_0(X12,k1_tops_1(sK0,sK2)) ) ),
    inference(superposition,[],[f36,f314])).

fof(f314,plain,(
    ! [X2] : k1_tops_1(sK0,sK2) = k4_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(X2,sK2)) ),
    inference(resolution,[],[f309,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X2)
      | k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0 ) ),
    inference(resolution,[],[f99,f36])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(subsumption_resolution,[],[f98,f40])).

fof(f98,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X0) ) ),
    inference(resolution,[],[f46,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f46,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k4_xboole_0(X1,X2))
      | k4_xboole_0(X1,X2) = X1 ) ),
    inference(resolution,[],[f33,f30])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f309,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f222,f23])).

fof(f23,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f1073,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f836,f38])).

fof(f836,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f387,f815])).

fof(f815,plain,(
    ! [X67] : k4_xboole_0(k1_tops_1(sK0,sK1),X67) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X67) ),
    inference(resolution,[],[f386,f393])).

fof(f393,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f318,f40])).

fof(f318,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_tops_1(sK0,sK1))
      | r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f310,f55])).

fof(f310,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f222,f25])).

fof(f386,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X4)
      | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3) ) ),
    inference(resolution,[],[f37,f34])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f387,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f24,f385])).

fof(f385,plain,(
    ! [X1] : k4_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,X1) ),
    inference(resolution,[],[f37,f25])).

fof(f24,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:29:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.37  ipcrm: permission denied for id (787283969)
% 0.22/0.38  ipcrm: permission denied for id (788365315)
% 0.22/0.38  ipcrm: permission denied for id (788398084)
% 0.22/0.38  ipcrm: permission denied for id (787349509)
% 0.22/0.38  ipcrm: permission denied for id (787382279)
% 0.22/0.39  ipcrm: permission denied for id (788561931)
% 0.22/0.39  ipcrm: permission denied for id (787480588)
% 0.22/0.39  ipcrm: permission denied for id (788660239)
% 0.22/0.39  ipcrm: permission denied for id (788693008)
% 0.22/0.39  ipcrm: permission denied for id (788725777)
% 0.22/0.40  ipcrm: permission denied for id (787546130)
% 0.22/0.40  ipcrm: permission denied for id (788758547)
% 0.22/0.40  ipcrm: permission denied for id (788791316)
% 0.22/0.40  ipcrm: permission denied for id (788824085)
% 0.22/0.41  ipcrm: permission denied for id (788987929)
% 0.22/0.41  ipcrm: permission denied for id (789053467)
% 0.22/0.42  ipcrm: permission denied for id (789282850)
% 0.22/0.42  ipcrm: permission denied for id (789413924)
% 0.22/0.43  ipcrm: permission denied for id (789446693)
% 0.22/0.43  ipcrm: permission denied for id (789479462)
% 0.22/0.43  ipcrm: permission denied for id (789512231)
% 0.22/0.43  ipcrm: permission denied for id (789545000)
% 0.22/0.44  ipcrm: permission denied for id (789643307)
% 0.22/0.44  ipcrm: permission denied for id (789708845)
% 0.22/0.44  ipcrm: permission denied for id (789774383)
% 0.22/0.44  ipcrm: permission denied for id (789807152)
% 0.22/0.45  ipcrm: permission denied for id (789905459)
% 0.22/0.45  ipcrm: permission denied for id (789970997)
% 0.22/0.45  ipcrm: permission denied for id (787677239)
% 0.22/0.46  ipcrm: permission denied for id (787710008)
% 0.22/0.46  ipcrm: permission denied for id (787742778)
% 0.22/0.46  ipcrm: permission denied for id (790102076)
% 0.22/0.46  ipcrm: permission denied for id (790134845)
% 0.22/0.46  ipcrm: permission denied for id (787775551)
% 0.22/0.47  ipcrm: permission denied for id (787808321)
% 0.22/0.47  ipcrm: permission denied for id (790265922)
% 0.22/0.47  ipcrm: permission denied for id (790298691)
% 0.22/0.47  ipcrm: permission denied for id (790331460)
% 0.22/0.47  ipcrm: permission denied for id (787841093)
% 0.22/0.47  ipcrm: permission denied for id (790364230)
% 0.22/0.47  ipcrm: permission denied for id (790396999)
% 0.22/0.48  ipcrm: permission denied for id (790593612)
% 0.22/0.48  ipcrm: permission denied for id (790659150)
% 0.22/0.48  ipcrm: permission denied for id (790691919)
% 0.22/0.48  ipcrm: permission denied for id (790790226)
% 0.22/0.48  ipcrm: permission denied for id (790822995)
% 0.22/0.49  ipcrm: permission denied for id (790921302)
% 0.22/0.49  ipcrm: permission denied for id (790986840)
% 0.22/0.50  ipcrm: permission denied for id (791117916)
% 0.22/0.50  ipcrm: permission denied for id (788004957)
% 0.22/0.50  ipcrm: permission denied for id (791216224)
% 0.22/0.50  ipcrm: permission denied for id (791248993)
% 0.22/0.50  ipcrm: permission denied for id (791314531)
% 0.22/0.50  ipcrm: permission denied for id (791347300)
% 0.22/0.51  ipcrm: permission denied for id (791445607)
% 0.22/0.51  ipcrm: permission denied for id (788070506)
% 0.22/0.51  ipcrm: permission denied for id (791576683)
% 0.22/0.51  ipcrm: permission denied for id (791609452)
% 0.22/0.52  ipcrm: permission denied for id (791674990)
% 0.22/0.52  ipcrm: permission denied for id (788103281)
% 0.22/0.52  ipcrm: permission denied for id (791937142)
% 0.22/0.53  ipcrm: permission denied for id (791969911)
% 0.22/0.53  ipcrm: permission denied for id (792002680)
% 0.22/0.53  ipcrm: permission denied for id (792035449)
% 0.22/0.53  ipcrm: permission denied for id (792068218)
% 0.22/0.53  ipcrm: permission denied for id (788267131)
% 0.22/0.53  ipcrm: permission denied for id (792100988)
% 0.22/0.53  ipcrm: permission denied for id (792133757)
% 0.22/0.53  ipcrm: permission denied for id (792166526)
% 0.39/0.64  % (17112)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.39/0.64  % (17122)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.39/0.65  % (17118)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.39/0.65  % (17125)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.39/0.65  % (17127)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.39/0.65  % (17110)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.39/0.65  % (17126)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.39/0.65  % (17114)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.39/0.67  % (17113)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.39/0.67  % (17106)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.39/0.67  % (17111)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.39/0.69  % (17107)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.39/0.69  % (17115)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.39/0.69  % (17119)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.39/0.69  % (17108)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.39/0.69  % (17104)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.39/0.69  % (17109)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.39/0.69  % (17128)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.39/0.70  % (17123)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.39/0.70  % (17120)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.39/0.70  % (17105)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.39/0.70  % (17117)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.39/0.71  % (17129)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.39/0.72  % (17116)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.39/0.72  % (17124)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.39/0.73  % (17121)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.39/0.75  % (17123)Refutation found. Thanks to Tanya!
% 0.39/0.75  % SZS status Theorem for theBenchmark
% 0.39/0.75  % SZS output start Proof for theBenchmark
% 0.39/0.75  fof(f1080,plain,(
% 0.39/0.75    $false),
% 0.39/0.75    inference(subsumption_resolution,[],[f1079,f81])).
% 0.39/0.75  fof(f81,plain,(
% 0.39/0.75    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))) )),
% 0.39/0.75    inference(resolution,[],[f78,f40])).
% 0.39/0.75  fof(f40,plain,(
% 0.39/0.75    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.39/0.75    inference(equality_resolution,[],[f32])).
% 0.39/0.75  fof(f32,plain,(
% 0.39/0.75    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.39/0.75    inference(cnf_transformation,[],[f1])).
% 0.39/0.75  fof(f1,axiom,(
% 0.39/0.75    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.39/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.39/0.75  fof(f78,plain,(
% 0.39/0.75    ( ! [X2,X1] : (~r1_tarski(X1,k4_xboole_0(sK1,X2)) | r1_tarski(X1,u1_struct_0(sK0))) )),
% 0.39/0.75    inference(resolution,[],[f55,f30])).
% 0.39/0.75  fof(f30,plain,(
% 0.39/0.75    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.39/0.75    inference(cnf_transformation,[],[f3])).
% 0.39/0.75  fof(f3,axiom,(
% 0.39/0.75    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.39/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.39/0.75  fof(f55,plain,(
% 0.39/0.75    ( ! [X0,X1] : (~r1_tarski(X0,sK1) | ~r1_tarski(X1,X0) | r1_tarski(X1,u1_struct_0(sK0))) )),
% 0.39/0.75    inference(resolution,[],[f52,f39])).
% 0.39/0.75  fof(f39,plain,(
% 0.39/0.75    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 0.39/0.75    inference(cnf_transformation,[],[f22])).
% 0.39/0.75  fof(f22,plain,(
% 0.39/0.75    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.39/0.75    inference(flattening,[],[f21])).
% 0.39/0.75  fof(f21,plain,(
% 0.39/0.75    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.39/0.75    inference(ennf_transformation,[],[f2])).
% 0.39/0.75  fof(f2,axiom,(
% 0.39/0.75    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.39/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.39/0.75  fof(f52,plain,(
% 0.39/0.75    ( ! [X6] : (r1_tarski(X6,u1_struct_0(sK0)) | ~r1_tarski(X6,sK1)) )),
% 0.39/0.75    inference(resolution,[],[f39,f43])).
% 0.39/0.75  fof(f43,plain,(
% 0.39/0.75    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.39/0.75    inference(resolution,[],[f35,f25])).
% 0.39/0.75  fof(f25,plain,(
% 0.39/0.75    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.39/0.75    inference(cnf_transformation,[],[f13])).
% 0.39/0.75  fof(f13,plain,(
% 0.39/0.75    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.39/0.75    inference(flattening,[],[f12])).
% 0.39/0.75  fof(f12,plain,(
% 0.39/0.75    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.39/0.75    inference(ennf_transformation,[],[f11])).
% 0.39/0.75  fof(f11,negated_conjecture,(
% 0.39/0.75    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.39/0.75    inference(negated_conjecture,[],[f10])).
% 0.39/0.75  fof(f10,conjecture,(
% 0.39/0.75    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.39/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tops_1)).
% 0.39/0.75  fof(f35,plain,(
% 0.39/0.75    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.39/0.75    inference(cnf_transformation,[],[f7])).
% 0.39/0.75  fof(f7,axiom,(
% 0.39/0.75    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.39/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.39/0.75  fof(f1079,plain,(
% 0.39/0.75    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 0.39/0.75    inference(resolution,[],[f1078,f34])).
% 0.39/0.75  fof(f34,plain,(
% 0.39/0.75    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.39/0.75    inference(cnf_transformation,[],[f7])).
% 0.39/0.75  fof(f1078,plain,(
% 0.39/0.75    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.39/0.75    inference(subsumption_resolution,[],[f1077,f27])).
% 0.39/0.75  fof(f27,plain,(
% 0.39/0.75    l1_pre_topc(sK0)),
% 0.39/0.75    inference(cnf_transformation,[],[f13])).
% 0.39/0.75  fof(f1077,plain,(
% 0.39/0.75    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 0.39/0.75    inference(subsumption_resolution,[],[f1076,f30])).
% 0.39/0.75  fof(f1076,plain,(
% 0.39/0.75    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~l1_pre_topc(sK0)),
% 0.39/0.75    inference(subsumption_resolution,[],[f1075,f25])).
% 0.39/0.75  fof(f1075,plain,(
% 0.39/0.75    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~l1_pre_topc(sK0)),
% 0.39/0.75    inference(resolution,[],[f1074,f29])).
% 0.39/0.75  fof(f29,plain,(
% 0.39/0.75    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 0.39/0.75    inference(cnf_transformation,[],[f16])).
% 0.39/0.75  fof(f16,plain,(
% 0.39/0.75    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.39/0.75    inference(flattening,[],[f15])).
% 0.39/0.75  fof(f15,plain,(
% 0.39/0.75    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.39/0.75    inference(ennf_transformation,[],[f9])).
% 0.39/0.75  fof(f9,axiom,(
% 0.39/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.39/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tops_1)).
% 0.39/0.75  fof(f1074,plain,(
% 0.39/0.75    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 0.39/0.75    inference(subsumption_resolution,[],[f1073,f780])).
% 0.39/0.75  fof(f780,plain,(
% 0.39/0.75    r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))),
% 0.39/0.75    inference(resolution,[],[f750,f353])).
% 0.39/0.75  fof(f353,plain,(
% 0.39/0.75    ( ! [X13] : (r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X13)),k4_xboole_0(sK1,X13))) )),
% 0.39/0.75    inference(resolution,[],[f311,f81])).
% 0.39/0.75  fof(f311,plain,(
% 0.39/0.75    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 0.39/0.75    inference(resolution,[],[f222,f34])).
% 0.39/0.75  fof(f222,plain,(
% 0.39/0.75    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 0.39/0.75    inference(resolution,[],[f28,f27])).
% 0.39/0.75  fof(f28,plain,(
% 0.39/0.75    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.39/0.75    inference(cnf_transformation,[],[f14])).
% 0.39/0.75  fof(f14,plain,(
% 0.39/0.75    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.39/0.75    inference(ennf_transformation,[],[f8])).
% 0.39/0.75  fof(f8,axiom,(
% 0.39/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.39/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.39/0.75  fof(f750,plain,(
% 0.39/0.75    ( ! [X12,X11] : (~r1_tarski(X12,k4_xboole_0(X11,sK2)) | r1_xboole_0(X12,k1_tops_1(sK0,sK2))) )),
% 0.39/0.75    inference(superposition,[],[f36,f314])).
% 0.39/0.75  fof(f314,plain,(
% 0.39/0.75    ( ! [X2] : (k1_tops_1(sK0,sK2) = k4_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(X2,sK2))) )),
% 0.39/0.75    inference(resolution,[],[f309,f100])).
% 0.39/0.75  fof(f100,plain,(
% 0.39/0.75    ( ! [X2,X0,X1] : (~r1_tarski(X0,X2) | k4_xboole_0(X0,k4_xboole_0(X1,X2)) = X0) )),
% 0.39/0.75    inference(resolution,[],[f99,f36])).
% 0.39/0.75  fof(f99,plain,(
% 0.39/0.75    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.39/0.75    inference(subsumption_resolution,[],[f98,f40])).
% 0.39/0.75  fof(f98,plain,(
% 0.39/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1) | ~r1_tarski(X0,X0)) )),
% 0.39/0.75    inference(resolution,[],[f46,f38])).
% 0.39/0.75  fof(f38,plain,(
% 0.39/0.75    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.39/0.75    inference(cnf_transformation,[],[f20])).
% 0.39/0.75  fof(f20,plain,(
% 0.39/0.75    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 0.39/0.75    inference(flattening,[],[f19])).
% 0.39/0.75  fof(f19,plain,(
% 0.39/0.75    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.39/0.75    inference(ennf_transformation,[],[f5])).
% 0.39/0.75  fof(f5,axiom,(
% 0.39/0.75    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.39/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_xboole_1)).
% 0.39/0.75  fof(f46,plain,(
% 0.39/0.75    ( ! [X2,X1] : (~r1_tarski(X1,k4_xboole_0(X1,X2)) | k4_xboole_0(X1,X2) = X1) )),
% 0.39/0.75    inference(resolution,[],[f33,f30])).
% 0.39/0.75  fof(f33,plain,(
% 0.39/0.75    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.39/0.75    inference(cnf_transformation,[],[f1])).
% 0.39/0.75  fof(f309,plain,(
% 0.39/0.75    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.39/0.75    inference(resolution,[],[f222,f23])).
% 0.39/0.75  fof(f23,plain,(
% 0.39/0.75    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.39/0.75    inference(cnf_transformation,[],[f13])).
% 0.39/0.75  fof(f36,plain,(
% 0.39/0.75    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.39/0.75    inference(cnf_transformation,[],[f17])).
% 0.39/0.75  fof(f17,plain,(
% 0.39/0.75    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.39/0.75    inference(ennf_transformation,[],[f4])).
% 0.39/0.75  fof(f4,axiom,(
% 0.39/0.75    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 0.39/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).
% 0.39/0.75  fof(f1073,plain,(
% 0.39/0.75    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 0.39/0.75    inference(resolution,[],[f836,f38])).
% 0.39/0.75  fof(f836,plain,(
% 0.39/0.75    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 0.39/0.75    inference(backward_demodulation,[],[f387,f815])).
% 0.39/0.75  fof(f815,plain,(
% 0.39/0.75    ( ! [X67] : (k4_xboole_0(k1_tops_1(sK0,sK1),X67) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X67)) )),
% 0.39/0.75    inference(resolution,[],[f386,f393])).
% 0.39/0.75  fof(f393,plain,(
% 0.39/0.75    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 0.39/0.75    inference(resolution,[],[f318,f40])).
% 0.39/0.75  fof(f318,plain,(
% 0.39/0.75    ( ! [X1] : (~r1_tarski(X1,k1_tops_1(sK0,sK1)) | r1_tarski(X1,u1_struct_0(sK0))) )),
% 0.39/0.75    inference(resolution,[],[f310,f55])).
% 0.39/0.75  fof(f310,plain,(
% 0.39/0.75    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.39/0.75    inference(resolution,[],[f222,f25])).
% 0.39/0.75  fof(f386,plain,(
% 0.39/0.75    ( ! [X4,X2,X3] : (~r1_tarski(X2,X4) | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3)) )),
% 0.39/0.75    inference(resolution,[],[f37,f34])).
% 0.39/0.75  fof(f37,plain,(
% 0.39/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 0.39/0.75    inference(cnf_transformation,[],[f18])).
% 0.39/0.75  fof(f18,plain,(
% 0.39/0.75    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.39/0.75    inference(ennf_transformation,[],[f6])).
% 0.39/0.75  fof(f6,axiom,(
% 0.39/0.75    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 0.39/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.39/0.75  fof(f387,plain,(
% 0.39/0.75    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 0.39/0.75    inference(backward_demodulation,[],[f24,f385])).
% 0.39/0.75  fof(f385,plain,(
% 0.39/0.75    ( ! [X1] : (k4_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,X1)) )),
% 0.39/0.75    inference(resolution,[],[f37,f25])).
% 0.39/0.75  fof(f24,plain,(
% 0.39/0.75    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 0.39/0.75    inference(cnf_transformation,[],[f13])).
% 0.39/0.75  % SZS output end Proof for theBenchmark
% 0.39/0.75  % (17123)------------------------------
% 0.39/0.75  % (17123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.75  % (17123)Termination reason: Refutation
% 0.39/0.75  
% 0.39/0.75  % (17123)Memory used [KB]: 2686
% 0.39/0.75  % (17123)Time elapsed: 0.173 s
% 0.39/0.75  % (17123)------------------------------
% 0.39/0.75  % (17123)------------------------------
% 0.39/0.78  % (16940)Success in time 0.414 s
%------------------------------------------------------------------------------
