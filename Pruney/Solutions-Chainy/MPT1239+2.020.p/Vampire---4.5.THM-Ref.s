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
% DateTime   : Thu Dec  3 13:11:13 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 198 expanded)
%              Number of leaves         :   10 (  43 expanded)
%              Depth                    :   20
%              Number of atoms          :  170 ( 579 expanded)
%              Number of equality atoms :    8 (  23 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1355,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1354,f76])).

fof(f76,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0)) ),
    inference(resolution,[],[f73,f43])).

fof(f43,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f73,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(X1,k4_xboole_0(sK1,X2))
      | r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f64,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f38,f43])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(X1,X0)
      | r1_tarski(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f62,f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f62,plain,(
    ! [X9] :
      ( r1_tarski(X9,u1_struct_0(sK0))
      | ~ r1_tarski(X9,sK1) ) ),
    inference(resolution,[],[f41,f46])).

fof(f46,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f36,f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1354,plain,(
    ~ r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0)) ),
    inference(resolution,[],[f1353,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f1353,plain,(
    ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1352,f29])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f1352,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1351,f48])).

fof(f1351,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f1350,f27])).

fof(f1350,plain,
    ( ~ m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f1349,f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f1349,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1348,f216])).

fof(f216,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f211,f25])).

fof(f25,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f211,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f30,f29])).

fof(f30,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f1348,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f829,f808])).

fof(f808,plain,(
    ! [X35,X36] :
      ( r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X36)),X35)
      | ~ r1_tarski(X35,X36) ) ),
    inference(resolution,[],[f318,f244])).

fof(f244,plain,(
    ! [X2] : r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X2)),k4_xboole_0(sK1,X2)) ),
    inference(resolution,[],[f218,f76])).

fof(f218,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f211,f35])).

fof(f318,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X2,k4_xboole_0(X3,X1))
      | ~ r1_tarski(X0,X1)
      | r1_xboole_0(X2,X0) ) ),
    inference(resolution,[],[f42,f51])).

fof(f51,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(resolution,[],[f39,f43])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f829,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f735,f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f735,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f215,f721])).

fof(f721,plain,(
    ! [X168] : k4_xboole_0(k1_tops_1(sK0,sK1),X168) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X168) ),
    inference(resolution,[],[f214,f286])).

fof(f286,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f222,f43])).

fof(f222,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_tops_1(sK0,sK1))
      | r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f217,f64])).

fof(f217,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f211,f27])).

fof(f214,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X2,X4)
      | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3) ) ),
    inference(resolution,[],[f37,f35])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f215,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f26,f213])).

fof(f213,plain,(
    ! [X1] : k4_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,X1) ),
    inference(resolution,[],[f37,f27])).

fof(f26,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n005.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:46:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.23/0.53  % (29283)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.23/0.54  % (29304)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.40/0.54  % (29297)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.40/0.54  % (29294)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.40/0.54  % (29286)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.40/0.55  % (29282)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.40/0.55  % (29292)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.40/0.55  % (29281)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.40/0.55  % (29289)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.40/0.55  % (29299)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.40/0.55  % (29291)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.40/0.55  % (29303)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.40/0.56  % (29298)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.40/0.56  % (29285)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.40/0.56  % (29290)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.40/0.56  % (29300)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.40/0.56  % (29280)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.40/0.56  % (29284)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.40/0.56  % (29293)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.40/0.57  % (29296)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.40/0.57  % (29302)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.40/0.57  % (29301)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.40/0.57  % (29288)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.40/0.58  % (29279)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.40/0.59  % (29287)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.40/0.59  % (29295)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 2.10/0.68  % (29298)Refutation found. Thanks to Tanya!
% 2.10/0.68  % SZS status Theorem for theBenchmark
% 2.10/0.68  % SZS output start Proof for theBenchmark
% 2.10/0.68  fof(f1355,plain,(
% 2.10/0.68    $false),
% 2.10/0.68    inference(subsumption_resolution,[],[f1354,f76])).
% 2.10/0.68  fof(f76,plain,(
% 2.10/0.68    ( ! [X0] : (r1_tarski(k4_xboole_0(sK1,X0),u1_struct_0(sK0))) )),
% 2.10/0.68    inference(resolution,[],[f73,f43])).
% 2.10/0.68  fof(f43,plain,(
% 2.10/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.10/0.68    inference(equality_resolution,[],[f33])).
% 2.10/0.68  fof(f33,plain,(
% 2.10/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.10/0.68    inference(cnf_transformation,[],[f1])).
% 2.10/0.68  fof(f1,axiom,(
% 2.10/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.10/0.68  fof(f73,plain,(
% 2.10/0.68    ( ! [X2,X1] : (~r1_tarski(X1,k4_xboole_0(sK1,X2)) | r1_tarski(X1,u1_struct_0(sK0))) )),
% 2.10/0.68    inference(resolution,[],[f64,f48])).
% 2.10/0.68  fof(f48,plain,(
% 2.10/0.68    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.10/0.68    inference(resolution,[],[f38,f43])).
% 2.10/0.68  fof(f38,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f18])).
% 2.10/0.68  fof(f18,plain,(
% 2.10/0.68    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.10/0.68    inference(ennf_transformation,[],[f2])).
% 2.10/0.68  fof(f2,axiom,(
% 2.10/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.10/0.68  fof(f64,plain,(
% 2.10/0.68    ( ! [X0,X1] : (~r1_tarski(X0,sK1) | ~r1_tarski(X1,X0) | r1_tarski(X1,u1_struct_0(sK0))) )),
% 2.10/0.68    inference(resolution,[],[f62,f41])).
% 2.10/0.68  fof(f41,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f22])).
% 2.10/0.68  fof(f22,plain,(
% 2.10/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.10/0.68    inference(flattening,[],[f21])).
% 2.10/0.68  fof(f21,plain,(
% 2.10/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.10/0.68    inference(ennf_transformation,[],[f3])).
% 2.10/0.68  fof(f3,axiom,(
% 2.10/0.68    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.10/0.68  fof(f62,plain,(
% 2.10/0.68    ( ! [X9] : (r1_tarski(X9,u1_struct_0(sK0)) | ~r1_tarski(X9,sK1)) )),
% 2.10/0.68    inference(resolution,[],[f41,f46])).
% 2.10/0.68  fof(f46,plain,(
% 2.10/0.68    r1_tarski(sK1,u1_struct_0(sK0))),
% 2.10/0.68    inference(resolution,[],[f36,f27])).
% 2.10/0.68  fof(f27,plain,(
% 2.10/0.68    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.10/0.68    inference(cnf_transformation,[],[f13])).
% 2.10/0.68  fof(f13,plain,(
% 2.10/0.68    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.10/0.68    inference(flattening,[],[f12])).
% 2.10/0.68  fof(f12,plain,(
% 2.10/0.68    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.10/0.68    inference(ennf_transformation,[],[f11])).
% 2.10/0.68  fof(f11,negated_conjecture,(
% 2.10/0.68    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.10/0.68    inference(negated_conjecture,[],[f10])).
% 2.10/0.68  fof(f10,conjecture,(
% 2.10/0.68    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).
% 2.10/0.68  fof(f36,plain,(
% 2.10/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f7])).
% 2.10/0.68  fof(f7,axiom,(
% 2.10/0.68    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.10/0.68  fof(f1354,plain,(
% 2.10/0.68    ~r1_tarski(k4_xboole_0(sK1,sK2),u1_struct_0(sK0))),
% 2.10/0.68    inference(resolution,[],[f1353,f35])).
% 2.10/0.68  fof(f35,plain,(
% 2.10/0.68    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f7])).
% 2.10/0.68  fof(f1353,plain,(
% 2.10/0.68    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.10/0.68    inference(subsumption_resolution,[],[f1352,f29])).
% 2.10/0.68  fof(f29,plain,(
% 2.10/0.68    l1_pre_topc(sK0)),
% 2.10/0.68    inference(cnf_transformation,[],[f13])).
% 2.10/0.68  fof(f1352,plain,(
% 2.10/0.68    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1351,f48])).
% 2.10/0.68  fof(f1351,plain,(
% 2.10/0.68    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~l1_pre_topc(sK0)),
% 2.10/0.68    inference(subsumption_resolution,[],[f1350,f27])).
% 2.10/0.68  fof(f1350,plain,(
% 2.10/0.68    ~m1_subset_1(k4_xboole_0(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | ~l1_pre_topc(sK0)),
% 2.10/0.68    inference(resolution,[],[f1349,f31])).
% 2.10/0.68  fof(f31,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f16])).
% 2.10/0.68  fof(f16,plain,(
% 2.10/0.68    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.68    inference(flattening,[],[f15])).
% 2.10/0.68  fof(f15,plain,(
% 2.10/0.68    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.68    inference(ennf_transformation,[],[f9])).
% 2.10/0.68  fof(f9,axiom,(
% 2.10/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 2.10/0.68  fof(f1349,plain,(
% 2.10/0.68    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 2.10/0.68    inference(subsumption_resolution,[],[f1348,f216])).
% 2.10/0.68  fof(f216,plain,(
% 2.10/0.68    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 2.10/0.68    inference(resolution,[],[f211,f25])).
% 2.10/0.68  fof(f25,plain,(
% 2.10/0.68    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.10/0.68    inference(cnf_transformation,[],[f13])).
% 2.10/0.68  fof(f211,plain,(
% 2.10/0.68    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 2.10/0.68    inference(resolution,[],[f30,f29])).
% 2.10/0.68  fof(f30,plain,(
% 2.10/0.68    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f14])).
% 2.10/0.68  fof(f14,plain,(
% 2.10/0.68    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.10/0.68    inference(ennf_transformation,[],[f8])).
% 2.10/0.68  fof(f8,axiom,(
% 2.10/0.68    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 2.10/0.68  fof(f1348,plain,(
% 2.10/0.68    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 2.10/0.68    inference(resolution,[],[f829,f808])).
% 2.10/0.68  fof(f808,plain,(
% 2.10/0.68    ( ! [X35,X36] : (r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X36)),X35) | ~r1_tarski(X35,X36)) )),
% 2.10/0.68    inference(resolution,[],[f318,f244])).
% 2.10/0.68  fof(f244,plain,(
% 2.10/0.68    ( ! [X2] : (r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X2)),k4_xboole_0(sK1,X2))) )),
% 2.10/0.68    inference(resolution,[],[f218,f76])).
% 2.10/0.68  fof(f218,plain,(
% 2.10/0.68    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 2.10/0.68    inference(resolution,[],[f211,f35])).
% 2.10/0.68  fof(f318,plain,(
% 2.10/0.68    ( ! [X2,X0,X3,X1] : (~r1_tarski(X2,k4_xboole_0(X3,X1)) | ~r1_tarski(X0,X1) | r1_xboole_0(X2,X0)) )),
% 2.10/0.68    inference(resolution,[],[f42,f51])).
% 2.10/0.68  fof(f51,plain,(
% 2.10/0.68    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.10/0.68    inference(resolution,[],[f39,f43])).
% 2.10/0.68  fof(f39,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f18])).
% 2.10/0.68  fof(f42,plain,(
% 2.10/0.68    ( ! [X2,X0,X3,X1] : (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1) | r1_xboole_0(X0,X2)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f24])).
% 2.10/0.68  fof(f24,plain,(
% 2.10/0.68    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 2.10/0.68    inference(flattening,[],[f23])).
% 2.10/0.68  fof(f23,plain,(
% 2.10/0.68    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 2.10/0.68    inference(ennf_transformation,[],[f4])).
% 2.10/0.68  fof(f4,axiom,(
% 2.10/0.68    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_xboole_1)).
% 2.10/0.68  fof(f829,plain,(
% 2.10/0.68    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))),
% 2.10/0.68    inference(resolution,[],[f735,f40])).
% 2.10/0.68  fof(f40,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f20])).
% 2.10/0.68  fof(f20,plain,(
% 2.10/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 2.10/0.68    inference(flattening,[],[f19])).
% 2.10/0.68  fof(f19,plain,(
% 2.10/0.68    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 2.10/0.68    inference(ennf_transformation,[],[f5])).
% 2.10/0.68  fof(f5,axiom,(
% 2.10/0.68    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 2.10/0.68  fof(f735,plain,(
% 2.10/0.68    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.10/0.68    inference(backward_demodulation,[],[f215,f721])).
% 2.10/0.68  fof(f721,plain,(
% 2.10/0.68    ( ! [X168] : (k4_xboole_0(k1_tops_1(sK0,sK1),X168) = k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),X168)) )),
% 2.10/0.68    inference(resolution,[],[f214,f286])).
% 2.10/0.68  fof(f286,plain,(
% 2.10/0.68    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 2.10/0.68    inference(resolution,[],[f222,f43])).
% 2.10/0.68  fof(f222,plain,(
% 2.10/0.68    ( ! [X0] : (~r1_tarski(X0,k1_tops_1(sK0,sK1)) | r1_tarski(X0,u1_struct_0(sK0))) )),
% 2.10/0.68    inference(resolution,[],[f217,f64])).
% 2.10/0.68  fof(f217,plain,(
% 2.10/0.68    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.10/0.68    inference(resolution,[],[f211,f27])).
% 2.10/0.68  fof(f214,plain,(
% 2.10/0.68    ( ! [X4,X2,X3] : (~r1_tarski(X2,X4) | k4_xboole_0(X2,X3) = k7_subset_1(X4,X2,X3)) )),
% 2.10/0.68    inference(resolution,[],[f37,f35])).
% 2.10/0.68  fof(f37,plain,(
% 2.10/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 2.10/0.68    inference(cnf_transformation,[],[f17])).
% 2.10/0.68  fof(f17,plain,(
% 2.10/0.68    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.10/0.68    inference(ennf_transformation,[],[f6])).
% 2.10/0.68  fof(f6,axiom,(
% 2.10/0.68    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 2.10/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.10/0.68  fof(f215,plain,(
% 2.10/0.68    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.10/0.68    inference(backward_demodulation,[],[f26,f213])).
% 2.10/0.68  fof(f213,plain,(
% 2.10/0.68    ( ! [X1] : (k4_xboole_0(sK1,X1) = k7_subset_1(u1_struct_0(sK0),sK1,X1)) )),
% 2.10/0.68    inference(resolution,[],[f37,f27])).
% 2.10/0.68  fof(f26,plain,(
% 2.10/0.68    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 2.10/0.68    inference(cnf_transformation,[],[f13])).
% 2.10/0.68  % SZS output end Proof for theBenchmark
% 2.10/0.68  % (29298)------------------------------
% 2.10/0.68  % (29298)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.68  % (29298)Termination reason: Refutation
% 2.10/0.68  
% 2.10/0.68  % (29298)Memory used [KB]: 3070
% 2.10/0.68  % (29298)Time elapsed: 0.266 s
% 2.10/0.68  % (29298)------------------------------
% 2.10/0.68  % (29298)------------------------------
% 2.10/0.68  % (29278)Success in time 0.32 s
%------------------------------------------------------------------------------
