%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:15 EST 2020

% Result     : Theorem 3.25s
% Output     : Refutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 155 expanded)
%              Number of leaves         :   12 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :  161 ( 463 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3509,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3508,f1947])).

fof(f1947,plain,(
    r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f1689,f377])).

fof(f377,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,sK2)
      | r1_xboole_0(X0,k1_tops_1(sK0,sK2)) ) ),
    inference(superposition,[],[f177,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f177,plain,(
    ! [X0] : r1_xboole_0(k4_xboole_0(X0,sK2),k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f88,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f88,plain,(
    ! [X1] : r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(X1,sK2)) ),
    inference(resolution,[],[f57,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,k4_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_xboole_0(X0,k4_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).

fof(f57,plain,(
    r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(subsumption_resolution,[],[f52,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

fof(f52,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f30,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f1689,plain,(
    ! [X5] : r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X5)),X5) ),
    inference(resolution,[],[f265,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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

fof(f265,plain,(
    ! [X0] : r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0)) ),
    inference(resolution,[],[f169,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,u1_struct_0(sK0))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f50,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f50,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f34,f44])).

fof(f169,plain,(
    ! [X5] : r1_tarski(k4_xboole_0(sK1,X5),u1_struct_0(sK0)) ),
    inference(resolution,[],[f84,f42])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f84,plain,(
    ! [X3] :
      ( ~ r1_tarski(X3,sK1)
      | r1_tarski(X3,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f64,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f64,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f32,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f32,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f3508,plain,(
    ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f3502,f250])).

fof(f250,plain,(
    ! [X5] : r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X5)),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f115,f42])).

fof(f115,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f112,f84])).

fof(f112,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))
      | ~ r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f66,f40])).

fof(f66,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f61,f34])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f32,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f3502,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1))
    | ~ r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    inference(resolution,[],[f320,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f320,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(resolution,[],[f146,f171])).

fof(f171,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f84,f65])).

fof(f65,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f60,f34])).

fof(f60,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f32,f44])).

fof(f146,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(resolution,[],[f73,f40])).

fof(f73,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(superposition,[],[f68,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f68,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(backward_demodulation,[],[f31,f63])).

fof(f63,plain,(
    ! [X2] : k4_xboole_0(sK1,X2) = k7_subset_1(u1_struct_0(sK0),sK1,X2) ),
    inference(resolution,[],[f32,f45])).

fof(f31,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:00:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (15260)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.48  % (15253)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.49  % (15254)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.49  % (15268)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.50  % (15255)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (15267)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.50  % (15264)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.50  % (15266)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.50  % (15273)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (15263)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.50  % (15251)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (15259)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.50  % (15252)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (15256)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (15265)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (15271)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.51  % (15258)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (15261)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.51  % (15270)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (15257)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.51  % (15262)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.52  % (15269)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.52  % (15274)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.53  % (15272)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 3.25/0.79  % (15272)Refutation found. Thanks to Tanya!
% 3.25/0.79  % SZS status Theorem for theBenchmark
% 3.25/0.79  % SZS output start Proof for theBenchmark
% 3.25/0.79  fof(f3509,plain,(
% 3.25/0.79    $false),
% 3.25/0.79    inference(subsumption_resolution,[],[f3508,f1947])).
% 3.25/0.79  fof(f1947,plain,(
% 3.25/0.79    r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))),
% 3.25/0.79    inference(resolution,[],[f1689,f377])).
% 3.25/0.79  fof(f377,plain,(
% 3.25/0.79    ( ! [X0] : (~r1_xboole_0(X0,sK2) | r1_xboole_0(X0,k1_tops_1(sK0,sK2))) )),
% 3.25/0.79    inference(superposition,[],[f177,f47])).
% 3.25/0.79  fof(f47,plain,(
% 3.25/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.25/0.79    inference(cnf_transformation,[],[f7])).
% 3.25/0.79  fof(f7,axiom,(
% 3.25/0.79    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.25/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 3.25/0.79  fof(f177,plain,(
% 3.25/0.79    ( ! [X0] : (r1_xboole_0(k4_xboole_0(X0,sK2),k1_tops_1(sK0,sK2))) )),
% 3.25/0.79    inference(resolution,[],[f88,f49])).
% 3.25/0.79  fof(f49,plain,(
% 3.25/0.79    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 3.25/0.79    inference(cnf_transformation,[],[f29])).
% 3.25/0.79  fof(f29,plain,(
% 3.25/0.79    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.25/0.79    inference(ennf_transformation,[],[f1])).
% 3.25/0.79  fof(f1,axiom,(
% 3.25/0.79    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.25/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 3.25/0.79  fof(f88,plain,(
% 3.25/0.79    ( ! [X1] : (r1_xboole_0(k1_tops_1(sK0,sK2),k4_xboole_0(X1,sK2))) )),
% 3.25/0.79    inference(resolution,[],[f57,f39])).
% 3.25/0.79  fof(f39,plain,(
% 3.25/0.79    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_xboole_0(X0,k4_xboole_0(X2,X1))) )),
% 3.25/0.79    inference(cnf_transformation,[],[f23])).
% 3.25/0.79  fof(f23,plain,(
% 3.25/0.79    ! [X0,X1,X2] : (r1_xboole_0(X0,k4_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 3.25/0.79    inference(ennf_transformation,[],[f8])).
% 3.25/0.79  fof(f8,axiom,(
% 3.25/0.79    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_xboole_0(X0,k4_xboole_0(X2,X1)))),
% 3.25/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_xboole_1)).
% 3.25/0.79  fof(f57,plain,(
% 3.25/0.79    r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 3.25/0.79    inference(subsumption_resolution,[],[f52,f34])).
% 3.25/0.79  fof(f34,plain,(
% 3.25/0.79    l1_pre_topc(sK0)),
% 3.25/0.79    inference(cnf_transformation,[],[f17])).
% 3.25/0.79  fof(f17,plain,(
% 3.25/0.79    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.25/0.79    inference(flattening,[],[f16])).
% 3.25/0.79  fof(f16,plain,(
% 3.25/0.79    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.25/0.79    inference(ennf_transformation,[],[f15])).
% 3.25/0.79  fof(f15,negated_conjecture,(
% 3.25/0.79    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.25/0.79    inference(negated_conjecture,[],[f14])).
% 3.25/0.79  fof(f14,conjecture,(
% 3.25/0.79    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.25/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).
% 3.25/0.79  fof(f52,plain,(
% 3.25/0.79    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 3.25/0.79    inference(resolution,[],[f30,f44])).
% 3.25/0.79  fof(f44,plain,(
% 3.25/0.79    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 3.25/0.79    inference(cnf_transformation,[],[f26])).
% 3.25/0.79  fof(f26,plain,(
% 3.25/0.79    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.25/0.79    inference(ennf_transformation,[],[f12])).
% 3.25/0.79  fof(f12,axiom,(
% 3.25/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.25/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 3.25/0.79  fof(f30,plain,(
% 3.25/0.79    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.25/0.79    inference(cnf_transformation,[],[f17])).
% 3.25/0.79  fof(f1689,plain,(
% 3.25/0.79    ( ! [X5] : (r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,X5)),X5)) )),
% 3.25/0.79    inference(resolution,[],[f265,f38])).
% 3.25/0.79  fof(f38,plain,(
% 3.25/0.79    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 3.25/0.79    inference(cnf_transformation,[],[f22])).
% 3.25/0.79  fof(f22,plain,(
% 3.25/0.79    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.25/0.79    inference(ennf_transformation,[],[f2])).
% 3.25/0.79  fof(f2,axiom,(
% 3.25/0.79    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.25/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 3.25/0.79  fof(f265,plain,(
% 3.25/0.79    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X0)),k4_xboole_0(sK1,X0))) )),
% 3.25/0.79    inference(resolution,[],[f169,f102])).
% 3.25/0.79  fof(f102,plain,(
% 3.25/0.79    ( ! [X0] : (~r1_tarski(X0,u1_struct_0(sK0)) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 3.25/0.79    inference(resolution,[],[f50,f40])).
% 3.25/0.79  fof(f40,plain,(
% 3.25/0.79    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.25/0.79    inference(cnf_transformation,[],[f11])).
% 3.25/0.79  fof(f11,axiom,(
% 3.25/0.79    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.25/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.25/0.79  fof(f50,plain,(
% 3.25/0.79    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 3.25/0.79    inference(resolution,[],[f34,f44])).
% 3.25/0.79  fof(f169,plain,(
% 3.25/0.79    ( ! [X5] : (r1_tarski(k4_xboole_0(sK1,X5),u1_struct_0(sK0))) )),
% 3.25/0.79    inference(resolution,[],[f84,f42])).
% 3.25/0.79  fof(f42,plain,(
% 3.25/0.79    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.25/0.79    inference(cnf_transformation,[],[f5])).
% 3.25/0.79  fof(f5,axiom,(
% 3.25/0.79    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.25/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.25/0.79  fof(f84,plain,(
% 3.25/0.79    ( ! [X3] : (~r1_tarski(X3,sK1) | r1_tarski(X3,u1_struct_0(sK0))) )),
% 3.25/0.79    inference(resolution,[],[f64,f35])).
% 3.25/0.79  fof(f35,plain,(
% 3.25/0.79    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 3.25/0.79    inference(cnf_transformation,[],[f19])).
% 3.25/0.79  fof(f19,plain,(
% 3.25/0.79    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.25/0.79    inference(flattening,[],[f18])).
% 3.25/0.79  fof(f18,plain,(
% 3.25/0.79    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.25/0.79    inference(ennf_transformation,[],[f4])).
% 3.25/0.79  fof(f4,axiom,(
% 3.25/0.79    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.25/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.25/0.79  fof(f64,plain,(
% 3.25/0.79    r1_tarski(sK1,u1_struct_0(sK0))),
% 3.25/0.79    inference(resolution,[],[f32,f41])).
% 3.25/0.79  fof(f41,plain,(
% 3.25/0.79    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.25/0.79    inference(cnf_transformation,[],[f11])).
% 3.25/0.79  fof(f32,plain,(
% 3.25/0.79    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.25/0.79    inference(cnf_transformation,[],[f17])).
% 3.25/0.79  fof(f3508,plain,(
% 3.25/0.79    ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))),
% 3.25/0.79    inference(subsumption_resolution,[],[f3502,f250])).
% 3.25/0.79  fof(f250,plain,(
% 3.25/0.79    ( ! [X5] : (r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,X5)),k1_tops_1(sK0,sK1))) )),
% 3.25/0.79    inference(resolution,[],[f115,f42])).
% 3.25/0.79  fof(f115,plain,(
% 3.25/0.79    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))) )),
% 3.25/0.79    inference(subsumption_resolution,[],[f112,f84])).
% 3.25/0.79  fof(f112,plain,(
% 3.25/0.79    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,u1_struct_0(sK0))) )),
% 3.25/0.79    inference(resolution,[],[f66,f40])).
% 3.25/0.79  fof(f66,plain,(
% 3.25/0.79    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))) )),
% 3.25/0.79    inference(subsumption_resolution,[],[f61,f34])).
% 3.25/0.79  fof(f61,plain,(
% 3.25/0.79    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | r1_tarski(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK1))) )),
% 3.25/0.79    inference(resolution,[],[f32,f43])).
% 3.25/0.79  fof(f43,plain,(
% 3.25/0.79    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 3.25/0.79    inference(cnf_transformation,[],[f25])).
% 3.25/0.79  fof(f25,plain,(
% 3.25/0.79    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.25/0.79    inference(flattening,[],[f24])).
% 3.25/0.79  fof(f24,plain,(
% 3.25/0.79    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.25/0.79    inference(ennf_transformation,[],[f13])).
% 3.25/0.79  fof(f13,axiom,(
% 3.25/0.79    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.25/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 3.25/0.79  fof(f3502,plain,(
% 3.25/0.79    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK1)) | ~r1_xboole_0(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k1_tops_1(sK0,sK2))),
% 3.25/0.79    inference(resolution,[],[f320,f36])).
% 3.25/0.79  fof(f36,plain,(
% 3.25/0.79    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 3.25/0.79    inference(cnf_transformation,[],[f21])).
% 3.25/0.79  fof(f21,plain,(
% 3.25/0.79    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 3.25/0.79    inference(flattening,[],[f20])).
% 3.25/0.79  fof(f20,plain,(
% 3.25/0.79    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.25/0.79    inference(ennf_transformation,[],[f9])).
% 3.25/0.79  fof(f9,axiom,(
% 3.25/0.79    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.25/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 3.25/0.79  fof(f320,plain,(
% 3.25/0.79    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 3.25/0.79    inference(resolution,[],[f146,f171])).
% 3.25/0.79  fof(f171,plain,(
% 3.25/0.79    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 3.25/0.79    inference(resolution,[],[f84,f65])).
% 3.25/0.79  fof(f65,plain,(
% 3.25/0.79    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.25/0.79    inference(subsumption_resolution,[],[f60,f34])).
% 3.25/0.79  fof(f60,plain,(
% 3.25/0.79    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.25/0.79    inference(resolution,[],[f32,f44])).
% 3.25/0.79  fof(f146,plain,(
% 3.25/0.79    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 3.25/0.79    inference(resolution,[],[f73,f40])).
% 3.25/0.79  fof(f73,plain,(
% 3.25/0.79    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k4_xboole_0(k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 3.25/0.79    inference(superposition,[],[f68,f45])).
% 3.25/0.79  fof(f45,plain,(
% 3.25/0.79    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 3.25/0.79    inference(cnf_transformation,[],[f27])).
% 3.25/0.79  fof(f27,plain,(
% 3.25/0.79    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.25/0.79    inference(ennf_transformation,[],[f10])).
% 3.25/0.79  fof(f10,axiom,(
% 3.25/0.79    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.25/0.79    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.25/0.79  fof(f68,plain,(
% 3.25/0.79    ~r1_tarski(k1_tops_1(sK0,k4_xboole_0(sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 3.25/0.79    inference(backward_demodulation,[],[f31,f63])).
% 3.25/0.79  fof(f63,plain,(
% 3.25/0.79    ( ! [X2] : (k4_xboole_0(sK1,X2) = k7_subset_1(u1_struct_0(sK0),sK1,X2)) )),
% 3.25/0.79    inference(resolution,[],[f32,f45])).
% 3.25/0.79  fof(f31,plain,(
% 3.25/0.79    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 3.25/0.79    inference(cnf_transformation,[],[f17])).
% 3.25/0.79  % SZS output end Proof for theBenchmark
% 3.25/0.79  % (15272)------------------------------
% 3.25/0.79  % (15272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.25/0.79  % (15272)Termination reason: Refutation
% 3.25/0.79  
% 3.25/0.79  % (15272)Memory used [KB]: 3454
% 3.25/0.79  % (15272)Time elapsed: 0.373 s
% 3.25/0.79  % (15272)------------------------------
% 3.25/0.79  % (15272)------------------------------
% 3.25/0.79  % (15250)Success in time 0.435 s
%------------------------------------------------------------------------------
