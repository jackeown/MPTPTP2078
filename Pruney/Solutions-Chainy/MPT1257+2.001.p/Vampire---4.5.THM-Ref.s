%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:28 EST 2020

% Result     : Theorem 2.81s
% Output     : Refutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 277 expanded)
%              Number of leaves         :   11 (  64 expanded)
%              Depth                    :   11
%              Number of atoms          :  126 ( 650 expanded)
%              Number of equality atoms :   24 (  55 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3663,plain,(
    $false ),
    inference(subsumption_resolution,[],[f3562,f2183])).

fof(f2183,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f1252,f2182])).

fof(f2182,plain,(
    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f44,f42,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f42,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f1252,plain,(
    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1069,f874])).

fof(f874,plain,(
    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f372,f872])).

fof(f872,plain,(
    k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(backward_demodulation,[],[f475,f871])).

fof(f871,plain,(
    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f855,f744])).

fof(f744,plain,(
    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f44,f42,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).

fof(f855,plain,(
    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    inference(unit_resulting_resolution,[],[f44,f76,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f76,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f42,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f475,plain,(
    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(forward_demodulation,[],[f338,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f338,plain,(
    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f98,f76,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f98,plain,(
    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f44,f42,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f372,plain,(
    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(unit_resulting_resolution,[],[f76,f98,f68])).

fof(f1069,plain,(
    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f98,f76,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).

fof(f3562,plain,(
    ~ r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f43,f98,f3529,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,k3_subset_1(X0,X2))
      | r1_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,X2)
          <=> r1_tarski(X1,k3_subset_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).

fof(f3529,plain,(
    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f3523,f873])).

fof(f873,plain,(
    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f435,f872])).

fof(f435,plain,(
    m1_subset_1(k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f128,f372])).

fof(f128,plain,(
    m1_subset_1(k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f98,f76,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f3523,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f49,f2182])).

fof(f43,plain,(
    ~ r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n020.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:31:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.50  % (13585)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (13591)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (13587)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (13608)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (13600)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (13605)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (13606)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.52  % (13598)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (13588)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (13590)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (13589)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (13593)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (13609)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (13586)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (13592)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.53  % (13607)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (13604)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (13610)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (13596)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (13599)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.54  % (13602)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.54  % (13603)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.54  % (13597)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.55  % (13595)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.55  % (13594)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.56  % (13601)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 2.24/0.69  % (13594)Refutation not found, incomplete strategy% (13594)------------------------------
% 2.24/0.69  % (13594)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.24/0.69  % (13594)Termination reason: Refutation not found, incomplete strategy
% 2.24/0.69  
% 2.24/0.69  % (13594)Memory used [KB]: 6140
% 2.24/0.69  % (13594)Time elapsed: 0.279 s
% 2.24/0.69  % (13594)------------------------------
% 2.24/0.69  % (13594)------------------------------
% 2.81/0.75  % (13592)Refutation found. Thanks to Tanya!
% 2.81/0.75  % SZS status Theorem for theBenchmark
% 2.81/0.75  % SZS output start Proof for theBenchmark
% 2.81/0.75  fof(f3663,plain,(
% 2.81/0.75    $false),
% 2.81/0.75    inference(subsumption_resolution,[],[f3562,f2183])).
% 2.81/0.75  fof(f2183,plain,(
% 2.81/0.75    r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 2.81/0.75    inference(backward_demodulation,[],[f1252,f2182])).
% 2.81/0.75  fof(f2182,plain,(
% 2.81/0.75    k1_tops_1(sK0,sK1) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 2.81/0.75    inference(unit_resulting_resolution,[],[f44,f42,f47])).
% 2.81/0.75  fof(f47,plain,(
% 2.81/0.75    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f24])).
% 2.81/0.75  fof(f24,plain,(
% 2.81/0.75    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.81/0.75    inference(ennf_transformation,[],[f15])).
% 2.81/0.75  fof(f15,axiom,(
% 2.81/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 2.81/0.75  fof(f42,plain,(
% 2.81/0.75    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.81/0.75    inference(cnf_transformation,[],[f21])).
% 2.81/0.75  fof(f21,plain,(
% 2.81/0.75    ? [X0] : (? [X1] : (~r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 2.81/0.75    inference(ennf_transformation,[],[f20])).
% 2.81/0.75  fof(f20,negated_conjecture,(
% 2.81/0.75    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 2.81/0.75    inference(negated_conjecture,[],[f19])).
% 2.81/0.75  fof(f19,conjecture,(
% 2.81/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_xboole_0(k1_tops_1(X0,X1),k2_tops_1(X0,X1))))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_tops_1)).
% 2.81/0.75  fof(f44,plain,(
% 2.81/0.75    l1_pre_topc(sK0)),
% 2.81/0.75    inference(cnf_transformation,[],[f21])).
% 2.81/0.75  fof(f1252,plain,(
% 2.81/0.75    r1_tarski(k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 2.81/0.75    inference(forward_demodulation,[],[f1069,f874])).
% 2.81/0.75  fof(f874,plain,(
% 2.81/0.75    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.81/0.75    inference(backward_demodulation,[],[f372,f872])).
% 2.81/0.75  fof(f872,plain,(
% 2.81/0.75    k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.81/0.75    inference(backward_demodulation,[],[f475,f871])).
% 2.81/0.75  fof(f871,plain,(
% 2.81/0.75    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.81/0.75    inference(forward_demodulation,[],[f855,f744])).
% 2.81/0.75  fof(f744,plain,(
% 2.81/0.75    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.81/0.75    inference(unit_resulting_resolution,[],[f44,f42,f45])).
% 2.81/0.75  fof(f45,plain,(
% 2.81/0.75    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f22])).
% 2.81/0.75  fof(f22,plain,(
% 2.81/0.75    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.81/0.75    inference(ennf_transformation,[],[f17])).
% 2.81/0.75  fof(f17,axiom,(
% 2.81/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k2_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_1)).
% 2.81/0.75  fof(f855,plain,(
% 2.81/0.75    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 2.81/0.75    inference(unit_resulting_resolution,[],[f44,f76,f46])).
% 2.81/0.75  fof(f46,plain,(
% 2.81/0.75    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f23])).
% 2.81/0.75  fof(f23,plain,(
% 2.81/0.75    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.81/0.75    inference(ennf_transformation,[],[f18])).
% 2.81/0.75  fof(f18,axiom,(
% 2.81/0.75    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 2.81/0.75  fof(f76,plain,(
% 2.81/0.75    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.81/0.75    inference(unit_resulting_resolution,[],[f42,f49])).
% 2.81/0.75  fof(f49,plain,(
% 2.81/0.75    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f25])).
% 2.81/0.75  fof(f25,plain,(
% 2.81/0.75    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.81/0.75    inference(ennf_transformation,[],[f3])).
% 2.81/0.75  fof(f3,axiom,(
% 2.81/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.81/0.75  fof(f475,plain,(
% 2.81/0.75    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.81/0.75    inference(forward_demodulation,[],[f338,f48])).
% 2.81/0.75  fof(f48,plain,(
% 2.81/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f1])).
% 2.81/0.75  fof(f1,axiom,(
% 2.81/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.81/0.75  fof(f338,plain,(
% 2.81/0.75    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1)) = k2_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),k2_tops_1(sK0,sK1))),
% 2.81/0.75    inference(unit_resulting_resolution,[],[f98,f76,f68])).
% 2.81/0.75  fof(f68,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f41])).
% 2.81/0.75  fof(f41,plain,(
% 2.81/0.75    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.81/0.75    inference(flattening,[],[f40])).
% 2.81/0.75  fof(f40,plain,(
% 2.81/0.75    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.81/0.75    inference(ennf_transformation,[],[f6])).
% 2.81/0.75  fof(f6,axiom,(
% 2.81/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.81/0.75  fof(f98,plain,(
% 2.81/0.75    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.81/0.75    inference(unit_resulting_resolution,[],[f44,f42,f61])).
% 2.81/0.75  fof(f61,plain,(
% 2.81/0.75    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f37])).
% 2.81/0.75  fof(f37,plain,(
% 2.81/0.75    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.81/0.75    inference(flattening,[],[f36])).
% 2.81/0.75  fof(f36,plain,(
% 2.81/0.75    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.81/0.75    inference(ennf_transformation,[],[f16])).
% 2.81/0.75  fof(f16,axiom,(
% 2.81/0.75    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 2.81/0.75  fof(f372,plain,(
% 2.81/0.75    k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)) = k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),
% 2.81/0.75    inference(unit_resulting_resolution,[],[f76,f98,f68])).
% 2.81/0.75  fof(f1069,plain,(
% 2.81/0.75    r1_tarski(k3_subset_1(u1_struct_0(sK0),k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1))),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 2.81/0.75    inference(unit_resulting_resolution,[],[f98,f76,f52])).
% 2.81/0.75  fof(f52,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f28])).
% 2.81/0.75  fof(f28,plain,(
% 2.81/0.75    ! [X0,X1] : (! [X2] : (r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.81/0.75    inference(ennf_transformation,[],[f11])).
% 2.81/0.75  fof(f11,axiom,(
% 2.81/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => r1_tarski(k3_subset_1(X0,k4_subset_1(X0,X1,X2)),k3_subset_1(X0,X1))))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_subset_1)).
% 2.81/0.75  fof(f3562,plain,(
% 2.81/0.75    ~r1_tarski(k1_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1)))),
% 2.81/0.75    inference(unit_resulting_resolution,[],[f43,f98,f3529,f55])).
% 2.81/0.75  fof(f55,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r1_tarski(X1,k3_subset_1(X0,X2)) | r1_xboole_0(X1,X2)) )),
% 2.81/0.75    inference(cnf_transformation,[],[f33])).
% 2.81/0.75  fof(f33,plain,(
% 2.81/0.75    ! [X0,X1] : (! [X2] : ((r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.81/0.75    inference(ennf_transformation,[],[f12])).
% 2.81/0.75  fof(f12,axiom,(
% 2.81/0.75    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (r1_xboole_0(X1,X2) <=> r1_tarski(X1,k3_subset_1(X0,X2)))))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_subset_1)).
% 2.81/0.75  fof(f3529,plain,(
% 2.81/0.75    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.81/0.75    inference(subsumption_resolution,[],[f3523,f873])).
% 2.81/0.75  fof(f873,plain,(
% 2.81/0.75    m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.81/0.75    inference(backward_demodulation,[],[f435,f872])).
% 2.81/0.75  fof(f435,plain,(
% 2.81/0.75    m1_subset_1(k2_xboole_0(k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.81/0.75    inference(backward_demodulation,[],[f128,f372])).
% 2.81/0.75  fof(f128,plain,(
% 2.81/0.75    m1_subset_1(k4_subset_1(u1_struct_0(sK0),k2_tops_1(sK0,sK1),k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.81/0.75    inference(unit_resulting_resolution,[],[f98,f76,f67])).
% 2.81/0.75  fof(f67,plain,(
% 2.81/0.75    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.81/0.75    inference(cnf_transformation,[],[f39])).
% 2.81/0.75  fof(f39,plain,(
% 2.81/0.75    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.81/0.75    inference(flattening,[],[f38])).
% 2.81/0.75  fof(f38,plain,(
% 2.81/0.75    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.81/0.75    inference(ennf_transformation,[],[f4])).
% 2.81/0.75  fof(f4,axiom,(
% 2.81/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.81/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 2.81/0.75  fof(f3523,plain,(
% 2.81/0.75    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.81/0.75    inference(superposition,[],[f49,f2182])).
% 2.81/0.75  fof(f43,plain,(
% 2.81/0.75    ~r1_xboole_0(k1_tops_1(sK0,sK1),k2_tops_1(sK0,sK1))),
% 2.81/0.75    inference(cnf_transformation,[],[f21])).
% 2.81/0.75  % SZS output end Proof for theBenchmark
% 2.81/0.75  % (13592)------------------------------
% 2.81/0.75  % (13592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.75  % (13592)Termination reason: Refutation
% 2.81/0.75  
% 2.81/0.75  % (13592)Memory used [KB]: 3454
% 2.81/0.75  % (13592)Time elapsed: 0.339 s
% 2.81/0.75  % (13592)------------------------------
% 2.81/0.75  % (13592)------------------------------
% 2.81/0.75  % (13584)Success in time 0.388 s
%------------------------------------------------------------------------------
