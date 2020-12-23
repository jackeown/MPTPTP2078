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
% DateTime   : Thu Dec  3 13:09:15 EST 2020

% Result     : Theorem 9.31s
% Output     : Refutation 9.31s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 653 expanded)
%              Number of leaves         :   26 ( 183 expanded)
%              Depth                    :   16
%              Number of atoms          :  250 (1255 expanded)
%              Number of equality atoms :   46 ( 261 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19276,plain,(
    $false ),
    inference(subsumption_resolution,[],[f19256,f2378])).

fof(f2378,plain,(
    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f66,f1873,f63,f2240,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f2240,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f137,f173,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f173,plain,(
    m1_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f153,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f153,plain,(
    r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f128,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f128,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f65,f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f65,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

fof(f137,plain,(
    ! [X0,X1] : r2_hidden(k3_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f72,f117])).

fof(f117,plain,(
    ! [X2,X0] :
      ( r2_hidden(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X2,X0) ) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | r2_hidden(X2,X1)
      | k1_zfmisc_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_zfmisc_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> r1_tarski(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f34])).

fof(f1873,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X1,X2),X2) ),
    inference(forward_demodulation,[],[f1731,f1640])).

fof(f1640,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(unit_resulting_resolution,[],[f1390,f1617,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1617,plain,(
    ! [X0] : r1_tarski(X0,k2_subset_1(X0)) ),
    inference(superposition,[],[f71,f1459])).

fof(f1459,plain,(
    ! [X0] : k2_subset_1(X0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1280,f905])).

fof(f905,plain,(
    ! [X0] : k2_subset_1(X0) = k4_subset_1(X0,X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f890,f496])).

fof(f496,plain,(
    ! [X0] : k1_xboole_0 = k3_subset_1(X0,X0) ),
    inference(forward_demodulation,[],[f488,f410])).

fof(f410,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f385,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
        & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
        & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( ~ r1_tarski(X0,k3_zfmisc_1(X2,X0,X1))
          & ~ r1_tarski(X0,k3_zfmisc_1(X1,X2,X0))
          & ~ r1_tarski(X0,k3_zfmisc_1(X0,X1,X2)) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).

fof(f385,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(unit_resulting_resolution,[],[f71,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f488,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k3_subset_1(X0,X0) ),
    inference(unit_resulting_resolution,[],[f123,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f123,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(unit_resulting_resolution,[],[f114,f97])).

fof(f114,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f890,plain,(
    ! [X0] : k2_subset_1(X0) = k4_subset_1(X0,X0,k3_subset_1(X0,X0)) ),
    inference(unit_resulting_resolution,[],[f123,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

fof(f1280,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k4_subset_1(X0,X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f68,f123,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f68,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1390,plain,(
    ! [X0] : r1_tarski(k2_subset_1(X0),X0) ),
    inference(backward_demodulation,[],[f555,f1388])).

fof(f1388,plain,(
    ! [X0] : k2_subset_1(X0) = k2_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f1306,f902])).

fof(f902,plain,(
    ! [X0] : k2_subset_1(X0) = k4_subset_1(X0,k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f893,f522])).

fof(f522,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f507,f496])).

fof(f507,plain,(
    ! [X0] : k3_subset_1(X0,k3_subset_1(X0,X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f123,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f893,plain,(
    ! [X0] : k2_subset_1(X0) = k4_subset_1(X0,k1_xboole_0,k3_subset_1(X0,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f68,f86])).

fof(f1306,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = k4_subset_1(X0,k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f123,f68,f108])).

fof(f555,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0) ),
    inference(superposition,[],[f386,f523])).

fof(f523,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f491,f522])).

fof(f491,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f68,f84])).

fof(f386,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1) ),
    inference(unit_resulting_resolution,[],[f114,f102])).

fof(f1731,plain,(
    ! [X2,X1] : r1_tarski(k2_subset_1(k3_xboole_0(X1,X2)),X2) ),
    inference(backward_demodulation,[],[f1454,f1640])).

fof(f1454,plain,(
    ! [X2,X1] : r1_tarski(k2_subset_1(k3_xboole_0(X1,X2)),k2_subset_1(X2)) ),
    inference(forward_demodulation,[],[f1407,f1388])).

fof(f1407,plain,(
    ! [X2,X1] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)),k2_subset_1(X2)) ),
    inference(backward_demodulation,[],[f1266,f1388])).

fof(f1266,plain,(
    ! [X2,X1] : r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)),k2_xboole_0(k1_xboole_0,X2)) ),
    inference(superposition,[],[f99,f1235])).

fof(f1235,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f67,f1222,f92])).

fof(f1222,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1221,f253])).

fof(f253,plain,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f234,f237])).

fof(f237,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f67,f226,f92])).

fof(f226,plain,(
    ! [X0] : r1_tarski(k1_relat_1(k1_xboole_0),X0) ),
    inference(unit_resulting_resolution,[],[f159,f225,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f225,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f68,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f159,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f68,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f234,plain,(
    ! [X0] : k10_relat_1(k1_xboole_0,X0) = k1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f160,f226,f92])).

fof(f160,plain,(
    ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_relat_1(k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f159,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f1221,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,k10_relat_1(k1_xboole_0,X1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1211,f253])).

fof(f1211,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,k10_relat_1(k1_xboole_0,X1)),k10_relat_1(k1_xboole_0,k3_xboole_0(k9_relat_1(k1_xboole_0,X0),X1))) ),
    inference(unit_resulting_resolution,[],[f159,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1)))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_funct_1)).

fof(f67,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f99,plain,(
    ! [X2,X0,X1] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).

fof(f66,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f19256,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f1160,f2376,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f2376,plain,(
    ! [X0] : r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,X0)),k2_pre_topc(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f66,f72,f65,f2240,f69])).

fof(f1160,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(backward_demodulation,[],[f785,f1158])).

fof(f1158,plain,(
    ! [X0] : k3_xboole_0(X0,k2_pre_topc(sK0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f1108,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1108,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f66,f63,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f785,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(backward_demodulation,[],[f64,f784])).

fof(f784,plain,(
    ! [X0] : k3_xboole_0(X0,sK2) = k9_subset_1(u1_struct_0(sK0),X0,sK2) ),
    inference(unit_resulting_resolution,[],[f63,f101])).

fof(f64,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f34])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 14:05:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (20588)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.46  % (20572)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (20569)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (20565)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (20570)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (20587)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (20574)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (20583)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.51  % (20568)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (20573)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (20578)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (20589)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (20576)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (20575)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (20579)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  % (20585)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (20590)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (20580)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (20582)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.52  % (20571)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.53  % (20577)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (20566)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (20571)Refutation not found, incomplete strategy% (20571)------------------------------
% 0.21/0.53  % (20571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (20571)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (20571)Memory used [KB]: 10618
% 0.21/0.53  % (20571)Time elapsed: 0.085 s
% 0.21/0.53  % (20571)------------------------------
% 0.21/0.53  % (20571)------------------------------
% 0.21/0.53  % (20567)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (20584)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (20581)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.42/0.54  % (20586)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 2.49/0.68  % (20574)Refutation not found, incomplete strategy% (20574)------------------------------
% 2.49/0.68  % (20574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.49/0.68  % (20574)Termination reason: Refutation not found, incomplete strategy
% 2.49/0.68  
% 2.49/0.68  % (20574)Memory used [KB]: 6140
% 2.49/0.68  % (20574)Time elapsed: 0.254 s
% 2.49/0.68  % (20574)------------------------------
% 2.49/0.68  % (20574)------------------------------
% 3.88/0.91  % (20565)Time limit reached!
% 3.88/0.91  % (20565)------------------------------
% 3.88/0.91  % (20565)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.88/0.92  % (20565)Termination reason: Time limit
% 3.88/0.92  % (20565)Termination phase: Saturation
% 3.88/0.92  
% 3.88/0.92  % (20565)Memory used [KB]: 20340
% 3.88/0.92  % (20565)Time elapsed: 0.500 s
% 3.88/0.92  % (20565)------------------------------
% 3.88/0.92  % (20565)------------------------------
% 3.88/0.92  % (20578)Time limit reached!
% 3.88/0.92  % (20578)------------------------------
% 3.88/0.92  % (20578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/0.94  % (20578)Termination reason: Time limit
% 4.46/0.94  % (20578)Termination phase: Saturation
% 4.46/0.94  
% 4.46/0.94  % (20578)Memory used [KB]: 15735
% 4.46/0.94  % (20578)Time elapsed: 0.500 s
% 4.46/0.94  % (20578)------------------------------
% 4.46/0.94  % (20578)------------------------------
% 4.46/0.96  % (20579)Time limit reached!
% 4.46/0.96  % (20579)------------------------------
% 4.46/0.96  % (20579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.46/0.96  % (20579)Termination reason: Time limit
% 4.46/0.96  % (20579)Termination phase: Saturation
% 4.46/0.96  
% 4.46/0.96  % (20579)Memory used [KB]: 7803
% 4.46/0.96  % (20579)Time elapsed: 0.500 s
% 4.46/0.96  % (20579)------------------------------
% 4.46/0.96  % (20579)------------------------------
% 7.76/1.33  % (20573)Time limit reached!
% 7.76/1.33  % (20573)------------------------------
% 7.76/1.33  % (20573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.76/1.33  % (20573)Termination reason: Time limit
% 7.76/1.33  % (20573)Termination phase: Saturation
% 7.76/1.33  
% 7.76/1.33  % (20573)Memory used [KB]: 7291
% 7.76/1.33  % (20573)Time elapsed: 0.926 s
% 7.76/1.33  % (20573)------------------------------
% 7.76/1.33  % (20573)------------------------------
% 8.56/1.44  % (20566)Time limit reached!
% 8.56/1.44  % (20566)------------------------------
% 8.56/1.44  % (20566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.56/1.44  % (20566)Termination reason: Time limit
% 8.56/1.44  
% 8.56/1.44  % (20566)Memory used [KB]: 13816
% 8.56/1.44  % (20566)Time elapsed: 1.025 s
% 8.56/1.44  % (20566)------------------------------
% 8.56/1.44  % (20566)------------------------------
% 8.78/1.50  % (20569)Time limit reached!
% 8.78/1.50  % (20569)------------------------------
% 8.78/1.50  % (20569)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 8.78/1.50  % (20569)Termination reason: Time limit
% 8.78/1.50  % (20569)Termination phase: Saturation
% 8.78/1.50  
% 8.78/1.50  % (20569)Memory used [KB]: 14200
% 8.78/1.50  % (20569)Time elapsed: 1.100 s
% 8.78/1.50  % (20569)------------------------------
% 8.78/1.50  % (20569)------------------------------
% 9.31/1.54  % (20572)Refutation found. Thanks to Tanya!
% 9.31/1.54  % SZS status Theorem for theBenchmark
% 9.31/1.54  % SZS output start Proof for theBenchmark
% 9.31/1.54  fof(f19276,plain,(
% 9.31/1.54    $false),
% 9.31/1.54    inference(subsumption_resolution,[],[f19256,f2378])).
% 9.31/1.54  fof(f2378,plain,(
% 9.31/1.54    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2))),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f66,f1873,f63,f2240,f69])).
% 9.31/1.54  fof(f69,plain,(
% 9.31/1.54    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f36])).
% 9.31/1.54  fof(f36,plain,(
% 9.31/1.54    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 9.31/1.54    inference(flattening,[],[f35])).
% 9.31/1.54  fof(f35,plain,(
% 9.31/1.54    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 9.31/1.54    inference(ennf_transformation,[],[f31])).
% 9.31/1.54  fof(f31,axiom,(
% 9.31/1.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).
% 9.31/1.54  fof(f2240,plain,(
% 9.31/1.54    ( ! [X0] : (m1_subset_1(k3_xboole_0(sK1,X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f137,f173,f106])).
% 9.31/1.54  fof(f106,plain,(
% 9.31/1.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f56])).
% 9.31/1.54  fof(f56,plain,(
% 9.31/1.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 9.31/1.54    inference(flattening,[],[f55])).
% 9.31/1.54  fof(f55,plain,(
% 9.31/1.54    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 9.31/1.54    inference(ennf_transformation,[],[f20])).
% 9.31/1.54  fof(f20,axiom,(
% 9.31/1.54    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).
% 9.31/1.54  fof(f173,plain,(
% 9.31/1.54    m1_subset_1(k1_zfmisc_1(sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f153,f97])).
% 9.31/1.54  fof(f97,plain,(
% 9.31/1.54    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f19])).
% 9.31/1.54  fof(f19,axiom,(
% 9.31/1.54    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 9.31/1.54  fof(f153,plain,(
% 9.31/1.54    r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f128,f83])).
% 9.31/1.54  fof(f83,plain,(
% 9.31/1.54    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f43])).
% 9.31/1.54  fof(f43,plain,(
% 9.31/1.54    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 9.31/1.54    inference(ennf_transformation,[],[f10])).
% 9.31/1.54  fof(f10,axiom,(
% 9.31/1.54    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 9.31/1.54  fof(f128,plain,(
% 9.31/1.54    r1_tarski(sK1,u1_struct_0(sK0))),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f65,f98])).
% 9.31/1.54  fof(f98,plain,(
% 9.31/1.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f19])).
% 9.31/1.54  fof(f65,plain,(
% 9.31/1.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 9.31/1.54    inference(cnf_transformation,[],[f34])).
% 9.31/1.54  fof(f34,plain,(
% 9.31/1.54    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 9.31/1.54    inference(ennf_transformation,[],[f33])).
% 9.31/1.54  fof(f33,negated_conjecture,(
% 9.31/1.54    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 9.31/1.54    inference(negated_conjecture,[],[f32])).
% 9.31/1.54  fof(f32,conjecture,(
% 9.31/1.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).
% 9.31/1.54  fof(f137,plain,(
% 9.31/1.54    ( ! [X0,X1] : (r2_hidden(k3_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f72,f117])).
% 9.31/1.54  fof(f117,plain,(
% 9.31/1.54    ( ! [X2,X0] : (r2_hidden(X2,k1_zfmisc_1(X0)) | ~r1_tarski(X2,X0)) )),
% 9.31/1.54    inference(equality_resolution,[],[f93])).
% 9.31/1.54  fof(f93,plain,(
% 9.31/1.54    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | r2_hidden(X2,X1) | k1_zfmisc_1(X0) != X1) )),
% 9.31/1.54    inference(cnf_transformation,[],[f9])).
% 9.31/1.54  fof(f9,axiom,(
% 9.31/1.54    ! [X0,X1] : (k1_zfmisc_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> r1_tarski(X2,X0)))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).
% 9.31/1.54  fof(f72,plain,(
% 9.31/1.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f2])).
% 9.31/1.54  fof(f2,axiom,(
% 9.31/1.54    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 9.31/1.54  fof(f63,plain,(
% 9.31/1.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 9.31/1.54    inference(cnf_transformation,[],[f34])).
% 9.31/1.54  fof(f1873,plain,(
% 9.31/1.54    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X1,X2),X2)) )),
% 9.31/1.54    inference(forward_demodulation,[],[f1731,f1640])).
% 9.31/1.54  fof(f1640,plain,(
% 9.31/1.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f1390,f1617,f92])).
% 9.31/1.54  fof(f92,plain,(
% 9.31/1.54    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 9.31/1.54    inference(cnf_transformation,[],[f1])).
% 9.31/1.54  fof(f1,axiom,(
% 9.31/1.54    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 9.31/1.54  fof(f1617,plain,(
% 9.31/1.54    ( ! [X0] : (r1_tarski(X0,k2_subset_1(X0))) )),
% 9.31/1.54    inference(superposition,[],[f71,f1459])).
% 9.31/1.54  fof(f1459,plain,(
% 9.31/1.54    ( ! [X0] : (k2_subset_1(X0) = k2_xboole_0(X0,k1_xboole_0)) )),
% 9.31/1.54    inference(forward_demodulation,[],[f1280,f905])).
% 9.31/1.54  fof(f905,plain,(
% 9.31/1.54    ( ! [X0] : (k2_subset_1(X0) = k4_subset_1(X0,X0,k1_xboole_0)) )),
% 9.31/1.54    inference(forward_demodulation,[],[f890,f496])).
% 9.31/1.54  fof(f496,plain,(
% 9.31/1.54    ( ! [X0] : (k1_xboole_0 = k3_subset_1(X0,X0)) )),
% 9.31/1.54    inference(forward_demodulation,[],[f488,f410])).
% 9.31/1.54  fof(f410,plain,(
% 9.31/1.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f385,f111])).
% 9.31/1.54  fof(f111,plain,(
% 9.31/1.54    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) | k1_xboole_0 = X0) )),
% 9.31/1.54    inference(cnf_transformation,[],[f61])).
% 9.31/1.54  fof(f61,plain,(
% 9.31/1.54    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))))),
% 9.31/1.54    inference(ennf_transformation,[],[f29])).
% 9.31/1.54  fof(f29,axiom,(
% 9.31/1.54    ! [X0,X1,X2] : (~(~r1_tarski(X0,k3_zfmisc_1(X2,X0,X1)) & ~r1_tarski(X0,k3_zfmisc_1(X1,X2,X0)) & ~r1_tarski(X0,k3_zfmisc_1(X0,X1,X2))) => k1_xboole_0 = X0)),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).
% 9.31/1.54  fof(f385,plain,(
% 9.31/1.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f71,f102])).
% 9.31/1.54  fof(f102,plain,(
% 9.31/1.54    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 9.31/1.54    inference(cnf_transformation,[],[f52])).
% 9.31/1.54  fof(f52,plain,(
% 9.31/1.54    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 9.31/1.54    inference(ennf_transformation,[],[f7])).
% 9.31/1.54  fof(f7,axiom,(
% 9.31/1.54    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).
% 9.31/1.54  fof(f488,plain,(
% 9.31/1.54    ( ! [X0] : (k4_xboole_0(X0,X0) = k3_subset_1(X0,X0)) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f123,f84])).
% 9.31/1.54  fof(f84,plain,(
% 9.31/1.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f44])).
% 9.31/1.54  fof(f44,plain,(
% 9.31/1.54    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 9.31/1.54    inference(ennf_transformation,[],[f12])).
% 9.31/1.54  fof(f12,axiom,(
% 9.31/1.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 9.31/1.54  fof(f123,plain,(
% 9.31/1.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f114,f97])).
% 9.31/1.54  fof(f114,plain,(
% 9.31/1.54    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 9.31/1.54    inference(equality_resolution,[],[f91])).
% 9.31/1.54  fof(f91,plain,(
% 9.31/1.54    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 9.31/1.54    inference(cnf_transformation,[],[f1])).
% 9.31/1.54  fof(f890,plain,(
% 9.31/1.54    ( ! [X0] : (k2_subset_1(X0) = k4_subset_1(X0,X0,k3_subset_1(X0,X0))) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f123,f86])).
% 9.31/1.54  fof(f86,plain,(
% 9.31/1.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f46])).
% 9.31/1.54  fof(f46,plain,(
% 9.31/1.54    ! [X0,X1] : (k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 9.31/1.54    inference(ennf_transformation,[],[f16])).
% 9.31/1.54  fof(f16,axiom,(
% 9.31/1.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_subset_1(X0,X1,k3_subset_1(X0,X1)) = k2_subset_1(X0))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).
% 9.31/1.54  fof(f1280,plain,(
% 9.31/1.54    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k4_subset_1(X0,X0,k1_xboole_0)) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f68,f123,f108])).
% 9.31/1.54  fof(f108,plain,(
% 9.31/1.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f60])).
% 9.31/1.54  fof(f60,plain,(
% 9.31/1.54    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 9.31/1.54    inference(flattening,[],[f59])).
% 9.31/1.54  fof(f59,plain,(
% 9.31/1.54    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 9.31/1.54    inference(ennf_transformation,[],[f14])).
% 9.31/1.54  fof(f14,axiom,(
% 9.31/1.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 9.31/1.54  fof(f68,plain,(
% 9.31/1.54    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 9.31/1.54    inference(cnf_transformation,[],[f18])).
% 9.31/1.54  fof(f18,axiom,(
% 9.31/1.54    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 9.31/1.54  fof(f71,plain,(
% 9.31/1.54    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 9.31/1.54    inference(cnf_transformation,[],[f8])).
% 9.31/1.54  fof(f8,axiom,(
% 9.31/1.54    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 9.31/1.54  fof(f1390,plain,(
% 9.31/1.54    ( ! [X0] : (r1_tarski(k2_subset_1(X0),X0)) )),
% 9.31/1.54    inference(backward_demodulation,[],[f555,f1388])).
% 9.31/1.54  fof(f1388,plain,(
% 9.31/1.54    ( ! [X0] : (k2_subset_1(X0) = k2_xboole_0(k1_xboole_0,X0)) )),
% 9.31/1.54    inference(forward_demodulation,[],[f1306,f902])).
% 9.31/1.54  fof(f902,plain,(
% 9.31/1.54    ( ! [X0] : (k2_subset_1(X0) = k4_subset_1(X0,k1_xboole_0,X0)) )),
% 9.31/1.54    inference(forward_demodulation,[],[f893,f522])).
% 9.31/1.54  fof(f522,plain,(
% 9.31/1.54    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 9.31/1.54    inference(forward_demodulation,[],[f507,f496])).
% 9.31/1.54  fof(f507,plain,(
% 9.31/1.54    ( ! [X0] : (k3_subset_1(X0,k3_subset_1(X0,X0)) = X0) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f123,f85])).
% 9.31/1.54  fof(f85,plain,(
% 9.31/1.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 9.31/1.54    inference(cnf_transformation,[],[f45])).
% 9.31/1.54  fof(f45,plain,(
% 9.31/1.54    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 9.31/1.54    inference(ennf_transformation,[],[f13])).
% 9.31/1.54  fof(f13,axiom,(
% 9.31/1.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 9.31/1.54  fof(f893,plain,(
% 9.31/1.54    ( ! [X0] : (k2_subset_1(X0) = k4_subset_1(X0,k1_xboole_0,k3_subset_1(X0,k1_xboole_0))) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f68,f86])).
% 9.31/1.54  fof(f1306,plain,(
% 9.31/1.54    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = k4_subset_1(X0,k1_xboole_0,X0)) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f123,f68,f108])).
% 9.31/1.54  fof(f555,plain,(
% 9.31/1.54    ( ! [X0] : (r1_tarski(k2_xboole_0(k1_xboole_0,X0),X0)) )),
% 9.31/1.54    inference(superposition,[],[f386,f523])).
% 9.31/1.54  fof(f523,plain,(
% 9.31/1.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 9.31/1.54    inference(backward_demodulation,[],[f491,f522])).
% 9.31/1.54  fof(f491,plain,(
% 9.31/1.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_subset_1(X0,k1_xboole_0)) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f68,f84])).
% 9.31/1.54  fof(f386,plain,(
% 9.31/1.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(k2_xboole_0(X0,X1),X0),X1)) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f114,f102])).
% 9.31/1.54  fof(f1731,plain,(
% 9.31/1.54    ( ! [X2,X1] : (r1_tarski(k2_subset_1(k3_xboole_0(X1,X2)),X2)) )),
% 9.31/1.54    inference(backward_demodulation,[],[f1454,f1640])).
% 9.31/1.54  fof(f1454,plain,(
% 9.31/1.54    ( ! [X2,X1] : (r1_tarski(k2_subset_1(k3_xboole_0(X1,X2)),k2_subset_1(X2))) )),
% 9.31/1.54    inference(forward_demodulation,[],[f1407,f1388])).
% 9.31/1.54  fof(f1407,plain,(
% 9.31/1.54    ( ! [X2,X1] : (r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)),k2_subset_1(X2))) )),
% 9.31/1.54    inference(backward_demodulation,[],[f1266,f1388])).
% 9.31/1.54  fof(f1266,plain,(
% 9.31/1.54    ( ! [X2,X1] : (r1_tarski(k2_xboole_0(k1_xboole_0,k3_xboole_0(X1,X2)),k2_xboole_0(k1_xboole_0,X2))) )),
% 9.31/1.54    inference(superposition,[],[f99,f1235])).
% 9.31/1.54  fof(f1235,plain,(
% 9.31/1.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f67,f1222,f92])).
% 9.31/1.54  fof(f1222,plain,(
% 9.31/1.54    ( ! [X0] : (r1_tarski(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0)) )),
% 9.31/1.54    inference(forward_demodulation,[],[f1221,f253])).
% 9.31/1.54  fof(f253,plain,(
% 9.31/1.54    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) )),
% 9.31/1.54    inference(forward_demodulation,[],[f234,f237])).
% 9.31/1.54  fof(f237,plain,(
% 9.31/1.54    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f67,f226,f92])).
% 9.31/1.54  fof(f226,plain,(
% 9.31/1.54    ( ! [X0] : (r1_tarski(k1_relat_1(k1_xboole_0),X0)) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f159,f225,f80])).
% 9.31/1.54  fof(f80,plain,(
% 9.31/1.54    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f41])).
% 9.31/1.54  fof(f41,plain,(
% 9.31/1.54    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 9.31/1.54    inference(ennf_transformation,[],[f22])).
% 9.31/1.54  fof(f22,axiom,(
% 9.31/1.54    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 9.31/1.54  fof(f225,plain,(
% 9.31/1.54    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f68,f104])).
% 9.31/1.54  fof(f104,plain,(
% 9.31/1.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f54])).
% 9.31/1.54  fof(f54,plain,(
% 9.31/1.54    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 9.31/1.54    inference(ennf_transformation,[],[f28])).
% 9.31/1.54  fof(f28,axiom,(
% 9.31/1.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 9.31/1.54  fof(f159,plain,(
% 9.31/1.54    v1_relat_1(k1_xboole_0)),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f68,f103])).
% 9.31/1.54  fof(f103,plain,(
% 9.31/1.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f53])).
% 9.31/1.54  fof(f53,plain,(
% 9.31/1.54    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 9.31/1.54    inference(ennf_transformation,[],[f27])).
% 9.31/1.54  fof(f27,axiom,(
% 9.31/1.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 9.31/1.54  fof(f234,plain,(
% 9.31/1.54    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k1_relat_1(k1_xboole_0)) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f160,f226,f92])).
% 9.31/1.54  fof(f160,plain,(
% 9.31/1.54    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_relat_1(k1_xboole_0))) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f159,f78])).
% 9.31/1.54  fof(f78,plain,(
% 9.31/1.54    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f40])).
% 9.31/1.54  fof(f40,plain,(
% 9.31/1.54    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 9.31/1.54    inference(ennf_transformation,[],[f25])).
% 9.31/1.54  fof(f25,axiom,(
% 9.31/1.54    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 9.31/1.54  fof(f1221,plain,(
% 9.31/1.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(k1_xboole_0,X1)),k1_xboole_0)) )),
% 9.31/1.54    inference(forward_demodulation,[],[f1211,f253])).
% 9.31/1.54  fof(f1211,plain,(
% 9.31/1.54    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(k1_xboole_0,X1)),k10_relat_1(k1_xboole_0,k3_xboole_0(k9_relat_1(k1_xboole_0,X0),X1)))) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f159,f100])).
% 9.31/1.54  fof(f100,plain,(
% 9.31/1.54    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) | ~v1_relat_1(X2)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f50])).
% 9.31/1.54  fof(f50,plain,(
% 9.31/1.54    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))) | ~v1_relat_1(X2))),
% 9.31/1.54    inference(ennf_transformation,[],[f26])).
% 9.31/1.54  fof(f26,axiom,(
% 9.31/1.54    ! [X0,X1,X2] : (v1_relat_1(X2) => r1_tarski(k3_xboole_0(X0,k10_relat_1(X2,X1)),k10_relat_1(X2,k3_xboole_0(k9_relat_1(X2,X0),X1))))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_funct_1)).
% 9.31/1.54  fof(f67,plain,(
% 9.31/1.54    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f4])).
% 9.31/1.54  fof(f4,axiom,(
% 9.31/1.54    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 9.31/1.54  fof(f99,plain,(
% 9.31/1.54    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))) )),
% 9.31/1.54    inference(cnf_transformation,[],[f5])).
% 9.31/1.54  fof(f5,axiom,(
% 9.31/1.54    ! [X0,X1,X2] : r1_tarski(k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)),k2_xboole_0(X1,X2))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_xboole_1)).
% 9.31/1.54  fof(f66,plain,(
% 9.31/1.54    l1_pre_topc(sK0)),
% 9.31/1.54    inference(cnf_transformation,[],[f34])).
% 9.31/1.54  fof(f19256,plain,(
% 9.31/1.54    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k2_pre_topc(sK0,sK2))),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f1160,f2376,f107])).
% 9.31/1.54  fof(f107,plain,(
% 9.31/1.54    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f58])).
% 9.31/1.54  fof(f58,plain,(
% 9.31/1.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 9.31/1.54    inference(flattening,[],[f57])).
% 9.31/1.54  fof(f57,plain,(
% 9.31/1.54    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 9.31/1.54    inference(ennf_transformation,[],[f3])).
% 9.31/1.54  fof(f3,axiom,(
% 9.31/1.54    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 9.31/1.54  fof(f2376,plain,(
% 9.31/1.54    ( ! [X0] : (r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,X0)),k2_pre_topc(sK0,sK1))) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f66,f72,f65,f2240,f69])).
% 9.31/1.54  fof(f1160,plain,(
% 9.31/1.54    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k3_xboole_0(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 9.31/1.54    inference(backward_demodulation,[],[f785,f1158])).
% 9.31/1.54  fof(f1158,plain,(
% 9.31/1.54    ( ! [X0] : (k3_xboole_0(X0,k2_pre_topc(sK0,sK2)) = k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2))) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f1108,f101])).
% 9.31/1.54  fof(f101,plain,(
% 9.31/1.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f51])).
% 9.31/1.54  fof(f51,plain,(
% 9.31/1.54    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 9.31/1.54    inference(ennf_transformation,[],[f15])).
% 9.31/1.54  fof(f15,axiom,(
% 9.31/1.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 9.31/1.54  fof(f1108,plain,(
% 9.31/1.54    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f66,f63,f89])).
% 9.31/1.54  fof(f89,plain,(
% 9.31/1.54    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 9.31/1.54    inference(cnf_transformation,[],[f49])).
% 9.31/1.54  fof(f49,plain,(
% 9.31/1.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 9.31/1.54    inference(flattening,[],[f48])).
% 9.31/1.54  fof(f48,plain,(
% 9.31/1.54    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 9.31/1.54    inference(ennf_transformation,[],[f30])).
% 9.31/1.54  fof(f30,axiom,(
% 9.31/1.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 9.31/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 9.31/1.54  fof(f785,plain,(
% 9.31/1.54    ~r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 9.31/1.54    inference(backward_demodulation,[],[f64,f784])).
% 9.31/1.54  fof(f784,plain,(
% 9.31/1.54    ( ! [X0] : (k3_xboole_0(X0,sK2) = k9_subset_1(u1_struct_0(sK0),X0,sK2)) )),
% 9.31/1.54    inference(unit_resulting_resolution,[],[f63,f101])).
% 9.31/1.54  fof(f64,plain,(
% 9.31/1.54    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 9.31/1.54    inference(cnf_transformation,[],[f34])).
% 9.31/1.54  % SZS output end Proof for theBenchmark
% 9.31/1.54  % (20572)------------------------------
% 9.31/1.54  % (20572)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.31/1.54  % (20572)Termination reason: Refutation
% 9.31/1.54  
% 9.31/1.54  % (20572)Memory used [KB]: 17654
% 9.31/1.54  % (20572)Time elapsed: 1.083 s
% 9.31/1.54  % (20572)------------------------------
% 9.31/1.54  % (20572)------------------------------
% 9.31/1.56  % (20564)Success in time 1.192 s
%------------------------------------------------------------------------------
