%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t99_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n030.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:25 EDT 2019

% Result     : Theorem 7.69s
% Output     : Refutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 575 expanded)
%              Number of leaves         :   17 ( 121 expanded)
%              Depth                    :   18
%              Number of atoms          :  227 (1808 expanded)
%              Number of equality atoms :   45 (  88 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8842,plain,(
    $false ),
    inference(resolution,[],[f4998,f195])).

fof(f195,plain,(
    ~ r2_hidden(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f84,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',d3_tarski)).

fof(f84,plain,(
    ~ r1_tarski(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',t99_tmap_1)).

fof(f4998,plain,(
    r2_hidden(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4997,f4770])).

fof(f4770,plain,(
    k2_xboole_0(k1_xboole_0,sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))) = sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f4769,f4639])).

fof(f4639,plain,(
    k2_xboole_0(k1_xboole_0,sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))) ),
    inference(unit_resulting_resolution,[],[f203,f679,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',redefinition_k4_subset_1)).

fof(f679,plain,(
    m1_subset_1(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f133,f194,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',t4_subset)).

fof(f194,plain,(
    r2_hidden(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f84,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f133,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f87,f102])).

fof(f102,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',dt_u1_pre_topc)).

fof(f87,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f203,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f132,f133,f103])).

fof(f132,plain,(
    r2_hidden(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f86,f87,f101])).

fof(f101,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',t5_pre_topc)).

fof(f86,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f4769,plain,(
    k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))) = sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4603,f4749])).

fof(f4749,plain,(
    k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k1_xboole_0) = sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4621,f123])).

fof(f123,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',t1_boole)).

fof(f4621,plain,(
    k2_xboole_0(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k1_xboole_0) = k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f203,f679,f114])).

fof(f4603,plain,(
    k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))) = k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f203,f679,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',commutativity_k4_subset_1)).

fof(f4997,plain,(
    r2_hidden(k2_xboole_0(k1_xboole_0,sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4996,f630])).

fof(f630,plain,(
    k3_xboole_0(k1_xboole_0,sK1) = k1_xboole_0 ),
    inference(superposition,[],[f298,f167])).

fof(f167,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
    inference(unit_resulting_resolution,[],[f83,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',redefinition_k9_subset_1)).

fof(f83,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f49])).

fof(f298,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X0) = k1_xboole_0 ),
    inference(forward_demodulation,[],[f283,f296])).

fof(f296,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k1_xboole_0) = k1_xboole_0 ),
    inference(forward_demodulation,[],[f284,f122])).

fof(f122,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',t2_boole)).

fof(f284,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k9_subset_1(u1_struct_0(sK0),X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f203,f118])).

fof(f283,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k1_xboole_0) = k9_subset_1(u1_struct_0(sK0),k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f203,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',commutativity_k9_subset_1)).

fof(f4996,plain,(
    r2_hidden(k2_xboole_0(k3_xboole_0(k1_xboole_0,sK1),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1))),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4995,f125])).

fof(f125,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',commutativity_k2_xboole_0)).

fof(f4995,plain,(
    r2_hidden(k2_xboole_0(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k3_xboole_0(k1_xboole_0,sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4994,f4619])).

fof(f4619,plain,(
    ! [X0] : k2_xboole_0(sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k3_xboole_0(k1_xboole_0,X0)) = k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k3_xboole_0(k1_xboole_0,X0)) ),
    inference(unit_resulting_resolution,[],[f2097,f679,f114])).

fof(f2097,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(k1_xboole_0,X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f2092,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',t3_subset)).

fof(f2092,plain,(
    ! [X5] : r1_tarski(k3_xboole_0(k1_xboole_0,X5),u1_struct_0(sK0)) ),
    inference(superposition,[],[f2071,f630])).

fof(f2071,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(k3_xboole_0(X1,sK1),X0),u1_struct_0(sK0)) ),
    inference(superposition,[],[f1854,f127])).

fof(f127,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',commutativity_k3_xboole_0)).

fof(f1854,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f422,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f422,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f407,f408])).

fof(f408,plain,(
    ! [X0,X1] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,k3_xboole_0(X1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f178,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',dt_k9_subset_1)).

fof(f178,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f167,f168])).

fof(f168,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f83,f119])).

fof(f407,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,sK1)) = k9_subset_1(u1_struct_0(sK0),X0,k3_xboole_0(X1,sK1)) ),
    inference(unit_resulting_resolution,[],[f178,f118])).

fof(f4994,plain,(
    r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k3_xboole_0(k1_xboole_0,sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4993,f167])).

fof(f4993,plain,(
    r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4501,f149])).

fof(f149,plain,(
    k5_tmap_1(sK0,sK1) = a_2_0_tmap_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f86,f87,f85,f83,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',d8_tmap_1)).

fof(f85,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f4501,plain,(
    r2_hidden(k4_subset_1(u1_struct_0(sK0),sK2(u1_pre_topc(sK0),k5_tmap_1(sK0,sK1)),k9_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1)),a_2_0_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f85,f86,f87,f132,f203,f83,f194,f679,f129])).

fof(f129,plain,(
    ! [X4,X2,X3,X1] :
      ( r2_hidden(k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)),a_2_0_tmap_1(X1,X2))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ r2_hidden(X4,u1_pre_topc(X1))
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) != X0
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ r2_hidden(X4,u1_pre_topc(X1))
      | r2_hidden(X0,a_2_0_tmap_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_pre_topc(X1)
        & v2_pre_topc(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_tmap_1(X1,X2))
      <=> ? [X3,X4] :
            ( r2_hidden(X4,u1_pre_topc(X1))
            & r2_hidden(X3,u1_pre_topc(X1))
            & k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)) = X0
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tmap_1__t99_tmap_1.p',fraenkel_a_2_0_tmap_1)).
%------------------------------------------------------------------------------
