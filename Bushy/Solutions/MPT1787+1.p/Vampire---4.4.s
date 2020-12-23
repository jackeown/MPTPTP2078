%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tmap_1__t102_tmap_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:02 EDT 2019

% Result     : Theorem 7.69s
% Output     : Refutation 7.69s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 245 expanded)
%              Number of leaves         :   16 (  50 expanded)
%              Depth                    :   13
%              Number of atoms          :  251 ( 893 expanded)
%              Number of equality atoms :   33 (  33 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f650,plain,(
    $false ),
    inference(resolution,[],[f599,f100])).

fof(f100,plain,(
    ~ r2_hidden(sK1,k5_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k5_tmap_1(X0,X1))
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(X1,k5_tmap_1(X0,X1))
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
           => r2_hidden(X1,k5_tmap_1(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r2_hidden(X1,k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t102_tmap_1)).

fof(f599,plain,(
    r2_hidden(sK1,k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f598,f556])).

fof(f556,plain,(
    k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = sK1 ),
    inference(forward_demodulation,[],[f508,f548])).

fof(f548,plain,(
    k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) = sK1 ),
    inference(forward_demodulation,[],[f512,f149])).

fof(f149,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t1_boole)).

fof(f512,plain,(
    k2_xboole_0(sK1,k1_xboole_0) = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f99,f423,f159])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',redefinition_k4_subset_1)).

fof(f423,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f180,f179,f105])).

fof(f105,plain,(
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
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t4_subset)).

fof(f179,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(unit_resulting_resolution,[],[f103,f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',dt_u1_pre_topc)).

fof(f103,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f180,plain,(
    r2_hidden(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f102,f103,f118])).

fof(f118,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f49])).

fof(f49,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t5_pre_topc)).

fof(f102,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f99,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f508,plain,(
    k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1) = k4_subset_1(u1_struct_0(sK0),sK1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f99,f423,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k4_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',commutativity_k4_subset_1)).

fof(f598,plain,(
    r2_hidden(k4_subset_1(u1_struct_0(sK0),k1_xboole_0,sK1),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f597,f251])).

fof(f251,plain,(
    k3_xboole_0(sK1,u1_struct_0(sK0)) = sK1 ),
    inference(unit_resulting_resolution,[],[f206,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t28_xboole_1)).

fof(f206,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f99,f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t3_subset)).

fof(f597,plain,(
    r2_hidden(k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_xboole_0(sK1,u1_struct_0(sK0))),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f596,f162])).

fof(f162,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',commutativity_k3_xboole_0)).

fof(f596,plain,(
    r2_hidden(k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k3_xboole_0(u1_struct_0(sK0),sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f595,f203])).

fof(f203,plain,(
    ! [X0] : k3_xboole_0(X0,sK1) = k9_subset_1(u1_struct_0(sK0),X0,sK1) ),
    inference(unit_resulting_resolution,[],[f99,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',redefinition_k9_subset_1)).

fof(f595,plain,(
    r2_hidden(k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f485,f201])).

fof(f201,plain,(
    k5_tmap_1(sK0,sK1) = a_2_0_tmap_1(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f102,f103,f101,f99,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_tmap_1(X0,X1) = a_2_0_tmap_1(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',d8_tmap_1)).

fof(f101,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f485,plain,(
    r2_hidden(k4_subset_1(u1_struct_0(sK0),k1_xboole_0,k9_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1)),a_2_0_tmap_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f101,f102,f103,f180,f181,f190,f99,f423,f166])).

fof(f166,plain,(
    ! [X4,X2,X3,X1] :
      ( ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X3,u1_pre_topc(X1))
      | ~ r2_hidden(X4,u1_pre_topc(X1))
      | r2_hidden(k4_subset_1(u1_struct_0(X1),X3,k9_subset_1(u1_struct_0(X1),X4,X2)),a_2_0_tmap_1(X1,X2)) ) ),
    inference(equality_resolution,[],[f142])).

fof(f142,plain,(
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
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
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
    inference(flattening,[],[f78])).

fof(f78,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',fraenkel_a_2_0_tmap_1)).

fof(f190,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f103,f183,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f41])).

fof(f41,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t1_tsep_1)).

fof(f183,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f103,f147])).

fof(f147,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f46])).

fof(f46,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',t2_tsep_1)).

fof(f181,plain,(
    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(unit_resulting_resolution,[],[f102,f103,f136])).

fof(f136,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
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
    inference(flattening,[],[f76])).

fof(f76,plain,(
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
    inference(ennf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(rectify,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/tmap_1__t102_tmap_1.p',d1_pre_topc)).
%------------------------------------------------------------------------------
