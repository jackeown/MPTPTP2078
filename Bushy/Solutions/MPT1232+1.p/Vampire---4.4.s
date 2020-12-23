%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t41_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:29 EDT 2019

% Result     : Theorem 8.87s
% Output     : Refutation 8.87s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 356 expanded)
%              Number of leaves         :   13 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  184 (1215 expanded)
%              Number of equality atoms :   33 ( 228 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f109124,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f23090,f13770,f23090,f180,f7327,f3915])).

fof(f3915,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,X1))
      | ~ r1_tarski(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_pre_topc(sK0,X0) = k2_pre_topc(sK0,X1) ) ),
    inference(resolution,[],[f137,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t41_tops_1.p',d10_xboole_0)).

fof(f137,plain,(
    ! [X4,X3] :
      ( r1_tarski(k2_pre_topc(sK0,X3),k2_pre_topc(sK0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X3,X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f83,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t41_tops_1.p',t49_pre_topc)).

fof(f83,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)))
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X1,X0)
                 => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t41_tops_1.p',t41_tops_1)).

fof(f7327,plain,(
    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,k2_pre_topc(sK0,sK2))),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f7325,f274])).

fof(f274,plain,(
    ! [X0] : k2_pre_topc(sK0,k3_xboole_0(X0,sK2)) = k2_pre_topc(sK0,k2_pre_topc(sK0,k3_xboole_0(X0,sK2))) ),
    inference(unit_resulting_resolution,[],[f83,f154,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k2_pre_topc(X0,X1) = k2_pre_topc(X0,k2_pre_topc(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t41_tops_1.p',projectivity_k2_pre_topc)).

fof(f154,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f146,f147])).

fof(f147,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f78,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t41_tops_1.p',dt_k9_subset_1)).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f146,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK2) = k3_xboole_0(X0,sK2) ),
    inference(unit_resulting_resolution,[],[f78,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t41_tops_1.p',redefinition_k9_subset_1)).

fof(f7325,plain,(
    r1_tarski(k2_pre_topc(sK0,k3_xboole_0(sK1,k2_pre_topc(sK0,sK2))),k2_pre_topc(sK0,k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)))) ),
    inference(unit_resulting_resolution,[],[f238,f275,f189,f137])).

fof(f189,plain,(
    r1_tarski(k3_xboole_0(sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f188,f118])).

fof(f118,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t41_tops_1.p',commutativity_k3_xboole_0)).

fof(f188,plain,(
    r1_tarski(k3_xboole_0(k2_pre_topc(sK0,sK2),sK1),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f187,f178])).

fof(f178,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),sK1,X0) = k3_xboole_0(X0,sK1) ),
    inference(forward_demodulation,[],[f169,f170])).

fof(f170,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k3_xboole_0(X0,sK1) ),
    inference(unit_resulting_resolution,[],[f81,f93])).

fof(f81,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f45])).

fof(f169,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,sK1) = k9_subset_1(u1_struct_0(sK0),sK1,X0) ),
    inference(unit_resulting_resolution,[],[f81,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t41_tops_1.p',commutativity_k9_subset_1)).

fof(f187,plain,(
    r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k3_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f166,f146])).

fof(f166,plain,(
    r1_tarski(k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2)),k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2))) ),
    inference(unit_resulting_resolution,[],[f82,f83,f79,f78,f81,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => r1_tarski(k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)),k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t41_tops_1.p',t40_tops_1)).

fof(f79,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f275,plain,(
    ! [X0] : m1_subset_1(k2_pre_topc(sK0,k3_xboole_0(X0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f83,f154,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t41_tops_1.p',dt_k2_pre_topc)).

fof(f238,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f231,f232])).

fof(f232,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f141,f94])).

fof(f141,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f83,f78,f89])).

fof(f231,plain,(
    ! [X0] : k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,sK2)) = k3_xboole_0(X0,k2_pre_topc(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f141,f93])).

fof(f180,plain,(
    k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) != k2_pre_topc(sK0,k3_xboole_0(sK1,k2_pre_topc(sK0,sK2))) ),
    inference(forward_demodulation,[],[f179,f118])).

fof(f179,plain,(
    k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) != k2_pre_topc(sK0,k3_xboole_0(k2_pre_topc(sK0,sK2),sK1)) ),
    inference(backward_demodulation,[],[f178,f153])).

fof(f153,plain,(
    k2_pre_topc(sK0,k3_xboole_0(sK1,sK2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))) ),
    inference(backward_demodulation,[],[f146,f80])).

fof(f80,plain,(
    k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f45])).

fof(f13770,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,sK2),k3_xboole_0(X0,k2_pre_topc(sK0,sK2))) ),
    inference(superposition,[],[f6074,f118])).

fof(f6074,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(X0,sK2),k3_xboole_0(k2_pre_topc(sK0,sK2),X0)) ),
    inference(superposition,[],[f198,f118])).

fof(f198,plain,(
    ! [X0] : r1_tarski(k3_xboole_0(sK2,X0),k3_xboole_0(k2_pre_topc(sK0,sK2),X0)) ),
    inference(unit_resulting_resolution,[],[f144,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t41_tops_1.p',t26_xboole_1)).

fof(f144,plain,(
    r1_tarski(sK2,k2_pre_topc(sK0,sK2)) ),
    inference(unit_resulting_resolution,[],[f83,f78,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t41_tops_1.p',t48_pre_topc)).

fof(f23090,plain,(
    ! [X4] : m1_subset_1(k3_xboole_0(sK1,X4),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f7962,f119])).

fof(f119,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/tops_1__t41_tops_1.p',idempotence_k3_xboole_0)).

fof(f7962,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(k3_xboole_0(X1,sK1),X0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f386,f118])).

fof(f386,plain,(
    ! [X0,X1] : m1_subset_1(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f376,f377])).

fof(f377,plain,(
    ! [X0,X1] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,k3_xboole_0(X1,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f177,f94])).

fof(f177,plain,(
    ! [X0] : m1_subset_1(k3_xboole_0(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f170,f171])).

fof(f171,plain,(
    ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f81,f94])).

fof(f376,plain,(
    ! [X0,X1] : k9_subset_1(u1_struct_0(sK0),X0,k3_xboole_0(X1,sK1)) = k3_xboole_0(X0,k3_xboole_0(X1,sK1)) ),
    inference(unit_resulting_resolution,[],[f177,f93])).
%------------------------------------------------------------------------------
