%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:20 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 319 expanded)
%              Number of leaves         :   11 (  72 expanded)
%              Depth                    :   16
%              Number of atoms          :  194 (1058 expanded)
%              Number of equality atoms :   60 ( 236 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f936,plain,(
    $false ),
    inference(subsumption_resolution,[],[f935,f66])).

fof(f66,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) ),
    inference(backward_demodulation,[],[f59,f65])).

fof(f65,plain,(
    ! [X3] : k9_subset_1(k2_struct_0(sK0),X3,sK1) = k9_subset_1(sK1,X3,sK1) ),
    inference(forward_demodulation,[],[f63,f61])).

fof(f61,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f45,f55])).

fof(f55,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f30,f29])).

fof(f29,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f30,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2)) ) ),
    inference(definition_unfolding,[],[f38,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f63,plain,(
    ! [X3] : k9_subset_1(k2_struct_0(sK0),X3,sK1) = k4_xboole_0(X3,k4_xboole_0(X3,sK1)) ),
    inference(resolution,[],[f45,f60])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f25,f57])).

fof(f57,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f31,f56])).

fof(f56,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f32,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1))
              & v3_pre_topc(X2,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & v1_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v1_tops_1(X1,X0)
             => ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( v3_pre_topc(X2,X0)
                   => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( v3_pre_topc(X2,X0)
                 => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).

fof(f32,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f31,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) ),
    inference(backward_demodulation,[],[f24,f57])).

fof(f24,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f935,plain,(
    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) ),
    inference(forward_demodulation,[],[f934,f65])).

fof(f934,plain,(
    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) ),
    inference(forward_demodulation,[],[f933,f342])).

fof(f342,plain,(
    sK2 = k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)) ),
    inference(superposition,[],[f330,f61])).

fof(f330,plain,(
    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f321])).

fof(f321,plain,
    ( sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_struct_0(sK0)))
    | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_struct_0(sK0))) ),
    inference(resolution,[],[f184,f145])).

fof(f145,plain,(
    ! [X2] :
      ( r2_hidden(sK3(sK2,X2,sK2),k2_struct_0(sK0))
      | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,X2)) ) ),
    inference(resolution,[],[f135,f58])).

fof(f58,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f22,f57])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f135,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(X5))
      | k4_xboole_0(X3,k4_xboole_0(X3,X4)) = X3
      | r2_hidden(sK3(X3,X4,X3),X5) ) ),
    inference(resolution,[],[f127,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

fof(f127,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1,X0),X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(factoring,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f40,f36])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f184,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(sK3(X12,X13,X12),X13)
      | k4_xboole_0(X12,k4_xboole_0(X12,X13)) = X12 ) ),
    inference(subsumption_resolution,[],[f179,f50])).

fof(f179,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(sK3(X12,X13,X12),X13)
      | ~ r2_hidden(sK3(X12,X13,X12),X12)
      | k4_xboole_0(X12,k4_xboole_0(X12,X13)) = X12 ) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
    ! [X12,X13] :
      ( ~ r2_hidden(sK3(X12,X13,X12),X13)
      | ~ r2_hidden(sK3(X12,X13,X12),X12)
      | k4_xboole_0(X12,k4_xboole_0(X12,X13)) = X12
      | k4_xboole_0(X12,k4_xboole_0(X12,X13)) = X12 ) ),
    inference(resolution,[],[f51,f127])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 ) ),
    inference(definition_unfolding,[],[f39,f36])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X0)
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(sK3(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f933,plain,(
    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f929,f78])).

fof(f78,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f77,f60])).

fof(f77,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f76,f26])).

fof(f26,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f75,f57])).

fof(f75,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ v1_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f34,f28])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).

fof(f929,plain,(
    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f926,f60])).

fof(f926,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f925,f58])).

fof(f925,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)) ) ),
    inference(resolution,[],[f292,f23])).

fof(f23,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f292,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) ) ),
    inference(forward_demodulation,[],[f291,f57])).

fof(f291,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(forward_demodulation,[],[f290,f57])).

fof(f290,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(forward_demodulation,[],[f289,f57])).

fof(f289,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(subsumption_resolution,[],[f288,f28])).

fof(f288,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(resolution,[],[f35,f27])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:31:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (19204)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.49  % (19220)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.49  % (19202)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (19210)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.51  % (19215)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.51  % (19208)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.24/0.51  % (19218)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.24/0.51  % (19202)Refutation not found, incomplete strategy% (19202)------------------------------
% 1.24/0.51  % (19202)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.52  % (19212)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.24/0.52  % (19228)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.24/0.52  % (19227)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.24/0.52  % (19217)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.52  % (19231)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.36/0.52  % (19216)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.36/0.52  % (19213)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.36/0.52  % (19225)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.36/0.53  % (19211)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.36/0.53  % (19229)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.36/0.53  % (19224)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.36/0.53  % (19223)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.36/0.53  % (19207)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.36/0.53  % (19205)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.36/0.53  % (19230)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.36/0.53  % (19209)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.36/0.53  % (19203)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.36/0.53  % (19202)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.53  
% 1.36/0.53  % (19202)Memory used [KB]: 1918
% 1.36/0.53  % (19202)Time elapsed: 0.121 s
% 1.36/0.53  % (19202)------------------------------
% 1.36/0.53  % (19202)------------------------------
% 1.36/0.54  % (19212)Refutation not found, incomplete strategy% (19212)------------------------------
% 1.36/0.54  % (19212)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (19212)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (19212)Memory used [KB]: 10746
% 1.36/0.54  % (19212)Time elapsed: 0.142 s
% 1.36/0.54  % (19212)------------------------------
% 1.36/0.54  % (19212)------------------------------
% 1.36/0.54  % (19224)Refutation not found, incomplete strategy% (19224)------------------------------
% 1.36/0.54  % (19224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (19224)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (19224)Memory used [KB]: 10746
% 1.36/0.54  % (19224)Time elapsed: 0.138 s
% 1.36/0.54  % (19224)------------------------------
% 1.36/0.54  % (19224)------------------------------
% 1.36/0.54  % (19211)Refutation not found, incomplete strategy% (19211)------------------------------
% 1.36/0.54  % (19211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (19211)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (19211)Memory used [KB]: 10874
% 1.36/0.54  % (19211)Time elapsed: 0.141 s
% 1.36/0.54  % (19211)------------------------------
% 1.36/0.54  % (19211)------------------------------
% 1.36/0.54  % (19219)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.36/0.54  % (19219)Refutation not found, incomplete strategy% (19219)------------------------------
% 1.36/0.54  % (19219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (19219)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (19219)Memory used [KB]: 10618
% 1.36/0.54  % (19219)Time elapsed: 0.148 s
% 1.36/0.54  % (19219)------------------------------
% 1.36/0.54  % (19219)------------------------------
% 1.36/0.54  % (19206)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.36/0.54  % (19213)Refutation not found, incomplete strategy% (19213)------------------------------
% 1.36/0.54  % (19213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (19213)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (19213)Memory used [KB]: 10746
% 1.36/0.54  % (19213)Time elapsed: 0.151 s
% 1.36/0.54  % (19213)------------------------------
% 1.36/0.54  % (19213)------------------------------
% 1.36/0.54  % (19221)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.36/0.55  % (19223)Refutation not found, incomplete strategy% (19223)------------------------------
% 1.36/0.55  % (19223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.55  % (19223)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.55  
% 1.36/0.55  % (19223)Memory used [KB]: 1791
% 1.36/0.55  % (19223)Time elapsed: 0.155 s
% 1.36/0.55  % (19223)------------------------------
% 1.36/0.55  % (19223)------------------------------
% 1.36/0.55  % (19226)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.36/0.55  % (19222)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.36/0.56  % (19222)Refutation not found, incomplete strategy% (19222)------------------------------
% 1.36/0.56  % (19222)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.57  % (19214)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.36/0.58  % (19222)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.58  
% 1.36/0.58  % (19222)Memory used [KB]: 10874
% 1.36/0.58  % (19222)Time elapsed: 0.152 s
% 1.36/0.58  % (19222)------------------------------
% 1.36/0.58  % (19222)------------------------------
% 1.36/0.60  % (19208)Refutation found. Thanks to Tanya!
% 1.36/0.60  % SZS status Theorem for theBenchmark
% 1.36/0.60  % SZS output start Proof for theBenchmark
% 1.36/0.60  fof(f936,plain,(
% 1.36/0.60    $false),
% 1.36/0.60    inference(subsumption_resolution,[],[f935,f66])).
% 1.36/0.60  fof(f66,plain,(
% 1.36/0.60    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1))),
% 1.36/0.60    inference(backward_demodulation,[],[f59,f65])).
% 1.36/0.60  fof(f65,plain,(
% 1.36/0.60    ( ! [X3] : (k9_subset_1(k2_struct_0(sK0),X3,sK1) = k9_subset_1(sK1,X3,sK1)) )),
% 1.36/0.60    inference(forward_demodulation,[],[f63,f61])).
% 1.36/0.60  fof(f61,plain,(
% 1.36/0.60    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.36/0.60    inference(resolution,[],[f45,f55])).
% 1.36/0.60  fof(f55,plain,(
% 1.36/0.60    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.36/0.60    inference(forward_demodulation,[],[f30,f29])).
% 1.36/0.60  fof(f29,plain,(
% 1.36/0.60    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.36/0.60    inference(cnf_transformation,[],[f3])).
% 1.36/0.60  fof(f3,axiom,(
% 1.36/0.60    ! [X0] : k2_subset_1(X0) = X0),
% 1.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 1.36/0.60  fof(f30,plain,(
% 1.36/0.60    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.36/0.60    inference(cnf_transformation,[],[f4])).
% 1.36/0.60  fof(f4,axiom,(
% 1.36/0.60    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.36/0.60  fof(f45,plain,(
% 1.36/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k4_xboole_0(X1,k4_xboole_0(X1,X2))) )),
% 1.36/0.60    inference(definition_unfolding,[],[f38,f36])).
% 1.36/0.60  fof(f36,plain,(
% 1.36/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.36/0.60    inference(cnf_transformation,[],[f2])).
% 1.36/0.60  fof(f2,axiom,(
% 1.36/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.36/0.60  fof(f38,plain,(
% 1.36/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.36/0.60    inference(cnf_transformation,[],[f21])).
% 1.36/0.60  fof(f21,plain,(
% 1.36/0.60    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.36/0.60    inference(ennf_transformation,[],[f6])).
% 1.36/0.60  fof(f6,axiom,(
% 1.36/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.36/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.36/0.60  fof(f63,plain,(
% 1.36/0.60    ( ! [X3] : (k9_subset_1(k2_struct_0(sK0),X3,sK1) = k4_xboole_0(X3,k4_xboole_0(X3,sK1))) )),
% 1.36/0.60    inference(resolution,[],[f45,f60])).
% 1.36/0.60  fof(f60,plain,(
% 1.36/0.60    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.36/0.60    inference(backward_demodulation,[],[f25,f57])).
% 1.36/0.60  fof(f57,plain,(
% 1.36/0.60    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.36/0.60    inference(resolution,[],[f31,f56])).
% 1.98/0.62  fof(f56,plain,(
% 1.98/0.62    l1_struct_0(sK0)),
% 1.98/0.62    inference(resolution,[],[f32,f28])).
% 1.98/0.62  fof(f28,plain,(
% 1.98/0.62    l1_pre_topc(sK0)),
% 1.98/0.62    inference(cnf_transformation,[],[f14])).
% 1.98/0.62  fof(f14,plain,(
% 1.98/0.62    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.98/0.62    inference(flattening,[],[f13])).
% 1.98/0.62  fof(f13,plain,(
% 1.98/0.62    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.98/0.62    inference(ennf_transformation,[],[f12])).
% 1.98/0.62  fof(f12,negated_conjecture,(
% 1.98/0.62    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 1.98/0.62    inference(negated_conjecture,[],[f11])).
% 1.98/0.62  fof(f11,conjecture,(
% 1.98/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tops_1)).
% 1.98/0.62  fof(f32,plain,(
% 1.98/0.62    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f16])).
% 1.98/0.62  fof(f16,plain,(
% 1.98/0.62    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.98/0.62    inference(ennf_transformation,[],[f8])).
% 1.98/0.62  fof(f8,axiom,(
% 1.98/0.62    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.98/0.62  fof(f31,plain,(
% 1.98/0.62    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f15])).
% 1.98/0.62  fof(f15,plain,(
% 1.98/0.62    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.98/0.62    inference(ennf_transformation,[],[f7])).
% 1.98/0.62  fof(f7,axiom,(
% 1.98/0.62    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.98/0.62  fof(f25,plain,(
% 1.98/0.62    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.98/0.62    inference(cnf_transformation,[],[f14])).
% 1.98/0.62  fof(f59,plain,(
% 1.98/0.62    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))),
% 1.98/0.62    inference(backward_demodulation,[],[f24,f57])).
% 1.98/0.62  fof(f24,plain,(
% 1.98/0.62    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 1.98/0.62    inference(cnf_transformation,[],[f14])).
% 1.98/0.62  fof(f935,plain,(
% 1.98/0.62    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1))),
% 1.98/0.62    inference(forward_demodulation,[],[f934,f65])).
% 1.98/0.62  fof(f934,plain,(
% 1.98/0.62    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))),
% 1.98/0.62    inference(forward_demodulation,[],[f933,f342])).
% 1.98/0.62  fof(f342,plain,(
% 1.98/0.62    sK2 = k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))),
% 1.98/0.62    inference(superposition,[],[f330,f61])).
% 1.98/0.62  fof(f330,plain,(
% 1.98/0.62    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_struct_0(sK0)))),
% 1.98/0.62    inference(duplicate_literal_removal,[],[f321])).
% 1.98/0.62  fof(f321,plain,(
% 1.98/0.62    sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_struct_0(sK0))) | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,k2_struct_0(sK0)))),
% 1.98/0.62    inference(resolution,[],[f184,f145])).
% 1.98/0.62  fof(f145,plain,(
% 1.98/0.62    ( ! [X2] : (r2_hidden(sK3(sK2,X2,sK2),k2_struct_0(sK0)) | sK2 = k4_xboole_0(sK2,k4_xboole_0(sK2,X2))) )),
% 1.98/0.62    inference(resolution,[],[f135,f58])).
% 1.98/0.62  fof(f58,plain,(
% 1.98/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.98/0.62    inference(backward_demodulation,[],[f22,f57])).
% 1.98/0.62  fof(f22,plain,(
% 1.98/0.62    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.98/0.62    inference(cnf_transformation,[],[f14])).
% 1.98/0.62  fof(f135,plain,(
% 1.98/0.62    ( ! [X4,X5,X3] : (~m1_subset_1(X3,k1_zfmisc_1(X5)) | k4_xboole_0(X3,k4_xboole_0(X3,X4)) = X3 | r2_hidden(sK3(X3,X4,X3),X5)) )),
% 1.98/0.62    inference(resolution,[],[f127,f37])).
% 1.98/0.62  fof(f37,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f20])).
% 1.98/0.62  fof(f20,plain,(
% 1.98/0.62    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.98/0.62    inference(ennf_transformation,[],[f5])).
% 1.98/0.62  fof(f5,axiom,(
% 1.98/0.62    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).
% 1.98/0.62  fof(f127,plain,(
% 1.98/0.62    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1,X0),X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 1.98/0.62    inference(factoring,[],[f50])).
% 1.98/0.62  fof(f50,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 1.98/0.62    inference(definition_unfolding,[],[f40,f36])).
% 1.98/0.62  fof(f40,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X0) | r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.98/0.62    inference(cnf_transformation,[],[f1])).
% 1.98/0.62  fof(f1,axiom,(
% 1.98/0.62    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 1.98/0.62  fof(f184,plain,(
% 1.98/0.62    ( ! [X12,X13] : (~r2_hidden(sK3(X12,X13,X12),X13) | k4_xboole_0(X12,k4_xboole_0(X12,X13)) = X12) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f179,f50])).
% 1.98/0.62  fof(f179,plain,(
% 1.98/0.62    ( ! [X12,X13] : (~r2_hidden(sK3(X12,X13,X12),X13) | ~r2_hidden(sK3(X12,X13,X12),X12) | k4_xboole_0(X12,k4_xboole_0(X12,X13)) = X12) )),
% 1.98/0.62    inference(duplicate_literal_removal,[],[f178])).
% 1.98/0.62  fof(f178,plain,(
% 1.98/0.62    ( ! [X12,X13] : (~r2_hidden(sK3(X12,X13,X12),X13) | ~r2_hidden(sK3(X12,X13,X12),X12) | k4_xboole_0(X12,k4_xboole_0(X12,X13)) = X12 | k4_xboole_0(X12,k4_xboole_0(X12,X13)) = X12) )),
% 1.98/0.62    inference(resolution,[],[f51,f127])).
% 1.98/0.62  fof(f51,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2) )),
% 1.98/0.62    inference(definition_unfolding,[],[f39,f36])).
% 1.98/0.62  fof(f39,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 1.98/0.62    inference(cnf_transformation,[],[f1])).
% 1.98/0.62  fof(f933,plain,(
% 1.98/0.62    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)))),
% 1.98/0.62    inference(forward_demodulation,[],[f929,f78])).
% 1.98/0.62  fof(f78,plain,(
% 1.98/0.62    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.98/0.62    inference(subsumption_resolution,[],[f77,f60])).
% 1.98/0.62  fof(f77,plain,(
% 1.98/0.62    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.98/0.62    inference(resolution,[],[f76,f26])).
% 1.98/0.62  fof(f26,plain,(
% 1.98/0.62    v1_tops_1(sK1,sK0)),
% 1.98/0.62    inference(cnf_transformation,[],[f14])).
% 1.98/0.62  fof(f76,plain,(
% 1.98/0.62    ( ! [X0] : (~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.98/0.62    inference(forward_demodulation,[],[f75,f57])).
% 1.98/0.62  fof(f75,plain,(
% 1.98/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0)) )),
% 1.98/0.62    inference(resolution,[],[f34,f28])).
% 1.98/0.62  fof(f34,plain,(
% 1.98/0.62    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 1.98/0.62    inference(cnf_transformation,[],[f17])).
% 1.98/0.62  fof(f17,plain,(
% 1.98/0.62    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.98/0.62    inference(ennf_transformation,[],[f9])).
% 1.98/0.62  fof(f9,axiom,(
% 1.98/0.62    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tops_1)).
% 1.98/0.62  fof(f929,plain,(
% 1.98/0.62    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1)))),
% 1.98/0.62    inference(resolution,[],[f926,f60])).
% 1.98/0.62  fof(f926,plain,(
% 1.98/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0))) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f925,f58])).
% 1.98/0.62  fof(f925,plain,(
% 1.98/0.62    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0))) )),
% 1.98/0.62    inference(resolution,[],[f292,f23])).
% 1.98/0.62  fof(f23,plain,(
% 1.98/0.62    v3_pre_topc(sK2,sK0)),
% 1.98/0.62    inference(cnf_transformation,[],[f14])).
% 1.98/0.62  fof(f292,plain,(
% 1.98/0.62    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))) )),
% 1.98/0.62    inference(forward_demodulation,[],[f291,f57])).
% 1.98/0.62  fof(f291,plain,(
% 1.98/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 1.98/0.62    inference(forward_demodulation,[],[f290,f57])).
% 1.98/0.62  fof(f290,plain,(
% 1.98/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 1.98/0.62    inference(forward_demodulation,[],[f289,f57])).
% 1.98/0.62  fof(f289,plain,(
% 1.98/0.62    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 1.98/0.62    inference(subsumption_resolution,[],[f288,f28])).
% 1.98/0.62  fof(f288,plain,(
% 1.98/0.62    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 1.98/0.62    inference(resolution,[],[f35,f27])).
% 1.98/0.62  fof(f27,plain,(
% 1.98/0.62    v2_pre_topc(sK0)),
% 1.98/0.62    inference(cnf_transformation,[],[f14])).
% 1.98/0.62  fof(f35,plain,(
% 1.98/0.62    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) )),
% 1.98/0.62    inference(cnf_transformation,[],[f19])).
% 1.98/0.62  fof(f19,plain,(
% 1.98/0.62    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.98/0.62    inference(flattening,[],[f18])).
% 1.98/0.62  fof(f18,plain,(
% 1.98/0.62    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.98/0.62    inference(ennf_transformation,[],[f10])).
% 1.98/0.62  fof(f10,axiom,(
% 1.98/0.62    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.98/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_tops_1)).
% 1.98/0.62  % SZS output end Proof for theBenchmark
% 1.98/0.62  % (19208)------------------------------
% 1.98/0.62  % (19208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.62  % (19208)Termination reason: Refutation
% 1.98/0.62  
% 1.98/0.62  % (19208)Memory used [KB]: 7547
% 1.98/0.62  % (19208)Time elapsed: 0.203 s
% 1.98/0.62  % (19208)------------------------------
% 1.98/0.62  % (19208)------------------------------
% 1.98/0.62  % (19201)Success in time 0.266 s
%------------------------------------------------------------------------------
