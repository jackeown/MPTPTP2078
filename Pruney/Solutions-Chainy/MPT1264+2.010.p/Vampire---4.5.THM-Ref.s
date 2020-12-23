%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:18 EST 2020

% Result     : Theorem 1.28s
% Output     : Refutation 1.28s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 321 expanded)
%              Number of leaves         :   13 (  71 expanded)
%              Depth                    :   17
%              Number of atoms          :  227 (1085 expanded)
%              Number of equality atoms :   59 ( 226 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f148,plain,(
    $false ),
    inference(subsumption_resolution,[],[f147,f95])).

fof(f95,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) ),
    inference(backward_demodulation,[],[f63,f94])).

fof(f94,plain,(
    ! [X3] : k9_subset_1(k2_struct_0(sK0),X3,sK1) = k9_subset_1(sK1,X3,sK1) ),
    inference(forward_demodulation,[],[f92,f90])).

fof(f90,plain,(
    ! [X0,X1] : k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(resolution,[],[f53,f59])).

fof(f59,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f35,f34])).

fof(f34,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f35,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f49,f41])).

fof(f41,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f92,plain,(
    ! [X3] : k9_subset_1(k2_struct_0(sK0),X3,sK1) = k1_setfam_1(k2_tarski(X3,sK1)) ),
    inference(resolution,[],[f53,f64])).

fof(f64,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f30,f61])).

fof(f61,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f36,f60])).

fof(f60,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f63,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) ),
    inference(backward_demodulation,[],[f29,f61])).

fof(f29,plain,(
    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f147,plain,(
    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1)) ),
    inference(forward_demodulation,[],[f146,f94])).

fof(f146,plain,(
    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) ),
    inference(forward_demodulation,[],[f145,f132])).

fof(f132,plain,(
    sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))) ),
    inference(resolution,[],[f124,f77])).

fof(f77,plain,(
    r1_tarski(sK2,k2_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0))
    | r1_tarski(sK2,k2_struct_0(sK0)) ),
    inference(resolution,[],[f72,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f72,plain,(
    ! [X2] :
      ( r2_hidden(sK3(sK2,X2),k2_struct_0(sK0))
      | r1_tarski(sK2,X2) ) ),
    inference(resolution,[],[f69,f62])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f27,f61])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r2_hidden(sK3(X0,X2),X1)
      | r1_tarski(X0,X2) ) ),
    inference(resolution,[],[f42,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f124,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(subsumption_resolution,[],[f123,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X0)
      | k1_setfam_1(k2_tarski(X0,X1)) = X0 ) ),
    inference(resolution,[],[f56,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(sK4(X0,X1,X2),X0)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X1,X2)) = X0 ) ),
    inference(definition_unfolding,[],[f52,f41])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(sK4(X0,X1,X2),X0)
      | k3_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = X0
      | ? [X3] :
          ( ~ r1_tarski(X3,X0)
          & r1_tarski(X3,X2)
          & r1_tarski(X3,X1) )
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ( r1_tarski(X3,X2)
              & r1_tarski(X3,X1) )
           => r1_tarski(X3,X0) )
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k3_xboole_0(X1,X2) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK4(X0,X1,X2),X1)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1)
      | k1_setfam_1(k2_tarski(X1,X2)) = X0 ) ),
    inference(definition_unfolding,[],[f50,f41])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(sK4(X0,X1,X2),X1)
      | k3_xboole_0(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f145,plain,(
    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f144,f90])).

fof(f144,plain,(
    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f139,f99])).

fof(f99,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f98,f64])).

fof(f98,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f97,f31])).

fof(f31,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_tops_1(X0,sK0)
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f96,f61])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k2_struct_0(sK0) = k2_pre_topc(sK0,X0)
      | ~ v1_tops_1(X0,sK0) ) ),
    inference(resolution,[],[f39,f33])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> k2_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).

fof(f139,plain,(
    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1))) ),
    inference(resolution,[],[f136,f64])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)) ) ),
    inference(subsumption_resolution,[],[f135,f62])).

fof(f135,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0)) ) ),
    inference(resolution,[],[f129,f28])).

fof(f28,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1)) ) ),
    inference(forward_demodulation,[],[f128,f61])).

fof(f128,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(forward_demodulation,[],[f127,f61])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(forward_demodulation,[],[f126,f61])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(subsumption_resolution,[],[f125,f33])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)) ) ),
    inference(resolution,[],[f40,f32])).

% (25939)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( v3_pre_topc(X1,X0)
               => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:12:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.28/0.53  % (25918)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.28/0.53  % (25917)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.28/0.54  % (25920)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.28/0.54  % (25944)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.28/0.54  % (25921)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.28/0.54  % (25919)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.28/0.54  % (25936)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.28/0.54  % (25924)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.28/0.54  % (25922)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.28/0.54  % (25943)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.28/0.54  % (25924)Refutation not found, incomplete strategy% (25924)------------------------------
% 1.28/0.54  % (25924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (25924)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (25924)Memory used [KB]: 10746
% 1.28/0.54  % (25924)Time elapsed: 0.123 s
% 1.28/0.54  % (25924)------------------------------
% 1.28/0.54  % (25924)------------------------------
% 1.28/0.54  % (25920)Refutation not found, incomplete strategy% (25920)------------------------------
% 1.28/0.54  % (25920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.54  % (25920)Termination reason: Refutation not found, incomplete strategy
% 1.28/0.54  
% 1.28/0.54  % (25920)Memory used [KB]: 6268
% 1.28/0.54  % (25920)Time elapsed: 0.123 s
% 1.28/0.54  % (25920)------------------------------
% 1.28/0.54  % (25920)------------------------------
% 1.28/0.54  % (25922)Refutation found. Thanks to Tanya!
% 1.28/0.54  % SZS status Theorem for theBenchmark
% 1.28/0.54  % SZS output start Proof for theBenchmark
% 1.28/0.54  fof(f148,plain,(
% 1.28/0.54    $false),
% 1.28/0.54    inference(subsumption_resolution,[],[f147,f95])).
% 1.28/0.54  fof(f95,plain,(
% 1.28/0.54    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1))),
% 1.28/0.54    inference(backward_demodulation,[],[f63,f94])).
% 1.28/0.54  fof(f94,plain,(
% 1.28/0.54    ( ! [X3] : (k9_subset_1(k2_struct_0(sK0),X3,sK1) = k9_subset_1(sK1,X3,sK1)) )),
% 1.28/0.54    inference(forward_demodulation,[],[f92,f90])).
% 1.28/0.54  fof(f90,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k9_subset_1(X0,X1,X0) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 1.28/0.54    inference(resolution,[],[f53,f59])).
% 1.28/0.54  fof(f59,plain,(
% 1.28/0.54    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 1.28/0.54    inference(forward_demodulation,[],[f35,f34])).
% 1.28/0.54  fof(f34,plain,(
% 1.28/0.54    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 1.28/0.54    inference(cnf_transformation,[],[f4])).
% 1.28/0.54  fof(f4,axiom,(
% 1.28/0.54    ! [X0] : k2_subset_1(X0) = X0),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 1.28/0.54  fof(f35,plain,(
% 1.28/0.54    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 1.28/0.54    inference(cnf_transformation,[],[f5])).
% 1.28/0.54  fof(f5,axiom,(
% 1.28/0.54    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 1.28/0.54  fof(f53,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 1.28/0.54    inference(definition_unfolding,[],[f49,f41])).
% 1.28/0.54  fof(f41,plain,(
% 1.28/0.54    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f8])).
% 1.28/0.54  fof(f8,axiom,(
% 1.28/0.54    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.28/0.54  fof(f49,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f24])).
% 1.28/0.54  fof(f24,plain,(
% 1.28/0.54    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f7])).
% 1.28/0.54  fof(f7,axiom,(
% 1.28/0.54    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.28/0.54  fof(f92,plain,(
% 1.28/0.54    ( ! [X3] : (k9_subset_1(k2_struct_0(sK0),X3,sK1) = k1_setfam_1(k2_tarski(X3,sK1))) )),
% 1.28/0.54    inference(resolution,[],[f53,f64])).
% 1.28/0.54  fof(f64,plain,(
% 1.28/0.54    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.28/0.54    inference(backward_demodulation,[],[f30,f61])).
% 1.28/0.54  fof(f61,plain,(
% 1.28/0.54    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.28/0.54    inference(resolution,[],[f36,f60])).
% 1.28/0.54  fof(f60,plain,(
% 1.28/0.54    l1_struct_0(sK0)),
% 1.28/0.54    inference(resolution,[],[f37,f33])).
% 1.28/0.54  fof(f33,plain,(
% 1.28/0.54    l1_pre_topc(sK0)),
% 1.28/0.54    inference(cnf_transformation,[],[f16])).
% 1.28/0.54  fof(f16,plain,(
% 1.28/0.54    ? [X0] : (? [X1] : (? [X2] : (k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.28/0.54    inference(flattening,[],[f15])).
% 1.28/0.54  fof(f15,plain,(
% 1.28/0.54    ? [X0] : (? [X1] : ((? [X2] : ((k2_pre_topc(X0,X2) != k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)) & v3_pre_topc(X2,X0)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f14])).
% 1.28/0.54  fof(f14,negated_conjecture,(
% 1.28/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 1.28/0.54    inference(negated_conjecture,[],[f13])).
% 1.28/0.54  fof(f13,conjecture,(
% 1.28/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X2,X0) => k2_pre_topc(X0,X2) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X2,X1)))))))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_tops_1)).
% 1.28/0.54  fof(f37,plain,(
% 1.28/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f18])).
% 1.28/0.54  fof(f18,plain,(
% 1.28/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.28/0.54    inference(ennf_transformation,[],[f10])).
% 1.28/0.54  fof(f10,axiom,(
% 1.28/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.28/0.54  fof(f36,plain,(
% 1.28/0.54    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f17])).
% 1.28/0.54  fof(f17,plain,(
% 1.28/0.54    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.28/0.54    inference(ennf_transformation,[],[f9])).
% 1.28/0.54  fof(f9,axiom,(
% 1.28/0.54    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.28/0.54  fof(f30,plain,(
% 1.28/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.28/0.54    inference(cnf_transformation,[],[f16])).
% 1.28/0.54  fof(f63,plain,(
% 1.28/0.54    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))),
% 1.28/0.54    inference(backward_demodulation,[],[f29,f61])).
% 1.28/0.54  fof(f29,plain,(
% 1.28/0.54    k2_pre_topc(sK0,sK2) != k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK1))),
% 1.28/0.54    inference(cnf_transformation,[],[f16])).
% 1.28/0.54  fof(f147,plain,(
% 1.28/0.54    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(sK1,sK2,sK1))),
% 1.28/0.54    inference(forward_demodulation,[],[f146,f94])).
% 1.28/0.54  fof(f146,plain,(
% 1.28/0.54    k2_pre_topc(sK0,sK2) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1))),
% 1.28/0.54    inference(forward_demodulation,[],[f145,f132])).
% 1.28/0.54  fof(f132,plain,(
% 1.28/0.54    sK2 = k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0)))),
% 1.28/0.54    inference(resolution,[],[f124,f77])).
% 1.28/0.54  fof(f77,plain,(
% 1.28/0.54    r1_tarski(sK2,k2_struct_0(sK0))),
% 1.28/0.54    inference(duplicate_literal_removal,[],[f74])).
% 1.28/0.54  fof(f74,plain,(
% 1.28/0.54    r1_tarski(sK2,k2_struct_0(sK0)) | r1_tarski(sK2,k2_struct_0(sK0))),
% 1.28/0.54    inference(resolution,[],[f72,f48])).
% 1.28/0.54  fof(f48,plain,(
% 1.28/0.54    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f23])).
% 1.28/0.54  fof(f23,plain,(
% 1.28/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f1])).
% 1.28/0.54  fof(f1,axiom,(
% 1.28/0.54    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.28/0.54  fof(f72,plain,(
% 1.28/0.54    ( ! [X2] : (r2_hidden(sK3(sK2,X2),k2_struct_0(sK0)) | r1_tarski(sK2,X2)) )),
% 1.28/0.54    inference(resolution,[],[f69,f62])).
% 1.28/0.54  fof(f62,plain,(
% 1.28/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.28/0.54    inference(backward_demodulation,[],[f27,f61])).
% 1.28/0.54  fof(f27,plain,(
% 1.28/0.54    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.28/0.54    inference(cnf_transformation,[],[f16])).
% 1.28/0.54  fof(f69,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r2_hidden(sK3(X0,X2),X1) | r1_tarski(X0,X2)) )),
% 1.28/0.54    inference(resolution,[],[f42,f47])).
% 1.28/0.54  fof(f47,plain,(
% 1.28/0.54    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f23])).
% 1.28/0.54  fof(f42,plain,(
% 1.28/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 1.28/0.54    inference(cnf_transformation,[],[f22])).
% 1.28/0.54  fof(f22,plain,(
% 1.28/0.54    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.28/0.54    inference(ennf_transformation,[],[f6])).
% 1.28/0.54  fof(f6,axiom,(
% 1.28/0.54    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.28/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.28/0.55  fof(f124,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.28/0.55    inference(subsumption_resolution,[],[f123,f57])).
% 1.28/0.55  fof(f57,plain,(
% 1.28/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.28/0.55    inference(equality_resolution,[],[f44])).
% 1.28/0.55  fof(f44,plain,(
% 1.28/0.55    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.28/0.55    inference(cnf_transformation,[],[f2])).
% 1.28/0.55  fof(f2,axiom,(
% 1.28/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.28/0.55  fof(f123,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X0) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.28/0.55    inference(duplicate_literal_removal,[],[f119])).
% 1.28/0.55  fof(f119,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X0) | k1_setfam_1(k2_tarski(X0,X1)) = X0 | ~r1_tarski(X0,X1) | ~r1_tarski(X0,X0) | k1_setfam_1(k2_tarski(X0,X1)) = X0) )),
% 1.28/0.55    inference(resolution,[],[f56,f54])).
% 1.28/0.55  fof(f54,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (~r1_tarski(sK4(X0,X1,X2),X0) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X1,X2)) = X0) )),
% 1.28/0.55    inference(definition_unfolding,[],[f52,f41])).
% 1.28/0.55  fof(f52,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | ~r1_tarski(sK4(X0,X1,X2),X0) | k3_xboole_0(X1,X2) = X0) )),
% 1.28/0.55    inference(cnf_transformation,[],[f26])).
% 1.28/0.55  fof(f26,plain,(
% 1.28/0.55    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | ? [X3] : (~r1_tarski(X3,X0) & r1_tarski(X3,X2) & r1_tarski(X3,X1)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.28/0.55    inference(flattening,[],[f25])).
% 1.28/0.55  fof(f25,plain,(
% 1.28/0.55    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = X0 | (? [X3] : (~r1_tarski(X3,X0) & (r1_tarski(X3,X2) & r1_tarski(X3,X1))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.28/0.55    inference(ennf_transformation,[],[f3])).
% 1.28/0.55  fof(f3,axiom,(
% 1.28/0.55    ! [X0,X1,X2] : ((! [X3] : ((r1_tarski(X3,X2) & r1_tarski(X3,X1)) => r1_tarski(X3,X0)) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k3_xboole_0(X1,X2) = X0)),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).
% 1.28/0.55  fof(f56,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (r1_tarski(sK4(X0,X1,X2),X1) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1) | k1_setfam_1(k2_tarski(X1,X2)) = X0) )),
% 1.28/0.55    inference(definition_unfolding,[],[f50,f41])).
% 1.28/0.55  fof(f50,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X0,X2) | r1_tarski(sK4(X0,X1,X2),X1) | k3_xboole_0(X1,X2) = X0) )),
% 1.28/0.55    inference(cnf_transformation,[],[f26])).
% 1.28/0.55  fof(f145,plain,(
% 1.28/0.55    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK2,k2_struct_0(sK0))))),
% 1.28/0.55    inference(forward_demodulation,[],[f144,f90])).
% 1.28/0.55  fof(f144,plain,(
% 1.28/0.55    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_struct_0(sK0)))),
% 1.28/0.55    inference(forward_demodulation,[],[f139,f99])).
% 1.28/0.55  fof(f99,plain,(
% 1.28/0.55    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 1.28/0.55    inference(subsumption_resolution,[],[f98,f64])).
% 1.28/0.55  fof(f98,plain,(
% 1.28/0.55    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.28/0.55    inference(resolution,[],[f97,f31])).
% 1.28/0.55  fof(f31,plain,(
% 1.28/0.55    v1_tops_1(sK1,sK0)),
% 1.28/0.55    inference(cnf_transformation,[],[f16])).
% 1.28/0.55  fof(f97,plain,(
% 1.28/0.55    ( ! [X0] : (~v1_tops_1(X0,sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.28/0.55    inference(forward_demodulation,[],[f96,f61])).
% 1.28/0.55  fof(f96,plain,(
% 1.28/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_struct_0(sK0) = k2_pre_topc(sK0,X0) | ~v1_tops_1(X0,sK0)) )),
% 1.28/0.55    inference(resolution,[],[f39,f33])).
% 1.28/0.55  fof(f39,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 1.28/0.55    inference(cnf_transformation,[],[f19])).
% 1.28/0.55  fof(f19,plain,(
% 1.28/0.55    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.28/0.55    inference(ennf_transformation,[],[f11])).
% 1.28/0.55  fof(f11,axiom,(
% 1.28/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> k2_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tops_1)).
% 1.28/0.55  fof(f139,plain,(
% 1.28/0.55    k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,sK1)) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,sK1)))),
% 1.28/0.55    inference(resolution,[],[f136,f64])).
% 1.28/0.55  fof(f136,plain,(
% 1.28/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0))) )),
% 1.28/0.55    inference(subsumption_resolution,[],[f135,f62])).
% 1.28/0.55  fof(f135,plain,(
% 1.28/0.55    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,k2_pre_topc(sK0,X0))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),sK2,X0))) )),
% 1.28/0.55    inference(resolution,[],[f129,f28])).
% 1.28/0.55  fof(f28,plain,(
% 1.28/0.55    v3_pre_topc(sK2,sK0)),
% 1.28/0.55    inference(cnf_transformation,[],[f16])).
% 1.28/0.55  fof(f129,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(k2_struct_0(sK0),X0,X1))) )),
% 1.28/0.55    inference(forward_demodulation,[],[f128,f61])).
% 1.28/0.55  fof(f128,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 1.28/0.55    inference(forward_demodulation,[],[f127,f61])).
% 1.28/0.55  fof(f127,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 1.28/0.55    inference(forward_demodulation,[],[f126,f61])).
% 1.28/0.55  fof(f126,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 1.28/0.55    inference(subsumption_resolution,[],[f125,f33])).
% 1.28/0.55  fof(f125,plain,(
% 1.28/0.55    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0) | k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1))) = k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1))) )),
% 1.28/0.55    inference(resolution,[],[f40,f32])).
% 1.28/0.55  % (25939)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.28/0.55  fof(f32,plain,(
% 1.28/0.55    v2_pre_topc(sK0)),
% 1.28/0.55    inference(cnf_transformation,[],[f16])).
% 1.28/0.55  fof(f40,plain,(
% 1.28/0.55    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) )),
% 1.28/0.55    inference(cnf_transformation,[],[f21])).
% 1.28/0.55  fof(f21,plain,(
% 1.28/0.55    ! [X0] : (! [X1] : (! [X2] : (k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.28/0.55    inference(flattening,[],[f20])).
% 1.28/0.55  fof(f20,plain,(
% 1.28/0.55    ! [X0] : (! [X1] : (! [X2] : ((k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.28/0.55    inference(ennf_transformation,[],[f12])).
% 1.28/0.55  fof(f12,axiom,(
% 1.28/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2))) = k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2))))))),
% 1.28/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tops_1)).
% 1.28/0.55  % SZS output end Proof for theBenchmark
% 1.28/0.55  % (25922)------------------------------
% 1.28/0.55  % (25922)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.28/0.55  % (25922)Termination reason: Refutation
% 1.28/0.55  
% 1.28/0.55  % (25922)Memory used [KB]: 6396
% 1.28/0.55  % (25922)Time elapsed: 0.125 s
% 1.28/0.55  % (25922)------------------------------
% 1.28/0.55  % (25922)------------------------------
% 1.28/0.55  % (25934)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.44/0.55  % (25915)Success in time 0.183 s
%------------------------------------------------------------------------------
