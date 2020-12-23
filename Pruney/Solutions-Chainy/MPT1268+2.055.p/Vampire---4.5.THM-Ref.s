%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 626 expanded)
%              Number of leaves         :   11 ( 125 expanded)
%              Depth                    :   23
%              Number of atoms          :  293 (3043 expanded)
%              Number of equality atoms :   53 ( 391 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f676,plain,(
    $false ),
    inference(subsumption_resolution,[],[f675,f424])).

fof(f424,plain,(
    k1_xboole_0 != sK2 ),
    inference(subsumption_resolution,[],[f418,f90])).

fof(f90,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | k1_xboole_0 != sK2 ),
    inference(subsumption_resolution,[],[f89,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
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
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

fof(f89,plain,
    ( k1_xboole_0 != sK2
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f88,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,
    ( k1_xboole_0 != sK2
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f28,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f28,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f14])).

fof(f418,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | k1_xboole_0 != sK2 ),
    inference(resolution,[],[f416,f28])).

fof(f416,plain,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f415,f119])).

fof(f119,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f118,f77])).

fof(f77,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f30,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f118,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | r1_tarski(k1_tops_1(sK0,sK1),X0) ) ),
    inference(superposition,[],[f48,f105])).

fof(f105,plain,(
    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f102,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f102,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f55,f30])).

fof(f55,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X0),X0) ) ),
    inference(resolution,[],[f32,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f415,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f411,f102])).

fof(f411,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f309,f30])).

fof(f309,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = k1_tops_1(sK0,X0)
      | v2_tops_1(sK1,sK0)
      | ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
      | ~ r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f116,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f5])).

fof(f116,plain,(
    ! [X2] :
      ( ~ m1_subset_1(k1_tops_1(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k1_tops_1(sK0,X2),sK1)
      | k1_xboole_0 = k1_tops_1(sK0,X2)
      | v2_tops_1(sK1,sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f115,f32])).

fof(f115,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_tops_1(sK0,X2),sK1)
      | ~ m1_subset_1(k1_tops_1(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = k1_tops_1(sK0,X2)
      | v2_tops_1(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f111,f31])).

fof(f31,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f111,plain,(
    ! [X2] :
      ( ~ r1_tarski(k1_tops_1(sK0,X2),sK1)
      | ~ m1_subset_1(k1_tops_1(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = k1_tops_1(sK0,X2)
      | v2_tops_1(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f29,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f29,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(X2,sK0)
      | ~ r1_tarski(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X2
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f675,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f674,f42])).

fof(f42,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f674,plain,(
    ! [X2] : ~ r2_hidden(X2,sK2) ),
    inference(subsumption_resolution,[],[f673,f165])).

fof(f165,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f150,f158])).

fof(f158,plain,(
    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0) ),
    inference(resolution,[],[f150,f42])).

fof(f150,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_tops_1(sK0,k1_xboole_0)) ),
    inference(resolution,[],[f149,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f149,plain,(
    ! [X0] : r1_tarski(k1_tops_1(sK0,k1_xboole_0),X0) ),
    inference(subsumption_resolution,[],[f148,f33])).

fof(f33,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f148,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_xboole_0,X0)
      | r1_tarski(k1_tops_1(sK0,k1_xboole_0),X0) ) ),
    inference(superposition,[],[f48,f138])).

fof(f138,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f131,f43])).

fof(f131,plain,(
    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f101,f33])).

fof(f101,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,u1_struct_0(sK0))
      | r1_tarski(k1_tops_1(sK0,X2),X2) ) ),
    inference(resolution,[],[f55,f45])).

fof(f673,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_xboole_0)
      | ~ r2_hidden(X2,sK2) ) ),
    inference(forward_demodulation,[],[f672,f428])).

fof(f428,plain,(
    k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f427,f30])).

fof(f427,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f422,f32])).

fof(f422,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f421])).

fof(f421,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f416,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f672,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK2)
      | r2_hidden(X2,k1_tops_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f669,f426])).

fof(f426,plain,(
    r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f420,f84])).

fof(f84,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f83,f30])).

fof(f83,plain,
    ( r1_tarski(sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f82,f32])).

fof(f82,plain,
    ( r1_tarski(sK2,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f26,f35])).

fof(f26,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f420,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f416,f26])).

fof(f669,plain,(
    ! [X2] :
      ( ~ r1_tarski(sK2,sK1)
      | ~ r2_hidden(X2,sK2)
      | r2_hidden(X2,k1_tops_1(sK0,sK1)) ) ),
    inference(resolution,[],[f520,f30])).

fof(f520,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f519,f423])).

fof(f423,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f417,f94])).

fof(f94,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f93,f30])).

fof(f93,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f92,f32])).

fof(f92,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f25,f35])).

fof(f25,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f417,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f416,f25])).

fof(f519,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f518,f32])).

fof(f518,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f514,f31])).

fof(f514,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | ~ r2_hidden(X1,sK2)
      | r2_hidden(X1,k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f425,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

fof(f425,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f419,f87])).

fof(f87,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f86,f30])).

fof(f86,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f85,f32])).

fof(f85,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f27,f35])).

fof(f27,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f419,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f416,f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 12:34:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.41  % (24974)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.45  % (24982)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.45  % (24982)Refutation found. Thanks to Tanya!
% 0.22/0.45  % SZS status Theorem for theBenchmark
% 0.22/0.46  % (24989)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (24989)Refutation not found, incomplete strategy% (24989)------------------------------
% 0.22/0.46  % (24989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (24981)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (24976)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.47  % (24989)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (24989)Memory used [KB]: 10618
% 0.22/0.47  % (24989)Time elapsed: 0.057 s
% 0.22/0.47  % (24989)------------------------------
% 0.22/0.47  % (24989)------------------------------
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f676,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(subsumption_resolution,[],[f675,f424])).
% 0.22/0.47  fof(f424,plain,(
% 0.22/0.47    k1_xboole_0 != sK2),
% 0.22/0.47    inference(subsumption_resolution,[],[f418,f90])).
% 0.22/0.47  fof(f90,plain,(
% 0.22/0.47    k1_xboole_0 != k1_tops_1(sK0,sK1) | k1_xboole_0 != sK2),
% 0.22/0.47    inference(subsumption_resolution,[],[f89,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f12])).
% 0.22/0.47  fof(f12,negated_conjecture,(
% 0.22/0.47    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.22/0.47    inference(negated_conjecture,[],[f11])).
% 0.22/0.47  fof(f11,conjecture,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    k1_xboole_0 != sK2 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f88,f32])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    l1_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    k1_xboole_0 != sK2 | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.22/0.47    inference(resolution,[],[f28,f35])).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ~v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f418,plain,(
% 0.22/0.47    k1_xboole_0 = k1_tops_1(sK0,sK1) | k1_xboole_0 != sK2),
% 0.22/0.47    inference(resolution,[],[f416,f28])).
% 0.22/0.47  fof(f416,plain,(
% 0.22/0.47    v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f415,f119])).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.47    inference(resolution,[],[f118,f77])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.22/0.47    inference(resolution,[],[f30,f46])).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(k1_tops_1(sK0,sK1),X0)) )),
% 0.22/0.47    inference(superposition,[],[f48,f105])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    sK1 = k2_xboole_0(k1_tops_1(sK0,sK1),sK1)),
% 0.22/0.47    inference(resolution,[],[f102,f43])).
% 0.22/0.47  fof(f43,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.47    inference(cnf_transformation,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.22/0.47    inference(resolution,[],[f55,f30])).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X0),X0)) )),
% 0.22/0.47    inference(resolution,[],[f32,f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.47  fof(f415,plain,(
% 0.22/0.47    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.47    inference(subsumption_resolution,[],[f411,f102])).
% 0.22/0.47  fof(f411,plain,(
% 0.22/0.47    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))),
% 0.22/0.47    inference(resolution,[],[f309,f30])).
% 0.22/0.47  fof(f309,plain,(
% 0.22/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,X0) | v2_tops_1(sK1,sK0) | ~r1_tarski(k1_tops_1(sK0,X0),sK1) | ~r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0))) )),
% 0.22/0.47    inference(resolution,[],[f116,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f116,plain,(
% 0.22/0.47    ( ! [X2] : (~m1_subset_1(k1_tops_1(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,X2),sK1) | k1_xboole_0 = k1_tops_1(sK0,X2) | v2_tops_1(sK1,sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f115,f32])).
% 0.22/0.47  fof(f115,plain,(
% 0.22/0.47    ( ! [X2] : (~r1_tarski(k1_tops_1(sK0,X2),sK1) | ~m1_subset_1(k1_tops_1(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,X2) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f111,f31])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    v2_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f111,plain,(
% 0.22/0.47    ( ! [X2] : (~r1_tarski(k1_tops_1(sK0,X2),sK1) | ~m1_subset_1(k1_tops_1(sK0,X2),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,X2) | v2_tops_1(sK1,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.47    inference(resolution,[],[f29,f44])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f22])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X2] : (~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | v2_tops_1(sK1,sK0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f675,plain,(
% 0.22/0.47    k1_xboole_0 = sK2),
% 0.22/0.47    inference(resolution,[],[f674,f42])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.47  fof(f674,plain,(
% 0.22/0.47    ( ! [X2] : (~r2_hidden(X2,sK2)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f673,f165])).
% 0.22/0.47  fof(f165,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.22/0.47    inference(backward_demodulation,[],[f150,f158])).
% 0.22/0.47  fof(f158,plain,(
% 0.22/0.47    k1_xboole_0 = k1_tops_1(sK0,k1_xboole_0)),
% 0.22/0.47    inference(resolution,[],[f150,f42])).
% 0.22/0.47  fof(f150,plain,(
% 0.22/0.47    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,k1_xboole_0))) )),
% 0.22/0.47    inference(resolution,[],[f149,f47])).
% 0.22/0.47  fof(f47,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f23])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.47  fof(f149,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(k1_tops_1(sK0,k1_xboole_0),X0)) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f148,f33])).
% 0.22/0.47  fof(f33,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.47  fof(f148,plain,(
% 0.22/0.47    ( ! [X0] : (~r1_tarski(k1_xboole_0,X0) | r1_tarski(k1_tops_1(sK0,k1_xboole_0),X0)) )),
% 0.22/0.47    inference(superposition,[],[f48,f138])).
% 0.22/0.47  fof(f138,plain,(
% 0.22/0.47    k1_xboole_0 = k2_xboole_0(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.47    inference(resolution,[],[f131,f43])).
% 0.22/0.47  fof(f131,plain,(
% 0.22/0.47    r1_tarski(k1_tops_1(sK0,k1_xboole_0),k1_xboole_0)),
% 0.22/0.47    inference(resolution,[],[f101,f33])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    ( ! [X2] : (~r1_tarski(X2,u1_struct_0(sK0)) | r1_tarski(k1_tops_1(sK0,X2),X2)) )),
% 0.22/0.47    inference(resolution,[],[f55,f45])).
% 0.22/0.47  fof(f673,plain,(
% 0.22/0.47    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,sK2)) )),
% 0.22/0.47    inference(forward_demodulation,[],[f672,f428])).
% 0.22/0.47  fof(f428,plain,(
% 0.22/0.47    k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f427,f30])).
% 0.22/0.47  fof(f427,plain,(
% 0.22/0.47    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(subsumption_resolution,[],[f422,f32])).
% 0.22/0.47  fof(f422,plain,(
% 0.22/0.47    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f421])).
% 0.22/0.47  fof(f421,plain,(
% 0.22/0.47    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.22/0.47    inference(resolution,[],[f416,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f672,plain,(
% 0.22/0.47    ( ! [X2] : (~r2_hidden(X2,sK2) | r2_hidden(X2,k1_tops_1(sK0,sK1))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f669,f426])).
% 0.22/0.47  fof(f426,plain,(
% 0.22/0.47    r1_tarski(sK2,sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f420,f84])).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    k1_xboole_0 != k1_tops_1(sK0,sK1) | r1_tarski(sK2,sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f83,f30])).
% 0.22/0.47  fof(f83,plain,(
% 0.22/0.47    r1_tarski(sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f82,f32])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    r1_tarski(sK2,sK1) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.22/0.47    inference(resolution,[],[f26,f35])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ~v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f420,plain,(
% 0.22/0.47    k1_xboole_0 = k1_tops_1(sK0,sK1) | r1_tarski(sK2,sK1)),
% 0.22/0.47    inference(resolution,[],[f416,f26])).
% 0.22/0.47  fof(f669,plain,(
% 0.22/0.47    ( ! [X2] : (~r1_tarski(sK2,sK1) | ~r2_hidden(X2,sK2) | r2_hidden(X2,k1_tops_1(sK0,sK1))) )),
% 0.22/0.47    inference(resolution,[],[f520,f30])).
% 0.22/0.47  fof(f520,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | ~r2_hidden(X1,sK2) | r2_hidden(X1,k1_tops_1(sK0,X0))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f519,f423])).
% 0.22/0.47  fof(f423,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(subsumption_resolution,[],[f417,f94])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    k1_xboole_0 != k1_tops_1(sK0,sK1) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(subsumption_resolution,[],[f93,f30])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f92,f32])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.22/0.47    inference(resolution,[],[f25,f35])).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ~v2_tops_1(sK1,sK0) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f417,plain,(
% 0.22/0.47    k1_xboole_0 = k1_tops_1(sK0,sK1) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(resolution,[],[f416,f25])).
% 0.22/0.47  fof(f519,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | ~r2_hidden(X1,sK2) | r2_hidden(X1,k1_tops_1(sK0,X0))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f518,f32])).
% 0.22/0.47  fof(f518,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | ~r2_hidden(X1,sK2) | r2_hidden(X1,k1_tops_1(sK0,X0))) )),
% 0.22/0.47    inference(subsumption_resolution,[],[f514,f31])).
% 0.22/0.47  fof(f514,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | ~r2_hidden(X1,sK2) | r2_hidden(X1,k1_tops_1(sK0,X0))) )),
% 0.22/0.47    inference(resolution,[],[f425,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X2) | ~r2_hidden(X1,X3) | r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f9])).
% 0.22/0.47  fof(f9,axiom,(
% 0.22/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).
% 0.22/0.47  fof(f425,plain,(
% 0.22/0.47    v3_pre_topc(sK2,sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f419,f87])).
% 0.22/0.47  fof(f87,plain,(
% 0.22/0.47    k1_xboole_0 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK2,sK0)),
% 0.22/0.47    inference(subsumption_resolution,[],[f86,f30])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.22/0.47    inference(subsumption_resolution,[],[f85,f32])).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    v3_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.22/0.47    inference(resolution,[],[f27,f35])).
% 0.22/0.47  fof(f27,plain,(
% 0.22/0.47    ~v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f419,plain,(
% 0.22/0.47    k1_xboole_0 = k1_tops_1(sK0,sK1) | v3_pre_topc(sK2,sK0)),
% 0.22/0.47    inference(resolution,[],[f416,f27])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (24982)------------------------------
% 0.22/0.47  % (24982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (24982)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (24982)Memory used [KB]: 1791
% 0.22/0.47  % (24982)Time elapsed: 0.072 s
% 0.22/0.47  % (24982)------------------------------
% 0.22/0.47  % (24982)------------------------------
% 0.22/0.47  % (24970)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.47  % (24968)Success in time 0.116 s
%------------------------------------------------------------------------------
