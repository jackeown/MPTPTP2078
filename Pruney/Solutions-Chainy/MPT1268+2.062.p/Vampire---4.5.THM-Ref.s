%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:35 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 459 expanded)
%              Number of leaves         :    8 (  87 expanded)
%              Depth                    :   21
%              Number of atoms          :  251 (2424 expanded)
%              Number of equality atoms :   47 ( 307 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f838,plain,(
    $false ),
    inference(subsumption_resolution,[],[f820,f191])).

fof(f191,plain,(
    k1_xboole_0 != sK2 ),
    inference(subsumption_resolution,[],[f185,f63])).

fof(f63,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | k1_xboole_0 != sK2 ),
    inference(subsumption_resolution,[],[f62,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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

fof(f62,plain,
    ( k1_xboole_0 != sK2
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f61,f28])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f61,plain,
    ( k1_xboole_0 != sK2
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f24,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f24,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f11])).

fof(f185,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | k1_xboole_0 != sK2 ),
    inference(resolution,[],[f183,f24])).

fof(f183,plain,
    ( v2_tops_1(sK1,sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f182,f77])).

fof(f77,plain,(
    r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f43,f26])).

fof(f43,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(k1_tops_1(sK0,X5),X5) ) ),
    inference(resolution,[],[f28,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).

fof(f182,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f136,f26])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = k1_tops_1(sK0,X0)
      | v2_tops_1(sK1,sK0)
      | ~ r1_tarski(k1_tops_1(sK0,X0),sK1) ) ),
    inference(subsumption_resolution,[],[f134,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | r1_tarski(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f50,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f26,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f134,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
      | k1_xboole_0 = k1_tops_1(sK0,X0)
      | v2_tops_1(sK1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f72,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f72,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
      | k1_xboole_0 = k1_tops_1(sK0,X0)
      | v2_tops_1(sK1,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f71,f28])).

fof(f71,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = k1_tops_1(sK0,X0)
      | v2_tops_1(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f70,f27])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f70,plain,(
    ! [X0] :
      ( ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
      | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = k1_tops_1(sK0,X0)
      | v2_tops_1(sK1,sK0)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f25,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f25,plain,(
    ! [X2] :
      ( ~ v3_pre_topc(X2,sK0)
      | ~ r1_tarski(X2,sK1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_xboole_0 = X2
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f820,plain,(
    k1_xboole_0 = sK2 ),
    inference(resolution,[],[f811,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f811,plain,(
    r1_tarski(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f810,f195])).

fof(f195,plain,(
    k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f194,f26])).

fof(f194,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f189,f28])).

fof(f189,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f183,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f810,plain,(
    r1_tarski(sK2,k1_tops_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f808,f193])).

fof(f193,plain,(
    r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f187,f57])).

fof(f57,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f56,f26])).

fof(f56,plain,
    ( r1_tarski(sK2,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f55,f28])).

fof(f55,plain,
    ( r1_tarski(sK2,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f22,f30])).

fof(f22,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f187,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f183,f22])).

fof(f808,plain,
    ( ~ r1_tarski(sK2,sK1)
    | r1_tarski(sK2,k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f244,f26])).

fof(f244,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f243,f190])).

fof(f190,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f184,f69])).

fof(f69,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f68,f26])).

fof(f68,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f67,f28])).

fof(f67,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f21,f30])).

fof(f21,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f184,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f183,f21])).

fof(f243,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f239,f28])).

fof(f239,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(sK2,X0)
      | r1_tarski(sK2,k1_tops_1(sK0,X0)) ) ),
    inference(resolution,[],[f192,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f192,plain,(
    v3_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f186,f60])).

fof(f60,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK2,sK0) ),
    inference(subsumption_resolution,[],[f59,f26])).

fof(f59,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f58,f28])).

fof(f58,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 != k1_tops_1(sK0,sK1) ),
    inference(resolution,[],[f23,f30])).

fof(f23,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | v3_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f186,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK2,sK0) ),
    inference(resolution,[],[f183,f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:45:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.43  % (23375)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.44  % (23375)Refutation found. Thanks to Tanya!
% 0.20/0.44  % SZS status Theorem for theBenchmark
% 0.20/0.44  % SZS output start Proof for theBenchmark
% 0.20/0.44  fof(f838,plain,(
% 0.20/0.44    $false),
% 0.20/0.44    inference(subsumption_resolution,[],[f820,f191])).
% 0.20/0.44  fof(f191,plain,(
% 0.20/0.44    k1_xboole_0 != sK2),
% 0.20/0.44    inference(subsumption_resolution,[],[f185,f63])).
% 0.20/0.44  fof(f63,plain,(
% 0.20/0.44    k1_xboole_0 != k1_tops_1(sK0,sK1) | k1_xboole_0 != sK2),
% 0.20/0.44    inference(subsumption_resolution,[],[f62,f26])).
% 0.20/0.44  fof(f26,plain,(
% 0.20/0.44    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f11,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.44    inference(flattening,[],[f10])).
% 0.20/0.44  fof(f10,plain,(
% 0.20/0.44    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.44    inference(ennf_transformation,[],[f9])).
% 0.20/0.44  fof(f9,negated_conjecture,(
% 0.20/0.44    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.44    inference(negated_conjecture,[],[f8])).
% 0.20/0.44  fof(f8,conjecture,(
% 0.20/0.44    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).
% 0.20/0.44  fof(f62,plain,(
% 0.20/0.44    k1_xboole_0 != sK2 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f61,f28])).
% 0.20/0.44  fof(f28,plain,(
% 0.20/0.44    l1_pre_topc(sK0)),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f61,plain,(
% 0.20/0.44    k1_xboole_0 != sK2 | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.20/0.44    inference(resolution,[],[f24,f30])).
% 0.20/0.44  fof(f30,plain,(
% 0.20/0.44    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) )),
% 0.20/0.44    inference(cnf_transformation,[],[f13])).
% 0.20/0.44  fof(f13,plain,(
% 0.20/0.44    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.44    inference(ennf_transformation,[],[f7])).
% 0.20/0.44  fof(f7,axiom,(
% 0.20/0.44    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.44  fof(f24,plain,(
% 0.20/0.44    ~v2_tops_1(sK1,sK0) | k1_xboole_0 != sK2),
% 0.20/0.44    inference(cnf_transformation,[],[f11])).
% 0.20/0.44  fof(f185,plain,(
% 0.20/0.44    k1_xboole_0 = k1_tops_1(sK0,sK1) | k1_xboole_0 != sK2),
% 0.20/0.44    inference(resolution,[],[f183,f24])).
% 0.20/0.44  fof(f183,plain,(
% 0.20/0.44    v2_tops_1(sK1,sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.44    inference(subsumption_resolution,[],[f182,f77])).
% 0.20/0.44  fof(f77,plain,(
% 0.20/0.44    r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.44    inference(resolution,[],[f43,f26])).
% 0.20/0.45  fof(f43,plain,(
% 0.20/0.45    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(k1_tops_1(sK0,X5),X5)) )),
% 0.20/0.45    inference(resolution,[],[f28,f29])).
% 0.20/0.45  fof(f29,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.45  fof(f182,plain,(
% 0.20/0.45    k1_xboole_0 = k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.45    inference(resolution,[],[f136,f26])).
% 0.20/0.45  fof(f136,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,X0) | v2_tops_1(sK1,sK0) | ~r1_tarski(k1_tops_1(sK0,X0),sK1)) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f134,f51])).
% 0.20/0.45  fof(f51,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_tarski(X0,sK1) | r1_tarski(X0,u1_struct_0(sK0))) )),
% 0.20/0.45    inference(resolution,[],[f50,f37])).
% 0.20/0.45  fof(f37,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(flattening,[],[f19])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.45  fof(f50,plain,(
% 0.20/0.45    r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.45    inference(resolution,[],[f26,f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.45  fof(f134,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,X0),sK1) | k1_xboole_0 = k1_tops_1(sK0,X0) | v2_tops_1(sK1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0))) )),
% 0.20/0.45    inference(resolution,[],[f72,f35])).
% 0.20/0.45  fof(f35,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f3])).
% 0.20/0.45  fof(f72,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,X0),sK1) | k1_xboole_0 = k1_tops_1(sK0,X0) | v2_tops_1(sK1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f71,f28])).
% 0.20/0.45  fof(f71,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,X0),sK1) | ~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,X0) | v2_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f70,f27])).
% 0.20/0.45  fof(f27,plain,(
% 0.20/0.45    v2_pre_topc(sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f70,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,X0),sK1) | ~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,X0) | v2_tops_1(sK1,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.45    inference(resolution,[],[f25,f34])).
% 0.20/0.45  fof(f34,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ( ! [X2] : (~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | v2_tops_1(sK1,sK0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f820,plain,(
% 0.20/0.45    k1_xboole_0 = sK2),
% 0.20/0.45    inference(resolution,[],[f811,f33])).
% 0.20/0.45  fof(f33,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.45  fof(f811,plain,(
% 0.20/0.45    r1_tarski(sK2,k1_xboole_0)),
% 0.20/0.45    inference(forward_demodulation,[],[f810,f195])).
% 0.20/0.45  fof(f195,plain,(
% 0.20/0.45    k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.45    inference(subsumption_resolution,[],[f194,f26])).
% 0.20/0.45  fof(f194,plain,(
% 0.20/0.45    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(subsumption_resolution,[],[f189,f28])).
% 0.20/0.45  fof(f189,plain,(
% 0.20/0.45    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(duplicate_literal_removal,[],[f188])).
% 0.20/0.45  fof(f188,plain,(
% 0.20/0.45    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.45    inference(resolution,[],[f183,f31])).
% 0.20/0.45  fof(f31,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f13])).
% 0.20/0.45  fof(f810,plain,(
% 0.20/0.45    r1_tarski(sK2,k1_tops_1(sK0,sK1))),
% 0.20/0.45    inference(subsumption_resolution,[],[f808,f193])).
% 0.20/0.45  fof(f193,plain,(
% 0.20/0.45    r1_tarski(sK2,sK1)),
% 0.20/0.45    inference(subsumption_resolution,[],[f187,f57])).
% 0.20/0.45  fof(f57,plain,(
% 0.20/0.45    k1_xboole_0 != k1_tops_1(sK0,sK1) | r1_tarski(sK2,sK1)),
% 0.20/0.45    inference(subsumption_resolution,[],[f56,f26])).
% 0.20/0.45  fof(f56,plain,(
% 0.20/0.45    r1_tarski(sK2,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.20/0.45    inference(subsumption_resolution,[],[f55,f28])).
% 0.20/0.45  fof(f55,plain,(
% 0.20/0.45    r1_tarski(sK2,sK1) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.20/0.45    inference(resolution,[],[f22,f30])).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ~v2_tops_1(sK1,sK0) | r1_tarski(sK2,sK1)),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f187,plain,(
% 0.20/0.45    k1_xboole_0 = k1_tops_1(sK0,sK1) | r1_tarski(sK2,sK1)),
% 0.20/0.45    inference(resolution,[],[f183,f22])).
% 0.20/0.45  fof(f808,plain,(
% 0.20/0.45    ~r1_tarski(sK2,sK1) | r1_tarski(sK2,k1_tops_1(sK0,sK1))),
% 0.20/0.45    inference(resolution,[],[f244,f26])).
% 0.20/0.45  fof(f244,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f243,f190])).
% 0.20/0.45  fof(f190,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(subsumption_resolution,[],[f184,f69])).
% 0.20/0.45  fof(f69,plain,(
% 0.20/0.45    k1_xboole_0 != k1_tops_1(sK0,sK1) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(subsumption_resolution,[],[f68,f26])).
% 0.20/0.45  fof(f68,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.20/0.45    inference(subsumption_resolution,[],[f67,f28])).
% 0.20/0.45  fof(f67,plain,(
% 0.20/0.45    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.20/0.45    inference(resolution,[],[f21,f30])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ~v2_tops_1(sK1,sK0) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f184,plain,(
% 0.20/0.45    k1_xboole_0 = k1_tops_1(sK0,sK1) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.45    inference(resolution,[],[f183,f21])).
% 0.20/0.45  fof(f243,plain,(
% 0.20/0.45    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) )),
% 0.20/0.45    inference(subsumption_resolution,[],[f239,f28])).
% 0.20/0.45  fof(f239,plain,(
% 0.20/0.45    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | r1_tarski(sK2,k1_tops_1(sK0,X0))) )),
% 0.20/0.45    inference(resolution,[],[f192,f32])).
% 0.20/0.45  fof(f32,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~r1_tarski(X1,X2) | r1_tarski(X1,k1_tops_1(X0,X2))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(flattening,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.45    inference(ennf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 0.20/0.45  fof(f192,plain,(
% 0.20/0.45    v3_pre_topc(sK2,sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f186,f60])).
% 0.20/0.45  fof(f60,plain,(
% 0.20/0.45    k1_xboole_0 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK2,sK0)),
% 0.20/0.45    inference(subsumption_resolution,[],[f59,f26])).
% 0.20/0.45  fof(f59,plain,(
% 0.20/0.45    v3_pre_topc(sK2,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.20/0.45    inference(subsumption_resolution,[],[f58,f28])).
% 0.20/0.45  fof(f58,plain,(
% 0.20/0.45    v3_pre_topc(sK2,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 != k1_tops_1(sK0,sK1)),
% 0.20/0.45    inference(resolution,[],[f23,f30])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ~v2_tops_1(sK1,sK0) | v3_pre_topc(sK2,sK0)),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f186,plain,(
% 0.20/0.45    k1_xboole_0 = k1_tops_1(sK0,sK1) | v3_pre_topc(sK2,sK0)),
% 0.20/0.45    inference(resolution,[],[f183,f23])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (23375)------------------------------
% 0.20/0.45  % (23375)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (23375)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (23375)Memory used [KB]: 1791
% 0.20/0.45  % (23375)Time elapsed: 0.019 s
% 0.20/0.45  % (23375)------------------------------
% 0.20/0.45  % (23375)------------------------------
% 0.20/0.45  % (23361)Success in time 0.09 s
%------------------------------------------------------------------------------
