%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   79 (2159 expanded)
%              Number of leaves         :    6 ( 394 expanded)
%              Depth                    :   34
%              Number of atoms          :  280 (10227 expanded)
%              Number of equality atoms :   36 (1295 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f602,plain,(
    $false ),
    inference(subsumption_resolution,[],[f601,f23])).

fof(f23,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( v2_compts_1(X2,X0)
                      <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).

fof(f601,plain,(
    ~ m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f600,f550])).

fof(f550,plain,(
    ~ v2_compts_1(sK2,sK1) ),
    inference(subsumption_resolution,[],[f548,f49])).

fof(f49,plain,
    ( ~ v2_compts_1(sK2,sK1)
    | ~ v2_compts_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f19,f21])).

fof(f21,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,
    ( ~ v2_compts_1(sK3,sK1)
    | ~ v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f548,plain,
    ( ~ v2_compts_1(sK2,sK1)
    | v2_compts_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f143,f546])).

fof(f546,plain,(
    sK2 = sK7(sK1,sK2) ),
    inference(subsumption_resolution,[],[f545,f144])).

fof(f144,plain,
    ( v2_compts_1(sK2,sK0)
    | sK2 = sK7(sK1,sK2) ),
    inference(subsumption_resolution,[],[f142,f23])).

fof(f142,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | sK2 = sK7(sK1,sK2)
    | v2_compts_1(sK2,sK0) ),
    inference(resolution,[],[f138,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | sK2 = sK7(X0,sK2)
      | v2_compts_1(sK2,sK0) ) ),
    inference(resolution,[],[f75,f22])).

fof(f22,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X0,sK0)
      | ~ r1_tarski(X1,k2_struct_0(X0))
      | sK7(X0,X1) = X1
      | v2_compts_1(X1,sK0) ) ),
    inference(resolution,[],[f38,f24])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | sK7(X1,X2) = X2
      | v2_compts_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).

fof(f138,plain,(
    r1_tarski(sK2,k2_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f137,f48])).

fof(f48,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f20,f21])).

fof(f20,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f137,plain,
    ( r1_tarski(sK2,k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f136,f53])).

fof(f53,plain,(
    l1_pre_topc(sK1) ),
    inference(resolution,[],[f52,f23])).

fof(f52,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK0)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f35,f24])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f136,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(sK2,k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f124,f60])).

fof(f60,plain,(
    ! [X1] :
      ( m1_pre_topc(k1_pre_topc(sK1,X1),sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f43,f53])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f124,plain,(
    ! [X2] :
      ( ~ m1_pre_topc(k1_pre_topc(sK1,sK2),X2)
      | ~ l1_pre_topc(X2)
      | r1_tarski(sK2,k2_struct_0(X2)) ) ),
    inference(subsumption_resolution,[],[f115,f67])).

fof(f67,plain,(
    l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(resolution,[],[f66,f48])).

fof(f66,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | l1_pre_topc(k1_pre_topc(sK1,X0)) ) ),
    inference(resolution,[],[f60,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,sK1)
      | l1_pre_topc(X0) ) ),
    inference(resolution,[],[f53,f35])).

fof(f115,plain,(
    ! [X2] :
      ( r1_tarski(sK2,k2_struct_0(X2))
      | ~ l1_pre_topc(k1_pre_topc(sK1,sK2))
      | ~ l1_pre_topc(X2)
      | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),X2) ) ),
    inference(superposition,[],[f34,f112])).

fof(f112,plain,(
    sK2 = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f111,f48])).

fof(f111,plain,
    ( sK2 = k2_struct_0(k1_pre_topc(sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f92,f60])).

fof(f92,plain,
    ( ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | sK2 = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f91,f53])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | sK2 = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f88,f48])).

fof(f88,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | sK2 = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(resolution,[],[f46,f58])).

fof(f58,plain,(
    v1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(resolution,[],[f56,f48])).

fof(f56,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v1_pre_topc(k1_pre_topc(sK1,X1)) ) ),
    inference(resolution,[],[f42,f53])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_pre_topc(k1_pre_topc(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | k2_struct_0(k1_pre_topc(X0,X1)) = X1 ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_pre_topc(X2)
      | ~ m1_pre_topc(X2,X0)
      | k2_struct_0(X2) = X1
      | k1_pre_topc(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 )
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_pre_topc(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_pre_topc(X2) )
             => ( k1_pre_topc(X0,X1) = X2
              <=> k2_struct_0(X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f545,plain,
    ( sK2 = sK7(sK1,sK2)
    | ~ v2_compts_1(sK2,sK0) ),
    inference(resolution,[],[f544,f49])).

fof(f544,plain,
    ( v2_compts_1(sK2,sK1)
    | sK2 = sK7(sK1,sK2) ),
    inference(subsumption_resolution,[],[f543,f23])).

fof(f543,plain,
    ( v2_compts_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | sK2 = sK7(sK1,sK2) ),
    inference(subsumption_resolution,[],[f542,f138])).

fof(f542,plain,
    ( ~ r1_tarski(sK2,k2_struct_0(sK1))
    | v2_compts_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | sK2 = sK7(sK1,sK2) ),
    inference(resolution,[],[f540,f48])).

fof(f540,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ r1_tarski(sK2,k2_struct_0(X2))
      | v2_compts_1(sK2,X2)
      | ~ m1_pre_topc(X2,sK0)
      | sK2 = sK7(sK1,sK2) ) ),
    inference(resolution,[],[f532,f144])).

fof(f532,plain,(
    ! [X0] :
      ( ~ v2_compts_1(sK2,sK0)
      | ~ r1_tarski(sK2,k2_struct_0(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(sK2,X0)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f515,f22])).

fof(f515,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X0,sK0)
      | ~ r1_tarski(X1,k2_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_compts_1(X1,X0)
      | ~ v2_compts_1(X1,sK0) ) ),
    inference(resolution,[],[f45,f24])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X3,k2_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_compts_1(X3,X1)
      | ~ v2_compts_1(X3,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | X2 != X3
      | v2_compts_1(X3,X1)
      | ~ v2_compts_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f143,plain,
    ( ~ v2_compts_1(sK7(sK1,sK2),sK1)
    | v2_compts_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f140,f23])).

fof(f140,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v2_compts_1(sK7(sK1,sK2),sK1)
    | v2_compts_1(sK2,sK0) ),
    inference(resolution,[],[f138,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK2,k2_struct_0(X0))
      | ~ m1_pre_topc(X0,sK0)
      | ~ v2_compts_1(sK7(X0,sK2),X0)
      | v2_compts_1(sK2,sK0) ) ),
    inference(resolution,[],[f81,f22])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_pre_topc(X0,sK0)
      | ~ r1_tarski(X1,k2_struct_0(X0))
      | ~ v2_compts_1(sK7(X0,X1),X0)
      | v2_compts_1(X1,sK0) ) ),
    inference(resolution,[],[f39,f24])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ v2_compts_1(sK7(X1,X2),X1)
      | v2_compts_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f600,plain,
    ( v2_compts_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f599,f138])).

fof(f599,plain,
    ( ~ r1_tarski(sK2,k2_struct_0(sK1))
    | v2_compts_1(sK2,sK1)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f562,f48])).

fof(f562,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(sK2,k2_struct_0(X0))
      | v2_compts_1(sK2,X0)
      | ~ m1_pre_topc(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f532,f551])).

fof(f551,plain,(
    v2_compts_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f50,f550])).

fof(f50,plain,
    ( v2_compts_1(sK2,sK1)
    | v2_compts_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f18,f21])).

fof(f18,plain,
    ( v2_compts_1(sK3,sK1)
    | v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:05:38 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.46  % (16599)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.46  % (16599)Refutation not found, incomplete strategy% (16599)------------------------------
% 0.20/0.46  % (16599)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (16599)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (16599)Memory used [KB]: 10618
% 0.20/0.46  % (16599)Time elapsed: 0.055 s
% 0.20/0.46  % (16599)------------------------------
% 0.20/0.46  % (16599)------------------------------
% 0.20/0.46  % (16607)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.49  % (16600)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (16607)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f602,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f601,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v2_compts_1(X2,X0) <~> v2_compts_1(X3,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v2_compts_1(X2,X0) <~> v2_compts_1(X3,X1)) & X2 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f6])).
% 0.20/0.49  fof(f6,conjecture,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_compts_1)).
% 0.20/0.49  fof(f601,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f600,f550])).
% 0.20/0.49  fof(f550,plain,(
% 0.20/0.49    ~v2_compts_1(sK2,sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f548,f49])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ~v2_compts_1(sK2,sK1) | ~v2_compts_1(sK2,sK0)),
% 0.20/0.49    inference(forward_demodulation,[],[f19,f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    sK2 = sK3),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ~v2_compts_1(sK3,sK1) | ~v2_compts_1(sK2,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f548,plain,(
% 0.20/0.49    ~v2_compts_1(sK2,sK1) | v2_compts_1(sK2,sK0)),
% 0.20/0.49    inference(backward_demodulation,[],[f143,f546])).
% 0.20/0.49  fof(f546,plain,(
% 0.20/0.49    sK2 = sK7(sK1,sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f545,f144])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    v2_compts_1(sK2,sK0) | sK2 = sK7(sK1,sK2)),
% 0.20/0.49    inference(subsumption_resolution,[],[f142,f23])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ~m1_pre_topc(sK1,sK0) | sK2 = sK7(sK1,sK2) | v2_compts_1(sK2,sK0)),
% 0.20/0.49    inference(resolution,[],[f138,f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(sK2,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | sK2 = sK7(X0,sK2) | v2_compts_1(sK2,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f75,f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X0,sK0) | ~r1_tarski(X1,k2_struct_0(X0)) | sK7(X0,X1) = X1 | v2_compts_1(X1,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f38,f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | sK7(X1,X2) = X2 | v2_compts_1(X2,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_compts_1)).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    r1_tarski(sK2,k2_struct_0(sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f137,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.49    inference(forward_demodulation,[],[f20,f21])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    r1_tarski(sK2,k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.49    inference(subsumption_resolution,[],[f136,f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    l1_pre_topc(sK1)),
% 0.20/0.49    inference(resolution,[],[f52,f23])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_pre_topc(X0,sK0) | l1_pre_topc(X0)) )),
% 0.20/0.49    inference(resolution,[],[f35,f24])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ~l1_pre_topc(sK1) | r1_tarski(sK2,k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.49    inference(resolution,[],[f124,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X1] : (m1_pre_topc(k1_pre_topc(sK1,X1),sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.49    inference(resolution,[],[f43,f53])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : ((m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    ( ! [X2] : (~m1_pre_topc(k1_pre_topc(sK1,sK2),X2) | ~l1_pre_topc(X2) | r1_tarski(sK2,k2_struct_0(X2))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f115,f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    l1_pre_topc(k1_pre_topc(sK1,sK2))),
% 0.20/0.50    inference(resolution,[],[f66,f48])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | l1_pre_topc(k1_pre_topc(sK1,X0))) )),
% 0.20/0.50    inference(resolution,[],[f60,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_pre_topc(X0,sK1) | l1_pre_topc(X0)) )),
% 0.20/0.50    inference(resolution,[],[f53,f35])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    ( ! [X2] : (r1_tarski(sK2,k2_struct_0(X2)) | ~l1_pre_topc(k1_pre_topc(sK1,sK2)) | ~l1_pre_topc(X2) | ~m1_pre_topc(k1_pre_topc(sK1,sK2),X2)) )),
% 0.20/0.50    inference(superposition,[],[f34,f112])).
% 0.20/0.50  fof(f112,plain,(
% 0.20/0.50    sK2 = k2_struct_0(k1_pre_topc(sK1,sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f111,f48])).
% 0.20/0.50  fof(f111,plain,(
% 0.20/0.50    sK2 = k2_struct_0(k1_pre_topc(sK1,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.50    inference(resolution,[],[f92,f60])).
% 0.20/0.50  fof(f92,plain,(
% 0.20/0.50    ~m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) | sK2 = k2_struct_0(k1_pre_topc(sK1,sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f91,f53])).
% 0.20/0.50  fof(f91,plain,(
% 0.20/0.50    ~l1_pre_topc(sK1) | ~m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) | sK2 = k2_struct_0(k1_pre_topc(sK1,sK2))),
% 0.20/0.50    inference(subsumption_resolution,[],[f88,f48])).
% 0.20/0.50  fof(f88,plain,(
% 0.20/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) | sK2 = k2_struct_0(k1_pre_topc(sK1,sK2))),
% 0.20/0.50    inference(resolution,[],[f46,f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    v1_pre_topc(k1_pre_topc(sK1,sK2))),
% 0.20/0.50    inference(resolution,[],[f56,f48])).
% 0.20/0.50  fof(f56,plain,(
% 0.20/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v1_pre_topc(k1_pre_topc(sK1,X1))) )),
% 0.20/0.50    inference(resolution,[],[f42,f53])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k1_pre_topc(X0,X1))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f17])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~v1_pre_topc(k1_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(k1_pre_topc(X0,X1),X0) | k2_struct_0(k1_pre_topc(X0,X1)) = X1) )),
% 0.20/0.50    inference(equality_resolution,[],[f41])).
% 0.20/0.50  fof(f41,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_pre_topc(X2) | ~m1_pre_topc(X2,X0) | k2_struct_0(X2) = X1 | k1_pre_topc(X0,X1) != X2) )),
% 0.20/0.50    inference(cnf_transformation,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | ~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(flattening,[],[f14])).
% 0.20/0.50  fof(f14,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1) | (~m1_pre_topc(X2,X0) | ~v1_pre_topc(X2))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f1])).
% 0.20/0.50  fof(f1,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : ((m1_pre_topc(X2,X0) & v1_pre_topc(X2)) => (k1_pre_topc(X0,X1) = X2 <=> k2_struct_0(X2) = X1))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_pre_topc)).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f10])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.20/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.20/0.50  fof(f545,plain,(
% 0.20/0.50    sK2 = sK7(sK1,sK2) | ~v2_compts_1(sK2,sK0)),
% 0.20/0.50    inference(resolution,[],[f544,f49])).
% 0.20/0.50  fof(f544,plain,(
% 0.20/0.50    v2_compts_1(sK2,sK1) | sK2 = sK7(sK1,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f543,f23])).
% 0.20/0.50  fof(f543,plain,(
% 0.20/0.50    v2_compts_1(sK2,sK1) | ~m1_pre_topc(sK1,sK0) | sK2 = sK7(sK1,sK2)),
% 0.20/0.50    inference(subsumption_resolution,[],[f542,f138])).
% 0.20/0.50  fof(f542,plain,(
% 0.20/0.50    ~r1_tarski(sK2,k2_struct_0(sK1)) | v2_compts_1(sK2,sK1) | ~m1_pre_topc(sK1,sK0) | sK2 = sK7(sK1,sK2)),
% 0.20/0.50    inference(resolution,[],[f540,f48])).
% 0.20/0.50  fof(f540,plain,(
% 0.20/0.50    ( ! [X2] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X2))) | ~r1_tarski(sK2,k2_struct_0(X2)) | v2_compts_1(sK2,X2) | ~m1_pre_topc(X2,sK0) | sK2 = sK7(sK1,sK2)) )),
% 0.20/0.50    inference(resolution,[],[f532,f144])).
% 0.20/0.50  fof(f532,plain,(
% 0.20/0.50    ( ! [X0] : (~v2_compts_1(sK2,sK0) | ~r1_tarski(sK2,k2_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(sK2,X0) | ~m1_pre_topc(X0,sK0)) )),
% 0.20/0.50    inference(resolution,[],[f515,f22])).
% 0.20/0.50  fof(f515,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X0,sK0) | ~r1_tarski(X1,k2_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_compts_1(X1,X0) | ~v2_compts_1(X1,sK0)) )),
% 0.20/0.50    inference(resolution,[],[f45,f24])).
% 0.20/0.50  fof(f45,plain,(
% 0.20/0.50    ( ! [X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X3,k2_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | v2_compts_1(X3,X1) | ~v2_compts_1(X3,X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f36])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | X2 != X3 | v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    ~v2_compts_1(sK7(sK1,sK2),sK1) | v2_compts_1(sK2,sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f140,f23])).
% 0.20/0.50  fof(f140,plain,(
% 0.20/0.50    ~m1_pre_topc(sK1,sK0) | ~v2_compts_1(sK7(sK1,sK2),sK1) | v2_compts_1(sK2,sK0)),
% 0.20/0.50    inference(resolution,[],[f138,f85])).
% 0.20/0.50  fof(f85,plain,(
% 0.20/0.50    ( ! [X0] : (~r1_tarski(sK2,k2_struct_0(X0)) | ~m1_pre_topc(X0,sK0) | ~v2_compts_1(sK7(X0,sK2),X0) | v2_compts_1(sK2,sK0)) )),
% 0.20/0.50    inference(resolution,[],[f81,f22])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_pre_topc(X0,sK0) | ~r1_tarski(X1,k2_struct_0(X0)) | ~v2_compts_1(sK7(X0,X1),X0) | v2_compts_1(X1,sK0)) )),
% 0.20/0.50    inference(resolution,[],[f39,f24])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~v2_compts_1(sK7(X1,X2),X1) | v2_compts_1(X2,X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f13])).
% 0.20/0.50  fof(f600,plain,(
% 0.20/0.50    v2_compts_1(sK2,sK1) | ~m1_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f599,f138])).
% 0.20/0.50  fof(f599,plain,(
% 0.20/0.50    ~r1_tarski(sK2,k2_struct_0(sK1)) | v2_compts_1(sK2,sK1) | ~m1_pre_topc(sK1,sK0)),
% 0.20/0.50    inference(resolution,[],[f562,f48])).
% 0.20/0.50  fof(f562,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(sK2,k2_struct_0(X0)) | v2_compts_1(sK2,X0) | ~m1_pre_topc(X0,sK0)) )),
% 0.20/0.50    inference(subsumption_resolution,[],[f532,f551])).
% 0.20/0.50  fof(f551,plain,(
% 0.20/0.50    v2_compts_1(sK2,sK0)),
% 0.20/0.50    inference(subsumption_resolution,[],[f50,f550])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    v2_compts_1(sK2,sK1) | v2_compts_1(sK2,sK0)),
% 0.20/0.50    inference(forward_demodulation,[],[f18,f21])).
% 0.20/0.50  fof(f18,plain,(
% 0.20/0.50    v2_compts_1(sK3,sK1) | v2_compts_1(sK2,sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f9])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (16607)------------------------------
% 0.20/0.50  % (16607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (16607)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (16607)Memory used [KB]: 2558
% 0.20/0.50  % (16607)Time elapsed: 0.097 s
% 0.20/0.50  % (16607)------------------------------
% 0.20/0.50  % (16607)------------------------------
% 0.20/0.50  % (16587)Success in time 0.141 s
%------------------------------------------------------------------------------
