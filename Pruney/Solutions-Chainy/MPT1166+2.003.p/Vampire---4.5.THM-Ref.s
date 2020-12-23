%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:11 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.14s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 717 expanded)
%              Number of leaves         :    6 ( 126 expanded)
%              Depth                    :   34
%              Number of atoms          :  440 (5238 expanded)
%              Number of equality atoms :   62 ( 508 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f195,plain,(
    $false ),
    inference(subsumption_resolution,[],[f194,f142])).

fof(f142,plain,(
    m1_orders_2(sK1,sK0,sK1) ),
    inference(backward_demodulation,[],[f19,f140])).

fof(f140,plain,(
    sK1 = sK2 ),
    inference(subsumption_resolution,[],[f139,f109])).

fof(f109,plain,(
    ~ r2_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f108,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f108,plain,(
    r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f107,f17])).

fof(f17,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( m1_orders_2(X2,X0,X1)
                    & m1_orders_2(X1,X0,X2)
                    & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

fof(f107,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f106,f26])).

fof(f26,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f106,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f105,f25])).

fof(f25,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f105,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f104,f24])).

fof(f24,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f104,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f103,f23])).

fof(f23,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f103,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f88,f22])).

fof(f22,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f88,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f19,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f139,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f137,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f137,plain,(
    r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f136,f21])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f136,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f135,f26])).

fof(f135,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f134,f25])).

fof(f134,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f133,f24])).

fof(f133,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f132,f23])).

fof(f132,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f115,f22])).

fof(f115,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK2,sK1) ),
    inference(resolution,[],[f20,f28])).

fof(f20,plain,(
    m1_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f19,plain,(
    m1_orders_2(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f9])).

fof(f194,plain,(
    ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(subsumption_resolution,[],[f193,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f9])).

fof(f193,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(subsumption_resolution,[],[f192,f21])).

fof(f192,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(subsumption_resolution,[],[f191,f26])).

fof(f191,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(subsumption_resolution,[],[f190,f25])).

fof(f190,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(subsumption_resolution,[],[f189,f24])).

fof(f189,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(subsumption_resolution,[],[f188,f23])).

fof(f188,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(subsumption_resolution,[],[f187,f22])).

fof(f187,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f186])).

fof(f186,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK1
    | ~ m1_orders_2(sK1,sK0,sK1) ),
    inference(resolution,[],[f185,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

fof(f185,plain,(
    ~ r2_hidden(sK3(sK0,sK1,sK1),sK1) ),
    inference(subsumption_resolution,[],[f184,f21])).

fof(f184,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f183,f153])).

fof(f153,plain,(
    m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f152,f140])).

fof(f152,plain,(
    m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f144,f18])).

fof(f144,plain,
    ( k1_xboole_0 = sK1
    | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f95,f140])).

fof(f95,plain,
    ( k1_xboole_0 = sK2
    | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f94,f21])).

fof(f94,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f93,f17])).

fof(f93,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f92,f26])).

fof(f92,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f91,f25])).

fof(f91,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f90,f24])).

fof(f90,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f89,f23])).

fof(f89,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f85,f22])).

fof(f85,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f19,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f183,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | ~ m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f182,f26])).

fof(f182,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f181,f25])).

fof(f181,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f180,f24])).

fof(f180,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f179,f23])).

fof(f179,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f178,f22])).

fof(f178,plain,
    ( ~ r2_hidden(sK3(sK0,sK1,sK1),sK1)
    | v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(superposition,[],[f27,f155])).

fof(f155,plain,(
    sK1 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK1)) ),
    inference(forward_demodulation,[],[f154,f140])).

fof(f154,plain,(
    sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f145,f18])).

fof(f145,plain,
    ( k1_xboole_0 = sK1
    | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f102,f140])).

fof(f102,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f101,f21])).

fof(f101,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f100,f17])).

fof(f100,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f99,f26])).

fof(f99,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f98,f25])).

fof(f98,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f97,f24])).

fof(f97,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f96,f23])).

fof(f96,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) ),
    inference(subsumption_resolution,[],[f87,f22])).

fof(f87,plain,
    ( v2_struct_0(sK0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = sK2
    | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) ),
    inference(resolution,[],[f19,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X1
      | k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,k3_orders_2(X0,X2,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k3_orders_2(X0,X2,X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ r2_hidden(X1,k3_orders_2(X0,X2,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.09  % Command    : run_vampire %s %d
% 0.08/0.29  % Computer   : n021.cluster.edu
% 0.08/0.29  % Model      : x86_64 x86_64
% 0.08/0.29  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.08/0.29  % Memory     : 8042.1875MB
% 0.08/0.29  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.08/0.29  % CPULimit   : 60
% 0.08/0.29  % WCLimit    : 600
% 0.08/0.29  % DateTime   : Tue Dec  1 11:31:49 EST 2020
% 0.08/0.29  % CPUTime    : 
% 0.14/0.41  % (18230)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.14/0.41  % (18219)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.14/0.41  % (18230)Refutation found. Thanks to Tanya!
% 0.14/0.41  % SZS status Theorem for theBenchmark
% 0.14/0.41  % SZS output start Proof for theBenchmark
% 0.14/0.41  fof(f195,plain,(
% 0.14/0.41    $false),
% 0.14/0.41    inference(subsumption_resolution,[],[f194,f142])).
% 0.14/0.41  fof(f142,plain,(
% 0.14/0.41    m1_orders_2(sK1,sK0,sK1)),
% 0.14/0.41    inference(backward_demodulation,[],[f19,f140])).
% 0.14/0.41  fof(f140,plain,(
% 0.14/0.41    sK1 = sK2),
% 0.14/0.41    inference(subsumption_resolution,[],[f139,f109])).
% 0.14/0.41  fof(f109,plain,(
% 0.14/0.41    ~r2_xboole_0(sK2,sK1)),
% 0.14/0.41    inference(resolution,[],[f108,f38])).
% 0.14/0.41  fof(f38,plain,(
% 0.14/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f16])).
% 0.14/0.41  fof(f16,plain,(
% 0.14/0.41    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.14/0.41    inference(ennf_transformation,[],[f2])).
% 0.14/0.41  fof(f2,axiom,(
% 0.14/0.41    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.14/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.14/0.41  fof(f108,plain,(
% 0.14/0.41    r1_tarski(sK1,sK2)),
% 0.14/0.41    inference(subsumption_resolution,[],[f107,f17])).
% 0.14/0.41  fof(f17,plain,(
% 0.14/0.41    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.14/0.41    inference(cnf_transformation,[],[f9])).
% 0.14/0.41  fof(f9,plain,(
% 0.14/0.41    ? [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.14/0.41    inference(flattening,[],[f8])).
% 0.14/0.41  fof(f8,plain,(
% 0.14/0.41    ? [X0] : (? [X1] : (? [X2] : ((m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.14/0.41    inference(ennf_transformation,[],[f7])).
% 0.14/0.41  fof(f7,negated_conjecture,(
% 0.14/0.41    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.14/0.41    inference(negated_conjecture,[],[f6])).
% 0.14/0.41  fof(f6,conjecture,(
% 0.14/0.41    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.14/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).
% 0.14/0.41  fof(f107,plain,(
% 0.14/0.41    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,sK2)),
% 0.14/0.41    inference(subsumption_resolution,[],[f106,f26])).
% 0.14/0.41  fof(f26,plain,(
% 0.14/0.41    l1_orders_2(sK0)),
% 0.14/0.41    inference(cnf_transformation,[],[f9])).
% 0.14/0.41  fof(f106,plain,(
% 0.14/0.41    ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,sK2)),
% 0.14/0.41    inference(subsumption_resolution,[],[f105,f25])).
% 0.14/0.41  fof(f25,plain,(
% 0.14/0.41    v5_orders_2(sK0)),
% 0.14/0.41    inference(cnf_transformation,[],[f9])).
% 0.14/0.41  fof(f105,plain,(
% 0.14/0.41    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,sK2)),
% 0.14/0.41    inference(subsumption_resolution,[],[f104,f24])).
% 0.14/0.41  fof(f24,plain,(
% 0.14/0.41    v4_orders_2(sK0)),
% 0.14/0.41    inference(cnf_transformation,[],[f9])).
% 0.14/0.41  fof(f104,plain,(
% 0.14/0.41    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,sK2)),
% 0.14/0.41    inference(subsumption_resolution,[],[f103,f23])).
% 0.14/0.41  fof(f23,plain,(
% 0.14/0.41    v3_orders_2(sK0)),
% 0.14/0.41    inference(cnf_transformation,[],[f9])).
% 0.14/0.41  fof(f103,plain,(
% 0.14/0.41    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,sK2)),
% 0.14/0.41    inference(subsumption_resolution,[],[f88,f22])).
% 0.14/0.41  fof(f22,plain,(
% 0.14/0.41    ~v2_struct_0(sK0)),
% 0.14/0.41    inference(cnf_transformation,[],[f9])).
% 0.14/0.41  fof(f88,plain,(
% 0.14/0.41    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,sK2)),
% 0.14/0.41    inference(resolution,[],[f19,f28])).
% 0.14/0.41  fof(f28,plain,(
% 0.14/0.41    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f13])).
% 0.14/0.41  fof(f13,plain,(
% 0.14/0.41    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.14/0.41    inference(flattening,[],[f12])).
% 0.14/0.41  fof(f12,plain,(
% 0.14/0.41    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.14/0.41    inference(ennf_transformation,[],[f5])).
% 0.14/0.41  fof(f5,axiom,(
% 0.14/0.41    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.14/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).
% 0.14/0.41  fof(f139,plain,(
% 0.14/0.41    sK1 = sK2 | r2_xboole_0(sK2,sK1)),
% 0.14/0.41    inference(resolution,[],[f137,f37])).
% 0.14/0.41  fof(f37,plain,(
% 0.14/0.41    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f1])).
% 0.14/0.41  fof(f1,axiom,(
% 0.14/0.41    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.14/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.14/0.41  fof(f137,plain,(
% 0.14/0.41    r1_tarski(sK2,sK1)),
% 0.14/0.41    inference(subsumption_resolution,[],[f136,f21])).
% 0.14/0.41  fof(f21,plain,(
% 0.14/0.41    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.14/0.41    inference(cnf_transformation,[],[f9])).
% 0.14/0.41  fof(f136,plain,(
% 0.14/0.41    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK1)),
% 0.14/0.41    inference(subsumption_resolution,[],[f135,f26])).
% 0.14/0.41  fof(f135,plain,(
% 0.14/0.41    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK1)),
% 0.14/0.41    inference(subsumption_resolution,[],[f134,f25])).
% 0.14/0.41  fof(f134,plain,(
% 0.14/0.41    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK1)),
% 0.14/0.41    inference(subsumption_resolution,[],[f133,f24])).
% 0.14/0.41  fof(f133,plain,(
% 0.14/0.41    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK1)),
% 0.14/0.41    inference(subsumption_resolution,[],[f132,f23])).
% 0.14/0.41  fof(f132,plain,(
% 0.14/0.41    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK1)),
% 0.14/0.41    inference(subsumption_resolution,[],[f115,f22])).
% 0.14/0.41  fof(f115,plain,(
% 0.14/0.41    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK2,sK1)),
% 0.14/0.41    inference(resolution,[],[f20,f28])).
% 0.14/0.41  fof(f20,plain,(
% 0.14/0.41    m1_orders_2(sK2,sK0,sK1)),
% 0.14/0.41    inference(cnf_transformation,[],[f9])).
% 0.14/0.41  fof(f19,plain,(
% 0.14/0.41    m1_orders_2(sK1,sK0,sK2)),
% 0.14/0.41    inference(cnf_transformation,[],[f9])).
% 0.14/0.41  fof(f194,plain,(
% 0.14/0.41    ~m1_orders_2(sK1,sK0,sK1)),
% 0.14/0.41    inference(subsumption_resolution,[],[f193,f18])).
% 0.14/0.41  fof(f18,plain,(
% 0.14/0.41    k1_xboole_0 != sK1),
% 0.14/0.41    inference(cnf_transformation,[],[f9])).
% 0.14/0.41  fof(f193,plain,(
% 0.14/0.41    k1_xboole_0 = sK1 | ~m1_orders_2(sK1,sK0,sK1)),
% 0.14/0.41    inference(subsumption_resolution,[],[f192,f21])).
% 0.14/0.41  fof(f192,plain,(
% 0.14/0.41    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | ~m1_orders_2(sK1,sK0,sK1)),
% 0.14/0.41    inference(subsumption_resolution,[],[f191,f26])).
% 0.14/0.41  fof(f191,plain,(
% 0.14/0.41    ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | ~m1_orders_2(sK1,sK0,sK1)),
% 0.14/0.41    inference(subsumption_resolution,[],[f190,f25])).
% 0.14/0.41  fof(f190,plain,(
% 0.14/0.41    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | ~m1_orders_2(sK1,sK0,sK1)),
% 0.14/0.41    inference(subsumption_resolution,[],[f189,f24])).
% 0.14/0.41  fof(f189,plain,(
% 0.14/0.41    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | ~m1_orders_2(sK1,sK0,sK1)),
% 0.14/0.41    inference(subsumption_resolution,[],[f188,f23])).
% 0.14/0.41  fof(f188,plain,(
% 0.14/0.41    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | ~m1_orders_2(sK1,sK0,sK1)),
% 0.14/0.41    inference(subsumption_resolution,[],[f187,f22])).
% 0.14/0.41  fof(f187,plain,(
% 0.14/0.41    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | ~m1_orders_2(sK1,sK0,sK1)),
% 0.14/0.41    inference(duplicate_literal_removal,[],[f186])).
% 0.14/0.41  fof(f186,plain,(
% 0.14/0.41    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1 | ~m1_orders_2(sK1,sK0,sK1)),
% 0.14/0.41    inference(resolution,[],[f185,f30])).
% 0.14/0.41  fof(f30,plain,(
% 0.14/0.41    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | r2_hidden(sK3(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f15])).
% 0.14/0.41  fof(f15,plain,(
% 0.14/0.41    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.14/0.41    inference(flattening,[],[f14])).
% 0.14/0.41  fof(f14,plain,(
% 0.14/0.41    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.14/0.41    inference(ennf_transformation,[],[f3])).
% 0.14/0.41  fof(f3,axiom,(
% 0.14/0.41    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.14/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).
% 0.14/0.41  fof(f185,plain,(
% 0.14/0.41    ~r2_hidden(sK3(sK0,sK1,sK1),sK1)),
% 0.14/0.41    inference(subsumption_resolution,[],[f184,f21])).
% 0.14/0.41  fof(f184,plain,(
% 0.14/0.41    ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.14/0.41    inference(subsumption_resolution,[],[f183,f153])).
% 0.14/0.41  fof(f153,plain,(
% 0.14/0.41    m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0))),
% 0.14/0.41    inference(forward_demodulation,[],[f152,f140])).
% 0.14/0.41  fof(f152,plain,(
% 0.14/0.41    m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.14/0.41    inference(subsumption_resolution,[],[f144,f18])).
% 0.14/0.41  fof(f144,plain,(
% 0.14/0.41    k1_xboole_0 = sK1 | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.14/0.41    inference(backward_demodulation,[],[f95,f140])).
% 0.14/0.41  fof(f95,plain,(
% 0.14/0.41    k1_xboole_0 = sK2 | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.14/0.41    inference(subsumption_resolution,[],[f94,f21])).
% 0.14/0.41  fof(f94,plain,(
% 0.14/0.41    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.14/0.41    inference(subsumption_resolution,[],[f93,f17])).
% 0.14/0.41  fof(f93,plain,(
% 0.14/0.41    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.14/0.41    inference(subsumption_resolution,[],[f92,f26])).
% 0.14/0.41  fof(f92,plain,(
% 0.14/0.41    ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.14/0.41    inference(subsumption_resolution,[],[f91,f25])).
% 0.14/0.41  fof(f91,plain,(
% 0.14/0.41    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.14/0.41    inference(subsumption_resolution,[],[f90,f24])).
% 0.14/0.41  fof(f90,plain,(
% 0.14/0.41    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.14/0.41    inference(subsumption_resolution,[],[f89,f23])).
% 0.14/0.41  fof(f89,plain,(
% 0.14/0.41    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.14/0.41    inference(subsumption_resolution,[],[f85,f22])).
% 0.14/0.41  fof(f85,plain,(
% 0.14/0.41    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.14/0.41    inference(resolution,[],[f19,f29])).
% 0.14/0.41  fof(f29,plain,(
% 0.14/0.41    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~m1_orders_2(X2,X0,X1)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f15])).
% 0.14/0.41  fof(f183,plain,(
% 0.14/0.41    ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | ~m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.14/0.41    inference(subsumption_resolution,[],[f182,f26])).
% 0.14/0.41  fof(f182,plain,(
% 0.14/0.41    ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.14/0.41    inference(subsumption_resolution,[],[f181,f25])).
% 0.14/0.41  fof(f181,plain,(
% 0.14/0.41    ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.14/0.41    inference(subsumption_resolution,[],[f180,f24])).
% 0.14/0.41  fof(f180,plain,(
% 0.14/0.41    ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.14/0.41    inference(subsumption_resolution,[],[f179,f23])).
% 0.14/0.41  fof(f179,plain,(
% 0.14/0.41    ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.14/0.41    inference(subsumption_resolution,[],[f178,f22])).
% 0.14/0.41  fof(f178,plain,(
% 0.14/0.41    ~r2_hidden(sK3(sK0,sK1,sK1),sK1) | v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK3(sK0,sK1,sK1),u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.14/0.41    inference(superposition,[],[f27,f155])).
% 0.14/0.41  fof(f155,plain,(
% 0.14/0.41    sK1 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK1))),
% 0.14/0.41    inference(forward_demodulation,[],[f154,f140])).
% 0.14/0.41  fof(f154,plain,(
% 0.14/0.41    sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))),
% 0.14/0.41    inference(subsumption_resolution,[],[f145,f18])).
% 0.14/0.41  fof(f145,plain,(
% 0.14/0.41    k1_xboole_0 = sK1 | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))),
% 0.14/0.41    inference(backward_demodulation,[],[f102,f140])).
% 0.14/0.41  fof(f102,plain,(
% 0.14/0.41    k1_xboole_0 = sK2 | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))),
% 0.14/0.41    inference(subsumption_resolution,[],[f101,f21])).
% 0.14/0.41  fof(f101,plain,(
% 0.14/0.41    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))),
% 0.14/0.41    inference(subsumption_resolution,[],[f100,f17])).
% 0.14/0.41  fof(f100,plain,(
% 0.14/0.41    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))),
% 0.14/0.41    inference(subsumption_resolution,[],[f99,f26])).
% 0.14/0.41  fof(f99,plain,(
% 0.14/0.41    ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))),
% 0.14/0.41    inference(subsumption_resolution,[],[f98,f25])).
% 0.14/0.41  fof(f98,plain,(
% 0.14/0.41    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))),
% 0.14/0.41    inference(subsumption_resolution,[],[f97,f24])).
% 0.14/0.41  fof(f97,plain,(
% 0.14/0.41    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))),
% 0.14/0.41    inference(subsumption_resolution,[],[f96,f23])).
% 0.14/0.41  fof(f96,plain,(
% 0.14/0.41    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))),
% 0.14/0.41    inference(subsumption_resolution,[],[f87,f22])).
% 0.14/0.41  fof(f87,plain,(
% 0.14/0.41    v2_struct_0(sK0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2 | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))),
% 0.14/0.41    inference(resolution,[],[f19,f31])).
% 0.14/0.41  fof(f31,plain,(
% 0.14/0.41    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X1 | k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1)) )),
% 0.14/0.41    inference(cnf_transformation,[],[f15])).
% 0.14/0.41  fof(f27,plain,(
% 0.14/0.41    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,k3_orders_2(X0,X2,X1))) )),
% 0.14/0.41    inference(cnf_transformation,[],[f11])).
% 0.14/0.41  fof(f11,plain,(
% 0.14/0.41    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k3_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.14/0.41    inference(flattening,[],[f10])).
% 0.14/0.41  fof(f10,plain,(
% 0.14/0.41    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k3_orders_2(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.14/0.41    inference(ennf_transformation,[],[f4])).
% 0.14/0.41  fof(f4,axiom,(
% 0.14/0.41    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~r2_hidden(X1,k3_orders_2(X0,X2,X1)))))),
% 0.14/0.41    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_orders_2)).
% 0.14/0.41  % SZS output end Proof for theBenchmark
% 0.14/0.41  % (18230)------------------------------
% 0.14/0.41  % (18230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.14/0.41  % (18230)Termination reason: Refutation
% 0.14/0.41  
% 0.14/0.41  % (18230)Memory used [KB]: 1663
% 0.14/0.41  % (18230)Time elapsed: 0.062 s
% 0.14/0.41  % (18230)------------------------------
% 0.14/0.41  % (18230)------------------------------
% 0.14/0.41  % (18216)Success in time 0.106 s
%------------------------------------------------------------------------------
