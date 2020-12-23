%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 399 expanded)
%              Number of leaves         :    4 (  68 expanded)
%              Depth                    :   20
%              Number of atoms          :  277 (2767 expanded)
%              Number of equality atoms :   22 (  70 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f129,plain,(
    $false ),
    inference(subsumption_resolution,[],[f128,f15])).

fof(f15,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k1_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( r2_hidden(X1,k1_orders_2(X0,X2))
              & r2_hidden(X1,X2)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                    & r2_hidden(X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
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
             => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).

fof(f128,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(subsumption_resolution,[],[f127,f17])).

fof(f17,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f127,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,sK2) ),
    inference(resolution,[],[f125,f120])).

fof(f120,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK2) ) ),
    inference(forward_demodulation,[],[f119,f50])).

fof(f50,plain,(
    sK1 = sK3(sK1,sK0,sK2) ),
    inference(resolution,[],[f49,f16])).

fof(f16,plain,(
    r2_hidden(sK1,k1_orders_2(sK0,sK2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,sK2))
      | sK3(X0,sK0,sK2) = X0 ) ),
    inference(forward_demodulation,[],[f48,f42])).

fof(f42,plain,(
    k1_orders_2(sK0,sK2) = a_2_0_orders_2(sK0,sK2) ),
    inference(resolution,[],[f41,f14])).

fof(f14,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f7])).

fof(f41,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f40,f18])).

fof(f18,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f40,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f39,f21])).

fof(f21,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f38,f20])).

fof(f20,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(subsumption_resolution,[],[f37,f19])).

fof(f19,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0) ) ),
    inference(resolution,[],[f23,f22])).

fof(f22,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f7])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

fof(f48,plain,(
    ! [X0] :
      ( sK3(X0,sK0,sK2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,sK2)) ) ),
    inference(resolution,[],[f47,f14])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f46,f18])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f45,f21])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f44,f20])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f43,f19])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(X1,sK0,X0) = X1
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f30,f22])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK3(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK2)
      | r2_orders_2(sK0,X0,sK3(sK1,sK0,sK2)) ) ),
    inference(resolution,[],[f118,f16])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_orders_2(sK0,sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK2)
      | r2_orders_2(sK0,X0,sK3(X1,sK0,sK2)) ) ),
    inference(forward_demodulation,[],[f117,f42])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK2)
      | r2_orders_2(sK0,X0,sK3(X1,sK0,sK2))
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,sK2)) ) ),
    inference(resolution,[],[f116,f14])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK3(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f115,f18])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK3(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f114,f21])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK3(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f113,f20])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK3(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f112,f19])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK3(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f28,f22])).

fof(f28,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(X4,X2)
      | r2_orders_2(X1,X4,sK3(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f125,plain,(
    ~ r2_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f124,f15])).

fof(f124,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ r2_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f123,f17])).

fof(f123,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_orders_2(sK0,sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,sK2)
    | ~ r2_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f120,f36])).

fof(f36,plain,(
    ! [X0] :
      ( ~ r2_orders_2(sK0,sK1,X0)
      | ~ r2_orders_2(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f35,f17])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X0,X1)
      | ~ r2_orders_2(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f34,f21])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_orders_2(sK0,X0,X1)
      | ~ r2_orders_2(sK0,X1,X0) ) ),
    inference(resolution,[],[f24,f22])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r2_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:38:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (3045)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.47  % (3053)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.48  % (3053)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f128,f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    r2_hidden(sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f6])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f4])).
% 0.21/0.48  fof(f4,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_orders_2)).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f127,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK2)),
% 0.21/0.48    inference(resolution,[],[f125,f120])).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    ( ! [X0] : (r2_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f119,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    sK1 = sK3(sK1,sK0,sK2)),
% 0.21/0.48    inference(resolution,[],[f49,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    r2_hidden(sK1,k1_orders_2(sK0,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,sK2)) | sK3(X0,sK0,sK2) = X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f48,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    k1_orders_2(sK0,sK2) = a_2_0_orders_2(sK0,sK2)),
% 0.21/0.48    inference(resolution,[],[f41,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f40,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f39,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    v5_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f38,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    v4_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f37,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    v3_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)) )),
% 0.21/0.48    inference(resolution,[],[f23,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    l1_orders_2(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f8])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0] : (sK3(X0,sK0,sK2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(sK0,sK2))) )),
% 0.21/0.48    inference(resolution,[],[f47,f14])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f46,f18])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f45,f21])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f44,f20])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f43,f19])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK3(X1,sK0,X0) = X1 | ~r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.21/0.48    inference(resolution,[],[f30,f22])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~l1_orders_2(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sK3(X0,X1,X2) = X0 | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2) | r2_orders_2(sK0,X0,sK3(sK1,sK0,sK2))) )),
% 0.21/0.48    inference(resolution,[],[f118,f16])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(X1,k1_orders_2(sK0,sK2)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2) | r2_orders_2(sK0,X0,sK3(X1,sK0,sK2))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f117,f42])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK2) | r2_orders_2(sK0,X0,sK3(X1,sK0,sK2)) | ~r2_hidden(X1,a_2_0_orders_2(sK0,sK2))) )),
% 0.21/0.48    inference(resolution,[],[f116,f14])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK3(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f115,f18])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK3(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f21])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK3(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f113,f20])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK3(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.21/0.48    inference(subsumption_resolution,[],[f112,f19])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK3(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.21/0.49    inference(resolution,[],[f28,f22])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ( ! [X4,X2,X0,X1] : (~l1_orders_2(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~r2_hidden(X4,X2) | r2_orders_2(X1,X4,sK3(X0,X1,X2)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    ~r2_orders_2(sK0,sK1,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f124,f15])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ~r2_hidden(sK1,sK2) | ~r2_orders_2(sK0,sK1,sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f123,f17])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK2) | ~r2_orders_2(sK0,sK1,sK1)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f121])).
% 0.21/0.49  fof(f121,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,sK2) | ~r2_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(resolution,[],[f120,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0] : (~r2_orders_2(sK0,sK1,X0) | ~r2_orders_2(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.21/0.49    inference(resolution,[],[f35,f17])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X0,X1) | ~r2_orders_2(sK0,X1,X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f34,f21])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v5_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X0,X1) | ~r2_orders_2(sK0,X1,X0)) )),
% 0.21/0.49    inference(resolution,[],[f24,f22])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X2,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r2_orders_2(X0,X1,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_orders_2)).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (3053)------------------------------
% 0.21/0.49  % (3053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3053)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (3053)Memory used [KB]: 1663
% 0.21/0.49  % (3053)Time elapsed: 0.066 s
% 0.21/0.49  % (3053)------------------------------
% 0.21/0.49  % (3053)------------------------------
% 0.21/0.49  % (3033)Success in time 0.126 s
%------------------------------------------------------------------------------
