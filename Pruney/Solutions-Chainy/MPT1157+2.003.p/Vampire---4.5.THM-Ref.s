%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:02 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  109 (2290 expanded)
%              Number of leaves         :    9 ( 455 expanded)
%              Depth                    :   36
%              Number of atoms          :  467 (12819 expanded)
%              Number of equality atoms :   43 ( 412 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f318,plain,(
    $false ),
    inference(subsumption_resolution,[],[f317,f287])).

fof(f287,plain,(
    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f286,f76])).

fof(f76,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(backward_demodulation,[],[f24,f72])).

fof(f72,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f61,f27,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f48,f51])).

fof(f51,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

% (31559)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
fof(f48,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f27,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_orders_2(X0,X1,X2)
                <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_orders_2)).

fof(f61,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f28,f60,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f60,plain,(
    l1_struct_0(sK0) ),
    inference(unit_resulting_resolution,[],[f32,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f32,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f24,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f286,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f285,f82])).

fof(f82,plain,(
    k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f28,f29,f32,f31,f30,f75,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

fof(f75,plain,(
    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f70,f72])).

fof(f70,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(unit_resulting_resolution,[],[f61,f27,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f30,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f31,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f29,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f285,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f284,f28])).

fof(f284,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f283,f26])).

fof(f26,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f283,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f282,f75])).

fof(f282,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f281,f32])).

fof(f281,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f280,f31])).

fof(f280,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f279,f30])).

fof(f279,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f274,f29])).

fof(f274,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(superposition,[],[f57,f263])).

fof(f263,plain,(
    sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2) ),
    inference(subsumption_resolution,[],[f262,f205])).

fof(f205,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2) ),
    inference(resolution,[],[f199,f76])).

fof(f199,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2) ),
    inference(subsumption_resolution,[],[f198,f26])).

fof(f198,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2)
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f173,f77])).

fof(f77,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f25,f72])).

fof(f25,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f173,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = sK6(sK0,k2_tarski(sK1,sK1),X0) ) ),
    inference(forward_demodulation,[],[f172,f82])).

fof(f172,plain,(
    ! [X0] :
      ( r2_hidden(X0,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = sK6(sK0,k2_tarski(sK1,sK1),X0) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X0] :
      ( r2_hidden(X0,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | sK1 = sK6(sK0,k2_tarski(sK1,sK1),X0)
      | sK1 = sK6(sK0,k2_tarski(sK1,sK1),X0) ) ),
    inference(resolution,[],[f147,f75])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k2_tarski(X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(X0,X1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | sK6(sK0,k2_tarski(X0,X1),X2) = X1
      | sK6(sK0,k2_tarski(X0,X1),X2) = X0 ) ),
    inference(resolution,[],[f114,f35])).

fof(f35,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( sP4(sK6(sK0,k2_tarski(X1,X2),X0),X2,X1)
      | ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X0,a_2_0_orders_2(sK0,k2_tarski(X1,X2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f92,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f91,f28])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(sK6(sK0,X0,X1),X0)
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f90,f31])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(sK6(sK0,X0,X1),X0)
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f89,f30])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(sK6(sK0,X0,X1),X0)
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f88,f29])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(sK6(sK0,X0,X1),X0)
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f58,f32])).

fof(f58,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(sK6(X1,X2,X3),X2)
      | r2_hidden(X3,a_2_0_orders_2(X1,X2)) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | r2_hidden(sK6(X1,X2,X3),X2)
      | r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f262,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2) ),
    inference(subsumption_resolution,[],[f261,f75])).

fof(f261,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2) ),
    inference(subsumption_resolution,[],[f257,f63])).

fof(f63,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f56,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_tarski(X0,X1))
      | ~ sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f56,plain,(
    ! [X3,X1] : sP4(X3,X1,X3) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X3,X1] :
      ( X0 != X3
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f257,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK1))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2) ),
    inference(superposition,[],[f207,f82])).

fof(f207,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,a_2_0_orders_2(sK0,X0))
      | ~ r2_hidden(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2) ) ),
    inference(subsumption_resolution,[],[f206,f27])).

fof(f206,plain,(
    ! [X0] :
      ( sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ r2_hidden(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f199,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f126,f28])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f125,f32])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f124,f31])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f123,f30])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f29])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ l1_orders_2(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) ) ),
    inference(superposition,[],[f113,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( sK5(X0,X1,X2) = X0
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X1,sK5(X2,sK0,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f112,f28])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK5(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f111,f31])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK5(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f110,f30])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK5(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f109,f29])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,X0)
      | r2_orders_2(sK0,X1,sK5(X2,sK0,X0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f43,f32])).

fof(f43,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(X4,X2)
      | r2_orders_2(X1,X4,sK5(X0,X1,X2))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f57,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_orders_2(X1,sK6(X1,X2,X3),X3)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | v2_struct_0(X1)
      | r2_hidden(X3,a_2_0_orders_2(X1,X2)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X1)
      | ~ v3_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | X0 != X3
      | ~ r2_orders_2(X1,sK6(X1,X2,X3),X3)
      | r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f317,plain,(
    ~ r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(forward_demodulation,[],[f314,f82])).

fof(f314,plain,(
    ~ r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(unit_resulting_resolution,[],[f62,f75,f27,f303,f127])).

fof(f303,plain,(
    ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f287,f77])).

fof(f62,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(unit_resulting_resolution,[],[f55,f54])).

fof(f55,plain,(
    ! [X0,X3] : sP4(X3,X3,X0) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X3,X1] :
      ( X1 != X3
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:29:31 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.44  % (31558)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.48  % (31578)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.48  % (31567)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.48  % (31579)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.48  % (31563)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (31561)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.50  % (31583)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (31569)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (31574)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.50  % (31572)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (31562)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.50  % (31564)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (31589)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.51  % (31588)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.51  % (31566)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (31578)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f318,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(subsumption_resolution,[],[f317,f287])).
% 0.20/0.51  fof(f287,plain,(
% 0.20/0.51    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f286,f76])).
% 0.20/0.51  fof(f76,plain,(
% 0.20/0.51    r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(backward_demodulation,[],[f24,f72])).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f61,f27,f52])).
% 0.20/0.51  fof(f52,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f48,f51])).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  % (31559)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,negated_conjecture,(
% 0.20/0.51    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 0.20/0.51    inference(negated_conjecture,[],[f9])).
% 0.20/0.51  fof(f9,conjecture,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_orders_2)).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f28,f60,f49])).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f21])).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.51  fof(f60,plain,(
% 0.20/0.51    l1_struct_0(sK0)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f32,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f23])).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    l1_orders_2(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ~v2_struct_0(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f286,plain,(
% 0.20/0.51    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~r2_orders_2(sK0,sK1,sK2)),
% 0.20/0.51    inference(forward_demodulation,[],[f285,f82])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f28,f29,f32,f31,f30,f75,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).
% 0.20/0.51  fof(f75,plain,(
% 0.20/0.51    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(backward_demodulation,[],[f70,f72])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f61,f27,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f18])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.51    inference(flattening,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    v4_orders_2(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    v5_orders_2(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    v3_orders_2(sK0)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f285,plain,(
% 0.20/0.51    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f284,f28])).
% 0.20/0.51  fof(f284,plain,(
% 0.20/0.51    ~r2_orders_2(sK0,sK1,sK2) | v2_struct_0(sK0) | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f283,f26])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f283,plain,(
% 0.20/0.51    ~r2_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f282,f75])).
% 0.20/0.51  fof(f282,plain,(
% 0.20/0.51    ~r2_orders_2(sK0,sK1,sK2) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f281,f32])).
% 0.20/0.51  fof(f281,plain,(
% 0.20/0.51    ~r2_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f280,f31])).
% 0.20/0.51  fof(f280,plain,(
% 0.20/0.51    ~r2_orders_2(sK0,sK1,sK2) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f279,f30])).
% 0.20/0.51  fof(f279,plain,(
% 0.20/0.51    ~r2_orders_2(sK0,sK1,sK2) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(subsumption_resolution,[],[f274,f29])).
% 0.20/0.51  fof(f274,plain,(
% 0.20/0.51    ~r2_orders_2(sK0,sK1,sK2) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(superposition,[],[f57,f263])).
% 0.20/0.51  fof(f263,plain,(
% 0.20/0.51    sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f262,f205])).
% 0.20/0.51  fof(f205,plain,(
% 0.20/0.51    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2)),
% 0.20/0.51    inference(resolution,[],[f199,f76])).
% 0.20/0.51  fof(f199,plain,(
% 0.20/0.51    ~r2_orders_2(sK0,sK1,sK2) | sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f198,f26])).
% 0.20/0.51  fof(f198,plain,(
% 0.20/0.51    ~m1_subset_1(sK2,u1_struct_0(sK0)) | sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2) | ~r2_orders_2(sK0,sK1,sK2)),
% 0.20/0.51    inference(resolution,[],[f173,f77])).
% 0.20/0.51  fof(f77,plain,(
% 0.20/0.51    ~r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~r2_orders_2(sK0,sK1,sK2)),
% 0.20/0.51    inference(backward_demodulation,[],[f25,f72])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ~r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f173,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = sK6(sK0,k2_tarski(sK1,sK1),X0)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f172,f82])).
% 0.20/0.51  fof(f172,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = sK6(sK0,k2_tarski(sK1,sK1),X0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f169])).
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    ( ! [X0] : (r2_hidden(X0,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | sK1 = sK6(sK0,k2_tarski(sK1,sK1),X0) | sK1 = sK6(sK0,k2_tarski(sK1,sK1),X0)) )),
% 0.20/0.51    inference(resolution,[],[f147,f75])).
% 0.20/0.51  fof(f147,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(k2_tarski(X0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(X0,X1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | sK6(sK0,k2_tarski(X0,X1),X2) = X1 | sK6(sK0,k2_tarski(X0,X1),X2) = X0) )),
% 0.20/0.51    inference(resolution,[],[f114,f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.51  fof(f114,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sP4(sK6(sK0,k2_tarski(X1,X2),X0),X2,X1) | ~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X0,a_2_0_orders_2(sK0,k2_tarski(X1,X2))) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.20/0.51    inference(resolution,[],[f92,f53])).
% 0.20/0.51  fof(f53,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | sP4(X3,X1,X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f37])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f92,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f91,f28])).
% 0.20/0.51  fof(f91,plain,(
% 0.20/0.51    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK6(sK0,X0,X1),X0) | r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f90,f31])).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK6(sK0,X0,X1),X0) | r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f89,f30])).
% 0.20/0.51  fof(f89,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK6(sK0,X0,X1),X0) | r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f88,f29])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK6(sK0,X0,X1),X0) | r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.20/0.51    inference(resolution,[],[f58,f32])).
% 0.20/0.51  fof(f58,plain,(
% 0.20/0.51    ( ! [X2,X3,X1] : (~l1_orders_2(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)) | r2_hidden(sK6(X1,X2,X3),X2) | r2_hidden(X3,a_2_0_orders_2(X1,X2))) )),
% 0.20/0.51    inference(equality_resolution,[],[f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (v2_struct_0(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)) | X0 != X3 | r2_hidden(sK6(X1,X2,X3),X2) | r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.20/0.51    inference(flattening,[],[f13])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.20/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 0.20/0.51  fof(f262,plain,(
% 0.20/0.51    ~r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f261,f75])).
% 0.20/0.51  fof(f261,plain,(
% 0.20/0.51    ~r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2)),
% 0.20/0.51    inference(subsumption_resolution,[],[f257,f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f56,f54])).
% 0.20/0.51  fof(f54,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_tarski(X0,X1)) | ~sP4(X3,X1,X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f36])).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f56,plain,(
% 0.20/0.51    ( ! [X3,X1] : (sP4(X3,X1,X3)) )),
% 0.20/0.51    inference(equality_resolution,[],[f33])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (X0 != X3 | sP4(X3,X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f257,plain,(
% 0.20/0.51    ~r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~r2_hidden(sK1,k2_tarski(sK1,sK1)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2)),
% 0.20/0.51    inference(superposition,[],[f207,f82])).
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    ( ! [X0] : (~r2_hidden(sK2,a_2_0_orders_2(sK0,X0)) | ~r2_hidden(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f206,f27])).
% 0.20/0.51  fof(f206,plain,(
% 0.20/0.51    ( ! [X0] : (sK1 = sK6(sK0,k2_tarski(sK1,sK1),sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2,a_2_0_orders_2(sK0,X0))) )),
% 0.20/0.51    inference(resolution,[],[f199,f127])).
% 0.20/0.51  fof(f127,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_orders_2(sK0,X2,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f126,f28])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_orders_2(sK0,X2,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1)) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f125,f32])).
% 0.20/0.51  fof(f125,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_orders_2(sK0,X2,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1)) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f124,f31])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_orders_2(sK0,X2,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1)) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f123,f30])).
% 0.20/0.51  fof(f123,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_orders_2(sK0,X2,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1)) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f117,f29])).
% 0.20/0.51  fof(f117,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_orders_2(sK0,X2,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1)) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.20/0.51    inference(duplicate_literal_removal,[],[f116])).
% 0.20/0.51  fof(f116,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_orders_2(sK0,X2,X0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1)) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1))) )),
% 0.20/0.51    inference(superposition,[],[f113,f45])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (sK5(X0,X1,X2) = X0 | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | v2_struct_0(X1) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f113,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (r2_orders_2(sK0,X1,sK5(X2,sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f112,f28])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK5(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f111,f31])).
% 0.20/0.51  fof(f111,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK5(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f110,f30])).
% 0.20/0.51  fof(f110,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK5(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.20/0.51    inference(subsumption_resolution,[],[f109,f29])).
% 0.20/0.51  fof(f109,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,X0) | r2_orders_2(sK0,X1,sK5(X2,sK0,X0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X0))) )),
% 0.20/0.51    inference(resolution,[],[f43,f32])).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X1] : (~l1_orders_2(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~r2_hidden(X4,X2) | r2_orders_2(X1,X4,sK5(X0,X1,X2)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X2,X3,X1] : (~r2_orders_2(X1,sK6(X1,X2,X3),X3) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)) | v2_struct_0(X1) | r2_hidden(X3,a_2_0_orders_2(X1,X2))) )),
% 0.20/0.51    inference(equality_resolution,[],[f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (v2_struct_0(X1) | ~v3_orders_2(X1) | ~v4_orders_2(X1) | ~v5_orders_2(X1) | ~l1_orders_2(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_subset_1(X3,u1_struct_0(X1)) | X0 != X3 | ~r2_orders_2(X1,sK6(X1,X2,X3),X3) | r2_hidden(X0,a_2_0_orders_2(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f317,plain,(
% 0.20/0.51    ~r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(forward_demodulation,[],[f314,f82])).
% 0.20/0.51  fof(f314,plain,(
% 0.20/0.51    ~r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f62,f75,f27,f303,f127])).
% 0.20/0.51  fof(f303,plain,(
% 0.20/0.51    ~r2_orders_2(sK0,sK1,sK2)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f287,f77])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f55,f54])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X0,X3] : (sP4(X3,X3,X0)) )),
% 0.20/0.51    inference(equality_resolution,[],[f34])).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X0,X3,X1] : (X1 != X3 | sP4(X3,X1,X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (31578)------------------------------
% 0.20/0.51  % (31578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (31578)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (31578)Memory used [KB]: 1918
% 0.20/0.51  % (31578)Time elapsed: 0.122 s
% 0.20/0.51  % (31578)------------------------------
% 0.20/0.51  % (31578)------------------------------
% 0.20/0.51  % (31560)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (31554)Success in time 0.167 s
%------------------------------------------------------------------------------
