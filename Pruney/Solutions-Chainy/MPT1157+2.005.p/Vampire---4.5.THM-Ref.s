%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  125 (3136 expanded)
%              Number of leaves         :   15 ( 984 expanded)
%              Depth                    :   40
%              Number of atoms          :  712 (27828 expanded)
%              Number of equality atoms :  106 ( 654 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f209,f45,f73,f221])).

fof(f221,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k2_tarski(sK1,sK1)) ) ),
    inference(subsumption_resolution,[],[f220,f198])).

fof(f198,plain,(
    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f197,f46])).

fof(f46,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | ~ r2_orders_2(sK0,sK1,sK2) )
    & ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | r2_orders_2(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                  | ~ r2_orders_2(X0,X1,X2) )
                & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                  | r2_orders_2(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
                | ~ r2_orders_2(sK0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
                | r2_orders_2(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
              | ~ r2_orders_2(sK0,X1,X2) )
            & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
              | r2_orders_2(sK0,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
            | ~ r2_orders_2(sK0,sK1,X2) )
          & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
            | r2_orders_2(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
          | ~ r2_orders_2(sK0,sK1,X2) )
        & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
          | r2_orders_2(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ r2_orders_2(sK0,sK1,sK2) )
      & ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | r2_orders_2(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

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

fof(f197,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(resolution,[],[f194,f85])).

fof(f85,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ),
    inference(backward_demodulation,[],[f47,f83])).

fof(f83,plain,(
    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) ),
    inference(resolution,[],[f82,f45])).

fof(f82,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0) ) ),
    inference(subsumption_resolution,[],[f81,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0) ) ),
    inference(resolution,[],[f80,f44])).

fof(f44,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(X1),X0) ) ),
    inference(resolution,[],[f79,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X1)
      | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(X1),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f68,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f55,f49])).

fof(f49,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f47,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f29])).

fof(f194,plain,(
    ! [X2] :
      ( ~ r2_orders_2(sK0,sK1,X2)
      | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f193])).

fof(f193,plain,(
    ! [X2] :
      ( r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ r2_orders_2(sK0,sK1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ) ),
    inference(forward_demodulation,[],[f192,f109])).

fof(f109,plain,(
    k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)) ),
    inference(subsumption_resolution,[],[f108,f40])).

fof(f108,plain,
    ( k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f107,f41])).

fof(f41,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f107,plain,
    ( k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f106,f42])).

fof(f42,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f106,plain,
    ( k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f105,f43])).

fof(f43,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f105,plain,
    ( k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f104,f44])).

fof(f104,plain,
    ( k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f102,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

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

fof(f102,plain,(
    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f100,f83])).

fof(f100,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f99,f45])).

fof(f99,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f98,f40])).

fof(f98,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f97,f41])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f54,f44])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

fof(f192,plain,(
    ! [X2] :
      ( ~ r2_orders_2(sK0,sK1,X2)
      | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ) ),
    inference(subsumption_resolution,[],[f191,f40])).

fof(f191,plain,(
    ! [X2] :
      ( ~ r2_orders_2(sK0,sK1,X2)
      | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | v2_struct_0(sK0)
      | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ) ),
    inference(subsumption_resolution,[],[f190,f41])).

fof(f190,plain,(
    ! [X2] :
      ( ~ r2_orders_2(sK0,sK1,X2)
      | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ) ),
    inference(subsumption_resolution,[],[f189,f42])).

fof(f189,plain,(
    ! [X2] :
      ( ~ r2_orders_2(sK0,sK1,X2)
      | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ) ),
    inference(subsumption_resolution,[],[f188,f43])).

fof(f188,plain,(
    ! [X2] :
      ( ~ r2_orders_2(sK0,sK1,X2)
      | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ) ),
    inference(subsumption_resolution,[],[f187,f44])).

fof(f187,plain,(
    ! [X2] :
      ( ~ r2_orders_2(sK0,sK1,X2)
      | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ) ),
    inference(subsumption_resolution,[],[f184,f102])).

fof(f184,plain,(
    ! [X2] :
      ( ~ r2_orders_2(sK0,sK1,X2)
      | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,(
    ! [X2] :
      ( ~ r2_orders_2(sK0,sK1,X2)
      | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0)
      | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(superposition,[],[f69,f172])).

fof(f172,plain,(
    ! [X0] :
      ( sK1 = sK3(sK0,k2_tarski(sK1,sK1),X0)
      | r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | sK1 = sK3(sK0,k2_tarski(sK1,sK1),X0)
      | sK1 = sK3(sK0,k2_tarski(sK1,sK1),X0) ) ),
    inference(resolution,[],[f150,f76])).

fof(f76,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK5(X0,X1,X2) != X1
              & sK5(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK5(X0,X1,X2),X2) )
          & ( sK5(X0,X1,X2) = X1
            | sK5(X0,X1,X2) = X0
            | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK5(X0,X1,X2) != X1
            & sK5(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( sK5(X0,X1,X2) = X1
          | sK5(X0,X1,X2) = X0
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f150,plain,(
    ! [X0] :
      ( r2_hidden(sK3(sK0,k2_tarski(sK1,sK1),X0),k2_tarski(sK1,sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) ) ),
    inference(forward_demodulation,[],[f148,f109])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(sK3(sK0,k2_tarski(sK1,sK1),X0),k2_tarski(sK1,sK1))
      | r2_hidden(X0,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) ) ),
    inference(resolution,[],[f145,f102])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(sK3(sK0,X0,X1),X0)
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f144,f40])).

fof(f144,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f143,f41])).

fof(f143,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f142,f42])).

fof(f142,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f141,f43])).

fof(f141,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f70,f44])).

fof(f70,plain,(
    ! [X2,X3,X1] :
      ( ~ l1_orders_2(X1)
      | r2_hidden(sK3(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK3(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK3(X1,X2,X3),X3)
                & r2_hidden(sK3(X1,X2,X3),X2)
                & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK4(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f33,f32])).

fof(f32,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK3(X1,X2,X3),X3)
        & r2_hidden(sK3(X1,X2,X3),X2)
        & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK4(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X6,X5)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X4,X3)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f69,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_orders_2(X1,sK3(X1,X2,X3),X3)
      | r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f61])).

% (18267)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ r2_orders_2(X1,sK3(X1,X2,X3),X3)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f220,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | r2_orders_2(sK0,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,k2_tarski(sK1,sK1)) ) ),
    inference(forward_demodulation,[],[f219,f109])).

fof(f219,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ r2_hidden(X0,k2_tarski(sK1,sK1)) ) ),
    inference(subsumption_resolution,[],[f216,f102])).

fof(f216,plain,(
    ! [X0] :
      ( r2_orders_2(sK0,X0,sK2)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,k2_tarski(sK1,sK1)) ) ),
    inference(superposition,[],[f170,f210])).

fof(f210,plain,(
    sK2 = sK4(sK2,sK0,k2_tarski(sK1,sK1)) ),
    inference(resolution,[],[f198,f128])).

fof(f128,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | sK4(X0,sK0,k2_tarski(sK1,sK1)) = X0 ) ),
    inference(subsumption_resolution,[],[f127,f40])).

fof(f127,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | sK4(X0,sK0,k2_tarski(sK1,sK1)) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f126,f41])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | sK4(X0,sK0,k2_tarski(sK1,sK1)) = X0
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f125,f42])).

fof(f125,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | sK4(X0,sK0,k2_tarski(sK1,sK1)) = X0
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f124,f43])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | sK4(X0,sK0,k2_tarski(sK1,sK1)) = X0
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f123,f44])).

fof(f123,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | sK4(X0,sK0,k2_tarski(sK1,sK1)) = X0
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f122,f102])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
      | sK4(X0,sK0,k2_tarski(sK1,sK1)) = X0
      | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f57,f109])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | sK4(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X0,sK4(X2,sK0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f169,f40])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,sK4(X2,sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f168,f41])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,sK4(X2,sK0,X1))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f167,f42])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,sK4(X2,sK0,X1))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f166,f43])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,sK4(X2,sK0,X1))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f58,f44])).

fof(f58,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_orders_2(X1,X6,sK4(X0,X1,X2))
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f73,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f29])).

fof(f209,plain,(
    ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f198,f86])).

fof(f86,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f48,f83])).

fof(f48,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:00:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.50  % (18260)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (18282)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (18283)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.51  % (18274)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (18265)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (18266)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (18282)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f235,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(unit_resulting_resolution,[],[f209,f45,f73,f221])).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    ( ! [X0] : (r2_orders_2(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_tarski(sK1,sK1))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f220,f198])).
% 0.22/0.52  fof(f198,plain,(
% 0.22/0.52    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.22/0.52    inference(subsumption_resolution,[],[f197,f46])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    (((~r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,sK2)) & (r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | r2_orders_2(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f28,f27,f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~r2_orders_2(sK0,X1,X2)) & (r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | r2_orders_2(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~r2_orders_2(sK0,X1,X2)) & (r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | r2_orders_2(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,X2)) & (r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | r2_orders_2(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ? [X2] : ((~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,X2)) & (r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | r2_orders_2(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,sK2)) & (r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | r2_orders_2(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 0.22/0.52    inference(negated_conjecture,[],[f9])).
% 0.22/0.52  fof(f9,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_orders_2)).
% 0.22/0.52  fof(f197,plain,(
% 0.22/0.52    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f195])).
% 0.22/0.52  fof(f195,plain,(
% 0.22/0.52    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.22/0.52    inference(resolution,[],[f194,f85])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))),
% 0.22/0.52    inference(backward_demodulation,[],[f47,f83])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)),
% 0.22/0.52    inference(resolution,[],[f82,f45])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f81,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0)) )),
% 0.22/0.52    inference(resolution,[],[f80,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    l1_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_orders_2(X1) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(X1),X0)) )),
% 0.22/0.52    inference(resolution,[],[f79,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    ( ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.52  fof(f79,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_struct_0(X1) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(X1),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1)) )),
% 0.22/0.52    inference(resolution,[],[f68,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 0.22/0.52    inference(definition_unfolding,[],[f55,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f194,plain,(
% 0.22/0.52    ( ! [X2] : (~r2_orders_2(sK0,sK1,X2) | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f193])).
% 0.22/0.52  fof(f193,plain,(
% 0.22/0.52    ( ! [X2] : (r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~r2_orders_2(sK0,sK1,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f192,f109])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))),
% 0.22/0.52    inference(subsumption_resolution,[],[f108,f40])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)) | v2_struct_0(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f107,f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    v3_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f107,plain,(
% 0.22/0.52    k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f106,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    v4_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f105,f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    v5_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f105,plain,(
% 0.22/0.52    k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.52    inference(subsumption_resolution,[],[f104,f44])).
% 0.22/0.52  fof(f104,plain,(
% 0.22/0.52    k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.22/0.52    inference(resolution,[],[f102,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(forward_demodulation,[],[f100,f83])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(resolution,[],[f99,f45])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f98,f40])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f97,f41])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(resolution,[],[f54,f44])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).
% 0.22/0.52  fof(f192,plain,(
% 0.22/0.52    ( ! [X2] : (~r2_orders_2(sK0,sK1,X2) | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f191,f40])).
% 0.22/0.52  fof(f191,plain,(
% 0.22/0.52    ( ! [X2] : (~r2_orders_2(sK0,sK1,X2) | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f190,f41])).
% 0.22/0.52  fof(f190,plain,(
% 0.22/0.52    ( ! [X2] : (~r2_orders_2(sK0,sK1,X2) | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f189,f42])).
% 0.22/0.52  fof(f189,plain,(
% 0.22/0.52    ( ! [X2] : (~r2_orders_2(sK0,sK1,X2) | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f188,f43])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    ( ! [X2] : (~r2_orders_2(sK0,sK1,X2) | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f187,f44])).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    ( ! [X2] : (~r2_orders_2(sK0,sK1,X2) | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f184,f102])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    ( ! [X2] : (~r2_orders_2(sK0,sK1,X2) | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f183])).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    ( ! [X2] : (~r2_orders_2(sK0,sK1,X2) | r2_hidden(X2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | r2_hidden(X2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 0.22/0.52    inference(superposition,[],[f69,f172])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    ( ! [X0] : (sK1 = sK3(sK0,k2_tarski(sK1,sK1),X0) | r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f171])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK1 = sK3(sK0,k2_tarski(sK1,sK1),X0) | sK1 = sK3(sK0,k2_tarski(sK1,sK1),X0)) )),
% 0.22/0.52    inference(resolution,[],[f150,f76])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 0.22/0.52    inference(equality_resolution,[],[f62])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.52    inference(cnf_transformation,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK5(X0,X1,X2) != X1 & sK5(X0,X1,X2) != X0) | ~r2_hidden(sK5(X0,X1,X2),X2)) & (sK5(X0,X1,X2) = X1 | sK5(X0,X1,X2) = X0 | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.52    inference(rectify,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.52    inference(flattening,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.52  fof(f150,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(sK3(sK0,k2_tarski(sK1,sK1),X0),k2_tarski(sK1,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))) )),
% 0.22/0.52    inference(forward_demodulation,[],[f148,f109])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(sK3(sK0,k2_tarski(sK1,sK1),X0),k2_tarski(sK1,sK1)) | r2_hidden(X0,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))) )),
% 0.22/0.52    inference(resolution,[],[f145,f102])).
% 0.22/0.52  fof(f145,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(sK3(sK0,X0,X1),X0) | r2_hidden(X1,a_2_0_orders_2(sK0,X0))) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f144,f40])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_0_orders_2(sK0,X0)) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f143,f41])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_0_orders_2(sK0,X0)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f142,f42])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_0_orders_2(sK0,X0)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(subsumption_resolution,[],[f141,f43])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_hidden(sK3(sK0,X0,X1),X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X1,a_2_0_orders_2(sK0,X0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.52    inference(resolution,[],[f70,f44])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    ( ! [X2,X3,X1] : (~l1_orders_2(X1) | r2_hidden(sK3(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(X3,a_2_0_orders_2(X1,X2)) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.52    inference(equality_resolution,[],[f60])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | r2_hidden(sK3(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK3(X1,X2,X3),X3) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f31,f33,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK3(X1,X2,X3),X3) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.53    inference(rectify,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.53    inference(nnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.53    inference(flattening,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X2,X3,X1] : (~r2_orders_2(X1,sK3(X1,X2,X3),X3) | r2_hidden(X3,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(equality_resolution,[],[f61])).
% 0.22/0.53  % (18267)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~r2_orders_2(X1,sK3(X1,X2,X3),X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f220,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | r2_orders_2(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_tarski(sK1,sK1))) )),
% 0.22/0.53    inference(forward_demodulation,[],[f219,f109])).
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    ( ! [X0] : (r2_orders_2(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | ~r2_hidden(X0,k2_tarski(sK1,sK1))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f216,f102])).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    ( ! [X0] : (r2_orders_2(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,k2_tarski(sK1,sK1))) )),
% 0.22/0.53    inference(superposition,[],[f170,f210])).
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    sK2 = sK4(sK2,sK0,k2_tarski(sK1,sK1))),
% 0.22/0.53    inference(resolution,[],[f198,f128])).
% 0.22/0.53  fof(f128,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK4(X0,sK0,k2_tarski(sK1,sK1)) = X0) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f127,f40])).
% 0.22/0.53  fof(f127,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK4(X0,sK0,k2_tarski(sK1,sK1)) = X0 | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f126,f41])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK4(X0,sK0,k2_tarski(sK1,sK1)) = X0 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f125,f42])).
% 0.22/0.53  fof(f125,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK4(X0,sK0,k2_tarski(sK1,sK1)) = X0 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f124,f43])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK4(X0,sK0,k2_tarski(sK1,sK1)) = X0 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f123,f44])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK4(X0,sK0,k2_tarski(sK1,sK1)) = X0 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f122,f102])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK4(X0,sK0,k2_tarski(sK1,sK1)) = X0 | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(superposition,[],[f57,f109])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | sK4(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f170,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (r2_orders_2(sK0,X0,sK4(X2,sK0,X1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f169,f40])).
% 0.22/0.53  fof(f169,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,sK4(X2,sK0,X1)) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f168,f41])).
% 0.22/0.53  fof(f168,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,sK4(X2,sK0,X1)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f167,f42])).
% 0.22/0.53  fof(f167,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,sK4(X2,sK0,X1)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f166,f43])).
% 0.22/0.53  fof(f166,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X2,a_2_0_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,sK4(X2,sK0,X1)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 0.22/0.53    inference(resolution,[],[f58,f44])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X1] : (~l1_orders_2(X1) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | r2_orders_2(X1,X6,sK4(X0,X1,X2)) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 0.22/0.53    inference(equality_resolution,[],[f72])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 0.22/0.53    inference(equality_resolution,[],[f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f39])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  fof(f209,plain,(
% 0.22/0.53    ~r2_orders_2(sK0,sK1,sK2)),
% 0.22/0.53    inference(resolution,[],[f198,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ~r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~r2_orders_2(sK0,sK1,sK2)),
% 0.22/0.53    inference(backward_demodulation,[],[f48,f83])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ~r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,sK2)),
% 0.22/0.53    inference(cnf_transformation,[],[f29])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (18282)------------------------------
% 0.22/0.53  % (18282)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18282)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (18282)Memory used [KB]: 6396
% 0.22/0.53  % (18282)Time elapsed: 0.058 s
% 0.22/0.53  % (18282)------------------------------
% 0.22/0.53  % (18282)------------------------------
% 0.22/0.53  % (18259)Success in time 0.172 s
%------------------------------------------------------------------------------
