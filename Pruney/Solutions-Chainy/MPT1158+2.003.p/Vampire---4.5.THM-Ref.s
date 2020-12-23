%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:03 EST 2020

% Result     : Theorem 1.55s
% Output     : Refutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :  159 (17467 expanded)
%              Number of leaves         :   14 (5568 expanded)
%              Depth                    :   51
%              Number of atoms          :  787 (164269 expanded)
%              Number of equality atoms :   91 (1721 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f682,plain,(
    $false ),
    inference(subsumption_resolution,[],[f675,f664])).

fof(f664,plain,(
    ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f620,f261])).

fof(f261,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f48,f259])).

fof(f259,plain,(
    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    inference(subsumption_resolution,[],[f258,f40])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | ~ r2_orders_2(sK0,sK1,sK2) )
    & ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | r2_orders_2(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                  | ~ r2_orders_2(X0,X1,X2) )
                & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
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
              ( ( ~ r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
                | ~ r2_orders_2(sK0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
                | r2_orders_2(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              | ~ r2_orders_2(sK0,X1,X2) )
            & ( r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              | r2_orders_2(sK0,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            | ~ r2_orders_2(sK0,sK1,X2) )
          & ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            | r2_orders_2(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          | ~ r2_orders_2(sK0,sK1,X2) )
        & ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          | r2_orders_2(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
        | ~ r2_orders_2(sK0,sK1,sK2) )
      & ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
        | r2_orders_2(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
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
                <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
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
              <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).

fof(f258,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f257,f41])).

fof(f41,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f257,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f256,f42])).

fof(f42,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f256,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f255,f43])).

fof(f43,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f255,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f254,f44])).

fof(f44,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f254,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f253,f45])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f253,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f248,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_orders_2)).

fof(f248,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    inference(resolution,[],[f241,f77])).

fof(f77,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) ),
    inference(resolution,[],[f46,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f46,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f241,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f235,f87])).

fof(f87,plain,(
    ! [X6] :
      ( ~ r2_hidden(X6,k6_domain_1(u1_struct_0(sK0),sK1))
      | ~ v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f75,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f75,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f74,f40])).

fof(f74,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f73,f41])).

fof(f73,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f71,f44])).

fof(f71,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f45,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(f235,plain,
    ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),sK1),k6_domain_1(u1_struct_0(sK0),sK1))
    | r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(resolution,[],[f123,f45])).

fof(f123,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X5),k6_domain_1(u1_struct_0(sK0),sK1))
      | r2_hidden(X5,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ) ),
    inference(forward_demodulation,[],[f122,f93])).

fof(f93,plain,(
    k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(subsumption_resolution,[],[f92,f40])).

fof(f92,plain,
    ( k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f91,f41])).

fof(f91,plain,
    ( k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f90,f42])).

fof(f90,plain,
    ( k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f89,f43])).

fof(f89,plain,
    ( k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f81,f44])).

fof(f81,plain,
    ( k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f75,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
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
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(f122,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X5),k6_domain_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ) ),
    inference(subsumption_resolution,[],[f121,f40])).

fof(f121,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X5),k6_domain_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f120,f41])).

fof(f120,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X5),k6_domain_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f119,f42])).

fof(f119,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X5),k6_domain_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f118,f43])).

fof(f118,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X5),k6_domain_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f44])).

fof(f86,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X5),k6_domain_1(u1_struct_0(sK0),sK1))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f75,f66])).

fof(f66,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_hidden(sK3(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | r2_hidden(X3,a_2_1_orders_2(X1,X2))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | r2_hidden(sK3(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
                & r2_hidden(sK3(X1,X2,X3),X2)
                & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK4(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK4(X0,X1,X2) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f34,f33])).

fof(f33,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
        & r2_hidden(sK3(X1,X2,X3),X2)
        & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK4(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK4(X0,X1,X2) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( r2_orders_2(X1,X3,X4)
                  | ~ r2_hidden(X4,X2)
                  | ~ m1_subset_1(X4,u1_struct_0(X1)) )
              & X0 = X3
              & m1_subset_1(X3,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f48,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f620,plain,(
    r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) ),
    inference(subsumption_resolution,[],[f619,f260])).

fof(f260,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f47,f259])).

fof(f47,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f619,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f618,f265])).

fof(f265,plain,(
    k2_orders_2(sK0,k1_tarski(sK2)) = a_2_1_orders_2(sK0,k1_tarski(sK2)) ),
    inference(backward_demodulation,[],[f137,f259])).

fof(f137,plain,(
    k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(subsumption_resolution,[],[f136,f40])).

fof(f136,plain,
    ( k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f135,f41])).

fof(f135,plain,
    ( k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f134,f42])).

fof(f134,plain,
    ( k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f133,f43])).

fof(f133,plain,
    ( k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f125,f44])).

fof(f125,plain,
    ( k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f80,f61])).

fof(f80,plain,(
    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f79,f40])).

fof(f79,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f78,f41])).

fof(f78,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f76,f44])).

fof(f76,plain,
    ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f46,f63])).

fof(f618,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) ),
    inference(subsumption_resolution,[],[f617,f40])).

fof(f617,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f616,f41])).

fof(f616,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f615,f42])).

fof(f615,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f614,f43])).

fof(f614,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f613,f44])).

fof(f613,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f612,f262])).

fof(f262,plain,(
    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f80,f259])).

fof(f612,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f611,f45])).

fof(f611,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f65,f606])).

fof(f606,plain,(
    sK2 = sK3(sK0,k1_tarski(sK2),sK1) ),
    inference(subsumption_resolution,[],[f605,f498])).

fof(f498,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | sK2 = sK3(sK0,k1_tarski(sK2),sK1) ),
    inference(resolution,[],[f492,f261])).

fof(f492,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | sK2 = sK3(sK0,k1_tarski(sK2),sK1) ),
    inference(resolution,[],[f305,f70])).

fof(f70,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).

fof(f38,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f305,plain,
    ( r2_hidden(sK3(sK0,k1_tarski(sK2),sK1),k1_tarski(sK2))
    | r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) ),
    inference(forward_demodulation,[],[f281,f259])).

fof(f281,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),sK1),k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(backward_demodulation,[],[f242,f259])).

fof(f242,plain,
    ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),sK1),k6_domain_1(u1_struct_0(sK0),sK2))
    | r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(resolution,[],[f167,f45])).

fof(f167,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),X5),k6_domain_1(u1_struct_0(sK0),sK2))
      | r2_hidden(X5,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ) ),
    inference(forward_demodulation,[],[f166,f137])).

fof(f166,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),X5),k6_domain_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ) ),
    inference(subsumption_resolution,[],[f165,f40])).

fof(f165,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),X5),k6_domain_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f164,f41])).

fof(f164,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),X5),k6_domain_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f163,f42])).

fof(f163,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),X5),k6_domain_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f162,f43])).

fof(f162,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),X5),k6_domain_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f130,f44])).

fof(f130,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),X5),k6_domain_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f80,f66])).

fof(f605,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | sK2 = sK3(sK0,k1_tarski(sK2),sK1) ),
    inference(duplicate_literal_removal,[],[f604])).

fof(f604,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2)
    | sK2 = sK3(sK0,k1_tarski(sK2),sK1) ),
    inference(superposition,[],[f602,f499])).

fof(f499,plain,
    ( sK1 = sK4(sK1,sK0,k1_tarski(sK2))
    | sK2 = sK3(sK0,k1_tarski(sK2),sK1) ),
    inference(resolution,[],[f492,f288])).

fof(f288,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k1_tarski(sK2)))
      | sK4(X1,sK0,k1_tarski(sK2)) = X1 ) ),
    inference(forward_demodulation,[],[f267,f259])).

fof(f267,plain,(
    ! [X1] :
      ( sK4(X1,sK0,k1_tarski(sK2)) = X1
      | ~ r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ) ),
    inference(backward_demodulation,[],[f149,f259])).

fof(f149,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | sK4(X1,sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = X1 ) ),
    inference(forward_demodulation,[],[f148,f137])).

fof(f148,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | sK4(X1,sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = X1 ) ),
    inference(subsumption_resolution,[],[f147,f40])).

fof(f147,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | sK4(X1,sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = X1
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f146,f41])).

fof(f146,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | sK4(X1,sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = X1
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f145,f42])).

fof(f145,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | sK4(X1,sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = X1
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f144,f43])).

fof(f144,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | sK4(X1,sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = X1
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f127,f44])).

fof(f127,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | sK4(X1,sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = X1
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f80,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | sK4(X0,X1,X2) = X0
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f602,plain,
    ( r2_orders_2(sK0,sK4(sK1,sK0,k1_tarski(sK2)),sK2)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f597,f69])).

fof(f69,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f597,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK2))
    | r2_orders_2(sK0,sK4(sK1,sK0,k1_tarski(sK2)),sK2)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f515,f46])).

fof(f515,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ r2_hidden(X1,k1_tarski(sK2))
      | r2_orders_2(sK0,sK4(sK1,sK0,k1_tarski(sK2)),X1)
      | r2_orders_2(sK0,sK1,sK2) ) ),
    inference(resolution,[],[f290,f260])).

fof(f290,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k2_orders_2(sK0,k1_tarski(sK2)))
      | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2)
      | ~ r2_hidden(X2,k1_tarski(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f289,f259])).

fof(f289,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k2_orders_2(sK0,k1_tarski(sK2)))
      | ~ r2_hidden(X2,k1_tarski(sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2) ) ),
    inference(forward_demodulation,[],[f268,f259])).

fof(f268,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k1_tarski(sK2))
      | ~ r2_hidden(X3,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2) ) ),
    inference(backward_demodulation,[],[f155,f259])).

fof(f155,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | ~ r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2) ) ),
    inference(forward_demodulation,[],[f154,f137])).

fof(f154,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2) ) ),
    inference(subsumption_resolution,[],[f153,f40])).

fof(f153,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f152,f41])).

fof(f152,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f151,f42])).

fof(f151,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f150,f43])).

fof(f150,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f128,f44])).

fof(f128,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK2))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X3,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f80,f52])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | r2_orders_2(X1,sK4(X0,X1,X2),X6)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f65,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
      | r2_hidden(X3,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ r2_orders_2(X1,X3,sK3(X1,X2,X3))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f675,plain,(
    r2_orders_2(sK0,sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f672])).

fof(f672,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(backward_demodulation,[],[f602,f666])).

fof(f666,plain,(
    sK1 = sK4(sK1,sK0,k1_tarski(sK2)) ),
    inference(resolution,[],[f620,f288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:54:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (31179)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.50  % (31204)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.51  % (31204)Refutation not found, incomplete strategy% (31204)------------------------------
% 0.22/0.51  % (31204)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (31204)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (31204)Memory used [KB]: 6268
% 0.22/0.51  % (31204)Time elapsed: 0.113 s
% 0.22/0.51  % (31204)------------------------------
% 0.22/0.51  % (31204)------------------------------
% 0.22/0.51  % (31188)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.52  % (31184)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (31183)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (31208)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (31196)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.52  % (31208)Refutation not found, incomplete strategy% (31208)------------------------------
% 0.22/0.52  % (31208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (31208)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (31208)Memory used [KB]: 1663
% 0.22/0.52  % (31208)Time elapsed: 0.002 s
% 0.22/0.52  % (31208)------------------------------
% 0.22/0.52  % (31208)------------------------------
% 0.22/0.53  % (31185)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (31193)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (31201)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (31186)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (31180)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (31189)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.54  % (31181)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (31207)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (31202)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (31183)Refutation not found, incomplete strategy% (31183)------------------------------
% 0.22/0.55  % (31183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (31183)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (31183)Memory used [KB]: 1918
% 0.22/0.55  % (31183)Time elapsed: 0.136 s
% 0.22/0.55  % (31183)------------------------------
% 0.22/0.55  % (31183)------------------------------
% 0.22/0.55  % (31200)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (31194)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (31199)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.55/0.56  % (31192)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.55/0.56  % (31187)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.55/0.56  % (31191)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.55/0.56  % (31189)Refutation not found, incomplete strategy% (31189)------------------------------
% 1.55/0.56  % (31189)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (31189)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (31189)Memory used [KB]: 10746
% 1.55/0.56  % (31189)Time elapsed: 0.142 s
% 1.55/0.56  % (31189)------------------------------
% 1.55/0.56  % (31189)------------------------------
% 1.55/0.56  % (31191)Refutation not found, incomplete strategy% (31191)------------------------------
% 1.55/0.56  % (31191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.56  % (31191)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.56  
% 1.55/0.56  % (31191)Memory used [KB]: 10746
% 1.55/0.56  % (31191)Time elapsed: 0.154 s
% 1.55/0.56  % (31191)------------------------------
% 1.55/0.56  % (31191)------------------------------
% 1.55/0.57  % (31206)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.55/0.57  % (31182)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.55/0.57  % (31207)Refutation not found, incomplete strategy% (31207)------------------------------
% 1.55/0.57  % (31207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (31207)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (31207)Memory used [KB]: 10746
% 1.55/0.57  % (31207)Time elapsed: 0.156 s
% 1.55/0.57  % (31207)------------------------------
% 1.55/0.57  % (31207)------------------------------
% 1.55/0.57  % (31190)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.55/0.57  % (31205)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.55/0.57  % (31195)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.55/0.57  % (31205)Refutation not found, incomplete strategy% (31205)------------------------------
% 1.55/0.57  % (31205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (31205)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (31205)Memory used [KB]: 6268
% 1.55/0.57  % (31205)Time elapsed: 0.154 s
% 1.55/0.57  % (31205)------------------------------
% 1.55/0.57  % (31205)------------------------------
% 1.55/0.57  % (31195)Refutation not found, incomplete strategy% (31195)------------------------------
% 1.55/0.57  % (31195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.57  % (31195)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.57  
% 1.55/0.57  % (31195)Memory used [KB]: 10618
% 1.55/0.57  % (31195)Time elapsed: 0.158 s
% 1.55/0.57  % (31195)------------------------------
% 1.55/0.57  % (31195)------------------------------
% 1.55/0.58  % (31197)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.55/0.58  % (31203)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.55/0.58  % (31197)Refutation not found, incomplete strategy% (31197)------------------------------
% 1.55/0.58  % (31197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.58  % (31197)Termination reason: Refutation not found, incomplete strategy
% 1.55/0.58  
% 1.55/0.58  % (31197)Memory used [KB]: 1791
% 1.55/0.58  % (31197)Time elapsed: 0.165 s
% 1.55/0.58  % (31197)------------------------------
% 1.55/0.58  % (31197)------------------------------
% 1.55/0.58  % (31203)Refutation not found, incomplete strategy% (31203)------------------------------
% 1.55/0.58  % (31203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (31198)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.55/0.59  % (31193)Refutation found. Thanks to Tanya!
% 1.55/0.59  % SZS status Theorem for theBenchmark
% 1.55/0.59  % SZS output start Proof for theBenchmark
% 1.55/0.59  fof(f682,plain,(
% 1.55/0.59    $false),
% 1.55/0.59    inference(subsumption_resolution,[],[f675,f664])).
% 1.55/0.59  fof(f664,plain,(
% 1.55/0.59    ~r2_orders_2(sK0,sK1,sK2)),
% 1.55/0.59    inference(resolution,[],[f620,f261])).
% 1.55/0.59  fof(f261,plain,(
% 1.55/0.59    ~r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) | ~r2_orders_2(sK0,sK1,sK2)),
% 1.55/0.59    inference(backward_demodulation,[],[f48,f259])).
% 1.55/0.59  fof(f259,plain,(
% 1.55/0.59    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)),
% 1.55/0.59    inference(subsumption_resolution,[],[f258,f40])).
% 1.55/0.59  fof(f40,plain,(
% 1.55/0.59    ~v2_struct_0(sK0)),
% 1.55/0.59    inference(cnf_transformation,[],[f30])).
% 1.55/0.59  fof(f30,plain,(
% 1.55/0.59    (((~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~r2_orders_2(sK0,sK1,sK2)) & (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.55/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 1.55/0.59  fof(f27,plain,(
% 1.55/0.59    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_orders_2(sK0,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | r2_orders_2(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.55/0.59    introduced(choice_axiom,[])).
% 1.55/0.59  fof(f28,plain,(
% 1.55/0.59    ? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_orders_2(sK0,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | r2_orders_2(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_orders_2(sK0,sK1,X2)) & (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | r2_orders_2(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.55/0.59    introduced(choice_axiom,[])).
% 1.55/0.59  fof(f29,plain,(
% 1.55/0.59    ? [X2] : ((~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | ~r2_orders_2(sK0,sK1,X2)) & (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2))) | r2_orders_2(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~r2_orders_2(sK0,sK1,sK2)) & (r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.55/0.59    introduced(choice_axiom,[])).
% 1.55/0.59  fof(f26,plain,(
% 1.55/0.59    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.55/0.59    inference(flattening,[],[f25])).
% 1.55/0.59  fof(f25,plain,(
% 1.55/0.59    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.55/0.59    inference(nnf_transformation,[],[f13])).
% 1.55/0.59  fof(f13,plain,(
% 1.55/0.59    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.55/0.59    inference(flattening,[],[f12])).
% 1.55/0.59  fof(f12,plain,(
% 1.55/0.59    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.55/0.59    inference(ennf_transformation,[],[f10])).
% 1.55/0.59  fof(f10,negated_conjecture,(
% 1.55/0.59    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 1.55/0.59    inference(negated_conjecture,[],[f9])).
% 1.55/0.59  fof(f9,conjecture,(
% 1.55/0.59    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).
% 1.55/0.59  fof(f258,plain,(
% 1.55/0.59    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f257,f41])).
% 1.55/0.59  fof(f41,plain,(
% 1.55/0.59    v3_orders_2(sK0)),
% 1.55/0.59    inference(cnf_transformation,[],[f30])).
% 1.55/0.59  fof(f257,plain,(
% 1.55/0.59    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f256,f42])).
% 1.55/0.59  fof(f42,plain,(
% 1.55/0.59    v4_orders_2(sK0)),
% 1.55/0.59    inference(cnf_transformation,[],[f30])).
% 1.55/0.59  fof(f256,plain,(
% 1.55/0.59    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f255,f43])).
% 1.55/0.59  fof(f43,plain,(
% 1.55/0.59    v5_orders_2(sK0)),
% 1.55/0.59    inference(cnf_transformation,[],[f30])).
% 1.55/0.59  fof(f255,plain,(
% 1.55/0.59    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f254,f44])).
% 1.55/0.59  fof(f44,plain,(
% 1.55/0.59    l1_orders_2(sK0)),
% 1.55/0.59    inference(cnf_transformation,[],[f30])).
% 1.55/0.59  fof(f254,plain,(
% 1.55/0.59    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f253,f45])).
% 1.55/0.59  fof(f45,plain,(
% 1.55/0.59    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.55/0.59    inference(cnf_transformation,[],[f30])).
% 1.55/0.59  fof(f253,plain,(
% 1.55/0.59    k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(resolution,[],[f248,f60])).
% 1.55/0.59  fof(f60,plain,(
% 1.55/0.59    ( ! [X0,X1] : (~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f18])).
% 1.55/0.59  fof(f18,plain,(
% 1.55/0.59    ! [X0] : (! [X1] : (~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.55/0.59    inference(flattening,[],[f17])).
% 1.55/0.59  fof(f17,plain,(
% 1.55/0.59    ! [X0] : (! [X1] : (~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.55/0.59    inference(ennf_transformation,[],[f8])).
% 1.55/0.59  fof(f8,axiom,(
% 1.55/0.59    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_orders_2)).
% 1.55/0.59  fof(f248,plain,(
% 1.55/0.59    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)),
% 1.55/0.59    inference(resolution,[],[f241,f77])).
% 1.55/0.59  fof(f77,plain,(
% 1.55/0.59    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK2) = k1_tarski(sK2)),
% 1.55/0.59    inference(resolution,[],[f46,f62])).
% 1.55/0.59  fof(f62,plain,(
% 1.55/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f22])).
% 1.55/0.59  fof(f22,plain,(
% 1.55/0.59    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.55/0.59    inference(flattening,[],[f21])).
% 1.55/0.59  fof(f21,plain,(
% 1.55/0.59    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.55/0.59    inference(ennf_transformation,[],[f6])).
% 1.55/0.59  fof(f6,axiom,(
% 1.55/0.59    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.55/0.59  fof(f46,plain,(
% 1.55/0.59    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.55/0.59    inference(cnf_transformation,[],[f30])).
% 1.55/0.59  fof(f241,plain,(
% 1.55/0.59    ~v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 1.55/0.59    inference(resolution,[],[f235,f87])).
% 1.55/0.59  fof(f87,plain,(
% 1.55/0.59    ( ! [X6] : (~r2_hidden(X6,k6_domain_1(u1_struct_0(sK0),sK1)) | ~v1_xboole_0(u1_struct_0(sK0))) )),
% 1.55/0.59    inference(resolution,[],[f75,f49])).
% 1.55/0.59  fof(f49,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f14])).
% 1.55/0.59  fof(f14,plain,(
% 1.55/0.59    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.55/0.59    inference(ennf_transformation,[],[f3])).
% 1.55/0.59  fof(f3,axiom,(
% 1.55/0.59    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.55/0.59  fof(f75,plain,(
% 1.55/0.59    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.59    inference(subsumption_resolution,[],[f74,f40])).
% 1.55/0.59  fof(f74,plain,(
% 1.55/0.59    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f73,f41])).
% 1.55/0.59  fof(f73,plain,(
% 1.55/0.59    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f71,f44])).
% 1.55/0.59  fof(f71,plain,(
% 1.55/0.59    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(resolution,[],[f45,f63])).
% 1.55/0.59  fof(f63,plain,(
% 1.55/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f24])).
% 1.55/0.59  fof(f24,plain,(
% 1.55/0.59    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.55/0.59    inference(flattening,[],[f23])).
% 1.55/0.59  fof(f23,plain,(
% 1.55/0.59    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.55/0.59    inference(ennf_transformation,[],[f11])).
% 1.55/0.59  fof(f11,plain,(
% 1.55/0.59    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.55/0.59    inference(pure_predicate_removal,[],[f7])).
% 1.55/0.59  fof(f7,axiom,(
% 1.55/0.59    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).
% 1.55/0.59  fof(f235,plain,(
% 1.55/0.59    r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),sK1),k6_domain_1(u1_struct_0(sK0),sK1)) | r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 1.55/0.59    inference(resolution,[],[f123,f45])).
% 1.55/0.59  fof(f123,plain,(
% 1.55/0.59    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X5),k6_domain_1(u1_struct_0(sK0),sK1)) | r2_hidden(X5,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) )),
% 1.55/0.59    inference(forward_demodulation,[],[f122,f93])).
% 1.55/0.59  fof(f93,plain,(
% 1.55/0.59    k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.55/0.59    inference(subsumption_resolution,[],[f92,f40])).
% 1.55/0.59  fof(f92,plain,(
% 1.55/0.59    k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f91,f41])).
% 1.55/0.59  fof(f91,plain,(
% 1.55/0.59    k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f90,f42])).
% 1.55/0.59  fof(f90,plain,(
% 1.55/0.59    k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f89,f43])).
% 1.55/0.59  fof(f89,plain,(
% 1.55/0.59    k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f81,f44])).
% 1.55/0.59  fof(f81,plain,(
% 1.55/0.59    k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(resolution,[],[f75,f61])).
% 1.55/0.59  fof(f61,plain,(
% 1.55/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f20])).
% 1.55/0.59  fof(f20,plain,(
% 1.55/0.59    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.55/0.59    inference(flattening,[],[f19])).
% 1.55/0.59  fof(f19,plain,(
% 1.55/0.59    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.55/0.59    inference(ennf_transformation,[],[f4])).
% 1.55/0.59  fof(f4,axiom,(
% 1.55/0.59    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 1.55/0.59  fof(f122,plain,(
% 1.55/0.59    ( ! [X5] : (r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X5),k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f121,f40])).
% 1.55/0.59  fof(f121,plain,(
% 1.55/0.59    ( ! [X5] : (r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X5),k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f120,f41])).
% 1.55/0.59  fof(f120,plain,(
% 1.55/0.59    ( ! [X5] : (r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X5),k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f119,f42])).
% 1.55/0.59  fof(f119,plain,(
% 1.55/0.59    ( ! [X5] : (r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X5),k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f118,f43])).
% 1.55/0.59  fof(f118,plain,(
% 1.55/0.59    ( ! [X5] : (r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X5),k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f86,f44])).
% 1.55/0.59  fof(f86,plain,(
% 1.55/0.59    ( ! [X5] : (r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK1),X5),k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(resolution,[],[f75,f66])).
% 1.55/0.59  fof(f66,plain,(
% 1.55/0.59    ( ! [X2,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | r2_hidden(sK3(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | r2_hidden(X3,a_2_1_orders_2(X1,X2)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.55/0.59    inference(equality_resolution,[],[f54])).
% 1.55/0.59  fof(f54,plain,(
% 1.55/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_hidden(sK3(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f35])).
% 1.55/0.59  fof(f35,plain,(
% 1.55/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,X3,sK3(X1,X2,X3)) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.55/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f32,f34,f33])).
% 1.55/0.59  fof(f33,plain,(
% 1.55/0.59    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,X3,sK3(X1,X2,X3)) & r2_hidden(sK3(X1,X2,X3),X2) & m1_subset_1(sK3(X1,X2,X3),u1_struct_0(X1))))),
% 1.55/0.59    introduced(choice_axiom,[])).
% 1.55/0.59  fof(f34,plain,(
% 1.55/0.59    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK4(X0,X1,X2) = X0 & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X1))))),
% 1.55/0.59    introduced(choice_axiom,[])).
% 1.55/0.59  fof(f32,plain,(
% 1.55/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X5,X6) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.55/0.59    inference(rectify,[],[f31])).
% 1.55/0.59  fof(f31,plain,(
% 1.55/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.55/0.59    inference(nnf_transformation,[],[f16])).
% 1.55/0.59  fof(f16,plain,(
% 1.55/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.55/0.59    inference(flattening,[],[f15])).
% 1.55/0.59  fof(f15,plain,(
% 1.55/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.55/0.59    inference(ennf_transformation,[],[f5])).
% 1.55/0.59  fof(f5,axiom,(
% 1.55/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 1.55/0.59  fof(f48,plain,(
% 1.55/0.59    ~r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~r2_orders_2(sK0,sK1,sK2)),
% 1.55/0.59    inference(cnf_transformation,[],[f30])).
% 1.55/0.59  fof(f620,plain,(
% 1.55/0.59    r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))),
% 1.55/0.59    inference(subsumption_resolution,[],[f619,f260])).
% 1.55/0.59  fof(f260,plain,(
% 1.55/0.59    r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) | r2_orders_2(sK0,sK1,sK2)),
% 1.55/0.59    inference(backward_demodulation,[],[f47,f259])).
% 1.55/0.59  fof(f47,plain,(
% 1.55/0.59    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK1,sK2)),
% 1.55/0.59    inference(cnf_transformation,[],[f30])).
% 1.55/0.59  fof(f619,plain,(
% 1.55/0.59    r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) | ~r2_orders_2(sK0,sK1,sK2)),
% 1.55/0.59    inference(forward_demodulation,[],[f618,f265])).
% 1.55/0.59  fof(f265,plain,(
% 1.55/0.59    k2_orders_2(sK0,k1_tarski(sK2)) = a_2_1_orders_2(sK0,k1_tarski(sK2))),
% 1.55/0.59    inference(backward_demodulation,[],[f137,f259])).
% 1.55/0.59  fof(f137,plain,(
% 1.55/0.59    k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))),
% 1.55/0.59    inference(subsumption_resolution,[],[f136,f40])).
% 1.55/0.59  fof(f136,plain,(
% 1.55/0.59    k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f135,f41])).
% 1.55/0.59  fof(f135,plain,(
% 1.55/0.59    k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f134,f42])).
% 1.55/0.59  fof(f134,plain,(
% 1.55/0.59    k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f133,f43])).
% 1.55/0.59  fof(f133,plain,(
% 1.55/0.59    k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f125,f44])).
% 1.55/0.59  fof(f125,plain,(
% 1.55/0.59    k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(resolution,[],[f80,f61])).
% 1.55/0.59  fof(f80,plain,(
% 1.55/0.59    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.59    inference(subsumption_resolution,[],[f79,f40])).
% 1.55/0.59  fof(f79,plain,(
% 1.55/0.59    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f78,f41])).
% 1.55/0.59  fof(f78,plain,(
% 1.55/0.59    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f76,f44])).
% 1.55/0.59  fof(f76,plain,(
% 1.55/0.59    m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(resolution,[],[f46,f63])).
% 1.55/0.59  fof(f618,plain,(
% 1.55/0.59    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))),
% 1.55/0.59    inference(subsumption_resolution,[],[f617,f40])).
% 1.55/0.59  fof(f617,plain,(
% 1.55/0.59    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f616,f41])).
% 1.55/0.59  fof(f616,plain,(
% 1.55/0.59    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f615,f42])).
% 1.55/0.59  fof(f615,plain,(
% 1.55/0.59    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f614,f43])).
% 1.55/0.59  fof(f614,plain,(
% 1.55/0.59    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f613,f44])).
% 1.55/0.59  fof(f613,plain,(
% 1.55/0.59    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f612,f262])).
% 1.55/0.59  fof(f262,plain,(
% 1.55/0.59    m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.55/0.59    inference(backward_demodulation,[],[f80,f259])).
% 1.55/0.59  fof(f612,plain,(
% 1.55/0.59    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(subsumption_resolution,[],[f611,f45])).
% 1.55/0.59  fof(f611,plain,(
% 1.55/0.59    ~r2_orders_2(sK0,sK1,sK2) | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 1.55/0.59    inference(superposition,[],[f65,f606])).
% 1.55/0.59  fof(f606,plain,(
% 1.55/0.59    sK2 = sK3(sK0,k1_tarski(sK2),sK1)),
% 1.55/0.59    inference(subsumption_resolution,[],[f605,f498])).
% 1.55/0.59  fof(f498,plain,(
% 1.55/0.59    ~r2_orders_2(sK0,sK1,sK2) | sK2 = sK3(sK0,k1_tarski(sK2),sK1)),
% 1.55/0.59    inference(resolution,[],[f492,f261])).
% 1.55/0.59  fof(f492,plain,(
% 1.55/0.59    r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) | sK2 = sK3(sK0,k1_tarski(sK2),sK1)),
% 1.55/0.59    inference(resolution,[],[f305,f70])).
% 1.55/0.59  fof(f70,plain,(
% 1.55/0.59    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.55/0.59    inference(equality_resolution,[],[f56])).
% 1.55/0.59  fof(f56,plain,(
% 1.55/0.59    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.55/0.59    inference(cnf_transformation,[],[f39])).
% 1.55/0.59  fof(f39,plain,(
% 1.55/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f37,f38])).
% 1.55/0.59  fof(f38,plain,(
% 1.55/0.59    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.55/0.59    introduced(choice_axiom,[])).
% 1.55/0.59  fof(f37,plain,(
% 1.55/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.59    inference(rectify,[],[f36])).
% 1.55/0.59  fof(f36,plain,(
% 1.55/0.59    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.55/0.59    inference(nnf_transformation,[],[f1])).
% 1.55/0.59  fof(f1,axiom,(
% 1.55/0.59    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.55/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.55/0.59  fof(f305,plain,(
% 1.55/0.59    r2_hidden(sK3(sK0,k1_tarski(sK2),sK1),k1_tarski(sK2)) | r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))),
% 1.55/0.59    inference(forward_demodulation,[],[f281,f259])).
% 1.55/0.59  fof(f281,plain,(
% 1.55/0.59    r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) | r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),sK1),k6_domain_1(u1_struct_0(sK0),sK2))),
% 1.55/0.59    inference(backward_demodulation,[],[f242,f259])).
% 1.55/0.59  fof(f242,plain,(
% 1.55/0.59    r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),sK1),k6_domain_1(u1_struct_0(sK0),sK2)) | r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))),
% 1.55/0.59    inference(resolution,[],[f167,f45])).
% 1.55/0.59  fof(f167,plain,(
% 1.55/0.59    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),X5),k6_domain_1(u1_struct_0(sK0),sK2)) | r2_hidden(X5,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))) )),
% 1.55/0.59    inference(forward_demodulation,[],[f166,f137])).
% 1.55/0.59  fof(f166,plain,(
% 1.55/0.59    ( ! [X5] : (r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),X5),k6_domain_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f165,f40])).
% 1.55/0.59  fof(f165,plain,(
% 1.55/0.59    ( ! [X5] : (r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),X5),k6_domain_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f164,f41])).
% 1.55/0.59  fof(f164,plain,(
% 1.55/0.59    ( ! [X5] : (r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),X5),k6_domain_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f163,f42])).
% 1.55/0.59  fof(f163,plain,(
% 1.55/0.59    ( ! [X5] : (r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),X5),k6_domain_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f162,f43])).
% 1.55/0.59  fof(f162,plain,(
% 1.55/0.59    ( ! [X5] : (r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),X5),k6_domain_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f130,f44])).
% 1.55/0.59  fof(f130,plain,(
% 1.55/0.59    ( ! [X5] : (r2_hidden(sK3(sK0,k6_domain_1(u1_struct_0(sK0),sK2),X5),k6_domain_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | r2_hidden(X5,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(resolution,[],[f80,f66])).
% 1.55/0.59  fof(f605,plain,(
% 1.55/0.59    r2_orders_2(sK0,sK1,sK2) | sK2 = sK3(sK0,k1_tarski(sK2),sK1)),
% 1.55/0.59    inference(duplicate_literal_removal,[],[f604])).
% 1.55/0.59  fof(f604,plain,(
% 1.55/0.59    r2_orders_2(sK0,sK1,sK2) | r2_orders_2(sK0,sK1,sK2) | sK2 = sK3(sK0,k1_tarski(sK2),sK1)),
% 1.55/0.59    inference(superposition,[],[f602,f499])).
% 1.55/0.59  fof(f499,plain,(
% 1.55/0.59    sK1 = sK4(sK1,sK0,k1_tarski(sK2)) | sK2 = sK3(sK0,k1_tarski(sK2),sK1)),
% 1.55/0.59    inference(resolution,[],[f492,f288])).
% 1.55/0.59  fof(f288,plain,(
% 1.55/0.59    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k1_tarski(sK2))) | sK4(X1,sK0,k1_tarski(sK2)) = X1) )),
% 1.55/0.59    inference(forward_demodulation,[],[f267,f259])).
% 1.55/0.59  fof(f267,plain,(
% 1.55/0.59    ( ! [X1] : (sK4(X1,sK0,k1_tarski(sK2)) = X1 | ~r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))) )),
% 1.55/0.59    inference(backward_demodulation,[],[f149,f259])).
% 1.55/0.59  fof(f149,plain,(
% 1.55/0.59    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | sK4(X1,sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = X1) )),
% 1.55/0.59    inference(forward_demodulation,[],[f148,f137])).
% 1.55/0.59  fof(f148,plain,(
% 1.55/0.59    ( ! [X1] : (~r2_hidden(X1,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | sK4(X1,sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = X1) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f147,f40])).
% 1.55/0.59  fof(f147,plain,(
% 1.55/0.59    ( ! [X1] : (~r2_hidden(X1,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | sK4(X1,sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = X1 | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f146,f41])).
% 1.55/0.59  fof(f146,plain,(
% 1.55/0.59    ( ! [X1] : (~r2_hidden(X1,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | sK4(X1,sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = X1 | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f145,f42])).
% 1.55/0.59  fof(f145,plain,(
% 1.55/0.59    ( ! [X1] : (~r2_hidden(X1,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | sK4(X1,sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = X1 | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f144,f43])).
% 1.55/0.59  fof(f144,plain,(
% 1.55/0.59    ( ! [X1] : (~r2_hidden(X1,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | sK4(X1,sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = X1 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f127,f44])).
% 1.55/0.59  fof(f127,plain,(
% 1.55/0.59    ( ! [X1] : (~r2_hidden(X1,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | sK4(X1,sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = X1 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(resolution,[],[f80,f51])).
% 1.55/0.59  fof(f51,plain,(
% 1.55/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | sK4(X0,X1,X2) = X0 | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f35])).
% 1.55/0.59  fof(f602,plain,(
% 1.55/0.59    r2_orders_2(sK0,sK4(sK1,sK0,k1_tarski(sK2)),sK2) | r2_orders_2(sK0,sK1,sK2)),
% 1.55/0.59    inference(subsumption_resolution,[],[f597,f69])).
% 1.55/0.59  fof(f69,plain,(
% 1.55/0.59    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.55/0.59    inference(equality_resolution,[],[f68])).
% 1.55/0.59  fof(f68,plain,(
% 1.55/0.59    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.55/0.59    inference(equality_resolution,[],[f57])).
% 1.55/0.59  fof(f57,plain,(
% 1.55/0.59    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.55/0.59    inference(cnf_transformation,[],[f39])).
% 1.55/0.59  fof(f597,plain,(
% 1.55/0.59    ~r2_hidden(sK2,k1_tarski(sK2)) | r2_orders_2(sK0,sK4(sK1,sK0,k1_tarski(sK2)),sK2) | r2_orders_2(sK0,sK1,sK2)),
% 1.55/0.59    inference(resolution,[],[f515,f46])).
% 1.55/0.59  fof(f515,plain,(
% 1.55/0.59    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,k1_tarski(sK2)) | r2_orders_2(sK0,sK4(sK1,sK0,k1_tarski(sK2)),X1) | r2_orders_2(sK0,sK1,sK2)) )),
% 1.55/0.59    inference(resolution,[],[f290,f260])).
% 1.55/0.59  fof(f290,plain,(
% 1.55/0.59    ( ! [X2,X3] : (~r2_hidden(X3,k2_orders_2(sK0,k1_tarski(sK2))) | r2_orders_2(sK0,sK4(X3,sK0,k1_tarski(sK2)),X2) | ~r2_hidden(X2,k1_tarski(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0))) )),
% 1.55/0.59    inference(forward_demodulation,[],[f289,f259])).
% 1.55/0.59  fof(f289,plain,(
% 1.55/0.59    ( ! [X2,X3] : (~r2_hidden(X3,k2_orders_2(sK0,k1_tarski(sK2))) | ~r2_hidden(X2,k1_tarski(sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2)) )),
% 1.55/0.59    inference(forward_demodulation,[],[f268,f259])).
% 1.55/0.59  fof(f268,plain,(
% 1.55/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k1_tarski(sK2)) | ~r2_hidden(X3,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2)) )),
% 1.55/0.59    inference(backward_demodulation,[],[f155,f259])).
% 1.55/0.59  fof(f155,plain,(
% 1.55/0.59    ( ! [X2,X3] : (~r2_hidden(X3,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | ~r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2)) )),
% 1.55/0.59    inference(forward_demodulation,[],[f154,f137])).
% 1.55/0.59  fof(f154,plain,(
% 1.55/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f153,f40])).
% 1.55/0.59  fof(f153,plain,(
% 1.55/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f152,f41])).
% 1.55/0.59  fof(f152,plain,(
% 1.55/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f151,f42])).
% 1.55/0.59  fof(f151,plain,(
% 1.55/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f150,f43])).
% 1.55/0.59  fof(f150,plain,(
% 1.55/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(subsumption_resolution,[],[f128,f44])).
% 1.55/0.59  fof(f128,plain,(
% 1.55/0.59    ( ! [X2,X3] : (~r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),sK2)) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X3,a_2_1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) | r2_orders_2(sK0,sK4(X3,sK0,k6_domain_1(u1_struct_0(sK0),sK2)),X2) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) )),
% 1.55/0.59    inference(resolution,[],[f80,f52])).
% 1.55/0.59  fof(f52,plain,(
% 1.55/0.59    ( ! [X6,X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)) | r2_orders_2(X1,sK4(X0,X1,X2),X6) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f35])).
% 1.55/0.59  fof(f65,plain,(
% 1.55/0.59    ( ! [X2,X3,X1] : (~r2_orders_2(X1,X3,sK3(X1,X2,X3)) | r2_hidden(X3,a_2_1_orders_2(X1,X2)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.55/0.59    inference(equality_resolution,[],[f55])).
% 1.55/0.59  fof(f55,plain,(
% 1.55/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~r2_orders_2(X1,X3,sK3(X1,X2,X3)) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.55/0.59    inference(cnf_transformation,[],[f35])).
% 1.55/0.59  fof(f675,plain,(
% 1.55/0.59    r2_orders_2(sK0,sK1,sK2)),
% 1.55/0.59    inference(duplicate_literal_removal,[],[f672])).
% 1.55/0.59  fof(f672,plain,(
% 1.55/0.59    r2_orders_2(sK0,sK1,sK2) | r2_orders_2(sK0,sK1,sK2)),
% 1.55/0.59    inference(backward_demodulation,[],[f602,f666])).
% 1.55/0.59  fof(f666,plain,(
% 1.55/0.59    sK1 = sK4(sK1,sK0,k1_tarski(sK2))),
% 1.55/0.59    inference(resolution,[],[f620,f288])).
% 1.55/0.59  % SZS output end Proof for theBenchmark
% 1.55/0.59  % (31193)------------------------------
% 1.55/0.59  % (31193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.55/0.59  % (31193)Termination reason: Refutation
% 1.55/0.59  
% 1.55/0.59  % (31193)Memory used [KB]: 2046
% 1.55/0.59  % (31193)Time elapsed: 0.171 s
% 1.55/0.59  % (31193)------------------------------
% 1.55/0.59  % (31193)------------------------------
% 1.78/0.59  % (31178)Success in time 0.224 s
%------------------------------------------------------------------------------
