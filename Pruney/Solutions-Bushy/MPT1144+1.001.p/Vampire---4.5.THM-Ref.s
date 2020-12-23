%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1144+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:21 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :  283 (223551 expanded)
%              Number of leaves         :   18 (68311 expanded)
%              Depth                    :  132
%              Number of atoms          : 1204 (2299025 expanded)
%              Number of equality atoms :  238 (56556 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1030,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1029,f57])).

fof(f57,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ( ~ r3_orders_2(sK0,sK2,sK1)
        & ~ r3_orders_2(sK0,sK1,sK2) )
      | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) )
    & ( r3_orders_2(sK0,sK2,sK1)
      | r3_orders_2(sK0,sK1,sK2)
      | ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        & v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ( ~ r3_orders_2(X0,X2,X1)
                    & ~ r3_orders_2(X0,X1,X2) )
                  | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
                & ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2)
                  | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r3_orders_2(sK0,X2,X1)
                  & ~ r3_orders_2(sK0,X1,X2) )
                | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
                | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),X1,X2),sK0) )
              & ( r3_orders_2(sK0,X2,X1)
                | r3_orders_2(sK0,X1,X2)
                | ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(sK0),X1,X2),sK0) ) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ( ~ r3_orders_2(sK0,X2,X1)
                & ~ r3_orders_2(sK0,X1,X2) )
              | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
              | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),X1,X2),sK0) )
            & ( r3_orders_2(sK0,X2,X1)
              | r3_orders_2(sK0,X1,X2)
              | ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
                & v6_orders_2(k7_domain_1(u1_struct_0(sK0),X1,X2),sK0) ) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ( ~ r3_orders_2(sK0,X2,sK1)
              & ~ r3_orders_2(sK0,sK1,X2) )
            | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
            | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,X2),sK0) )
          & ( r3_orders_2(sK0,X2,sK1)
            | r3_orders_2(sK0,sK1,X2)
            | ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
              & v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,X2),sK0) ) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ( ( ~ r3_orders_2(sK0,X2,sK1)
            & ~ r3_orders_2(sK0,sK1,X2) )
          | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
          | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,X2),sK0) )
        & ( r3_orders_2(sK0,X2,sK1)
          | r3_orders_2(sK0,sK1,X2)
          | ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
            & v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,X2),sK0) ) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ( ~ r3_orders_2(sK0,sK2,sK1)
          & ~ r3_orders_2(sK0,sK1,sK2) )
        | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) )
      & ( r3_orders_2(sK0,sK2,sK1)
        | r3_orders_2(sK0,sK1,sK2)
        | ( m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
          & v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r3_orders_2(X0,X2,X1)
                  & ~ r3_orders_2(X0,X1,X2) )
                | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              & ( r3_orders_2(X0,X2,X1)
                | r3_orders_2(X0,X1,X2)
                | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( ~ r3_orders_2(X0,X2,X1)
                  & ~ r3_orders_2(X0,X1,X2) )
                | ~ m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                | ~ v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              & ( r3_orders_2(X0,X2,X1)
                | r3_orders_2(X0,X1,X2)
                | ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <~> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <~> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                    & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
                <=> ( r3_orders_2(X0,X2,X1)
                    | r3_orders_2(X0,X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( m1_subset_1(k7_domain_1(u1_struct_0(X0),X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
                  & v6_orders_2(k7_domain_1(u1_struct_0(X0),X1,X2),X0) )
              <=> ( r3_orders_2(X0,X2,X1)
                  | r3_orders_2(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_orders_2)).

fof(f1029,plain,(
    ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f1028,f69])).

fof(f69,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f1028,plain,(
    ~ l1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1027,f55])).

fof(f55,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f1027,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f1026,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f1026,plain,(
    v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1025,f139])).

fof(f139,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f138,f58])).

fof(f58,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f138,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f137,f59])).

fof(f59,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f137,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f78,f135])).

fof(f135,plain,(
    k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f134,f57])).

fof(f134,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f133,f69])).

fof(f133,plain,
    ( ~ l1_struct_0(sK0)
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ),
    inference(subsumption_resolution,[],[f132,f55])).

fof(f132,plain,
    ( k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f120,f75])).

fof(f120,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k7_domain_1(u1_struct_0(sK0),sK1,sK2) = k2_tarski(sK1,sK2) ),
    inference(resolution,[],[f114,f59])).

fof(f114,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k7_domain_1(u1_struct_0(sK0),sK1,X0) = k2_tarski(sK1,X0)
      | v1_xboole_0(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f79,f58])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | ~ m1_subset_1(X2,X0)
      | k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k7_domain_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_domain_1)).

fof(f1025,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f1023,f1011])).

fof(f1011,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    inference(subsumption_resolution,[],[f1009,f57])).

fof(f1009,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f1008,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r7_relat_2(u1_orders_2(X0),X1)
      | v6_orders_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_orders_2(X1,X0)
              | ~ r7_relat_2(u1_orders_2(X0),X1) )
            & ( r7_relat_2(u1_orders_2(X0),X1)
              | ~ v6_orders_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_orders_2(X1,X0)
          <=> r7_relat_2(u1_orders_2(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d11_orders_2)).

fof(f1008,plain,(
    r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f1007,f58])).

fof(f1007,plain,
    ( r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f990,f247])).

fof(f247,plain,(
    ! [X0] :
      ( r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f246,f57])).

fof(f246,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(duplicate_literal_removal,[],[f245])).

fof(f245,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r2_hidden(k4_tarski(X0,X0),u1_orders_2(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f244,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
                & ( r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
                  | ~ r1_orders_2(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_orders_2(X0,X1,X2)
              <=> r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_orders_2)).

fof(f244,plain,(
    ! [X0] :
      ( r1_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f243,f55])).

fof(f243,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f242,f56])).

fof(f56,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f242,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f241,f57])).

fof(f241,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X0)
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f239,f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r3_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(condensation,[],[f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f238,f55])).

fof(f238,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_orders_2(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f237,f57])).

fof(f237,plain,(
    ! [X0,X1] :
      ( ~ r3_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r1_orders_2(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f81,f56])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f990,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK1),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f941,f978])).

fof(f978,plain,(
    sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f977,f57])).

fof(f977,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f976,f69])).

fof(f976,plain,
    ( ~ l1_struct_0(sK0)
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f975,f55])).

fof(f975,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f973,f75])).

fof(f973,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f972,f139])).

fof(f972,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f971,f962])).

fof(f962,plain,
    ( ~ v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f960,f139])).

fof(f960,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    inference(resolution,[],[f956,f232])).

fof(f232,plain,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f231,f135])).

fof(f231,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r3_orders_2(sK0,sK1,sK2)
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f62,f135])).

fof(f62,plain,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f956,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f955,f58])).

fof(f955,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f953,f59])).

fof(f953,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f952,f252])).

fof(f252,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,X0,X1) ) ),
    inference(subsumption_resolution,[],[f251,f55])).

fof(f251,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r3_orders_2(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f250,f57])).

fof(f250,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK0,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | r3_orders_2(sK0,X0,X1)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f82,f56])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_orders_2(X0)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r3_orders_2(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f952,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f950,f139])).

fof(f950,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_orders_2(sK0,sK1,sK2)
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f949,f542])).

fof(f542,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_orders_2(sK0,sK1,sK2)
    | ~ v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    inference(resolution,[],[f538,f234])).

fof(f234,plain,
    ( ~ r3_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f233,f135])).

fof(f233,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r3_orders_2(sK0,sK2,sK1)
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(forward_demodulation,[],[f63,f135])).

fof(f63,plain,
    ( ~ r3_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f538,plain,
    ( r3_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f537,f59])).

fof(f537,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f535,f58])).

fof(f535,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f534,f252])).

fof(f534,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f533,f58])).

fof(f533,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f532,f59])).

fof(f532,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f531])).

fof(f531,plain,
    ( r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f529,f239])).

fof(f529,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f528,f59])).

fof(f528,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f526,f58])).

fof(f526,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f525])).

fof(f525,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f523,f239])).

fof(f523,plain,
    ( r3_orders_2(sK0,sK2,sK1)
    | r3_orders_2(sK0,sK1,sK2)
    | r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f522,f57])).

fof(f522,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f521,f58])).

fof(f521,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f519,f59])).

fof(f519,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f518,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(k4_tarski(X1,X2),u1_orders_2(X0))
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f518,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | r3_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f517,f57])).

fof(f517,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | r3_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK2,sK1)
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f516,f59])).

fof(f516,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | r3_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f514,f58])).

fof(f514,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | r3_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK2,sK1)
    | r1_orders_2(sK0,sK2,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f506,f72])).

fof(f506,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | r3_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK2,sK1) ),
    inference(resolution,[],[f500,f93])).

fof(f93,plain,(
    ! [X4,X1] : r2_hidden(X4,k2_tarski(X4,X1)) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X4,X2,X1] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X4,X1) != X2 ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f52,f53])).

fof(f53,plain,(
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

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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
    inference(flattening,[],[f50])).

fof(f50,plain,(
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
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f500,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_tarski(sK1,sK2))
      | r2_hidden(k4_tarski(sK2,X0),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X0,sK2),u1_orders_2(sK0))
      | r3_orders_2(sK0,sK1,sK2)
      | r3_orders_2(sK0,sK2,sK1) ) ),
    inference(resolution,[],[f257,f91])).

fof(f91,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f257,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(sK1,sK2))
      | ~ r2_hidden(X0,k2_tarski(sK1,sK2))
      | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | r3_orders_2(sK0,sK1,sK2)
      | r3_orders_2(sK0,sK2,sK1) ) ),
    inference(resolution,[],[f235,f181])).

fof(f181,plain,
    ( r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | r3_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK2,sK1) ),
    inference(subsumption_resolution,[],[f180,f136])).

fof(f136,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | r3_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK2,sK1) ),
    inference(superposition,[],[f60,f135])).

fof(f60,plain,
    ( v6_orders_2(k7_domain_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | r3_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK2,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f180,plain,
    ( r3_orders_2(sK0,sK2,sK1)
    | r3_orders_2(sK0,sK1,sK2)
    | ~ v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f177,f57])).

fof(f177,plain,
    ( r3_orders_2(sK0,sK2,sK1)
    | r3_orders_2(sK0,sK1,sK2)
    | ~ v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f176,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X1,X0)
      | r7_relat_2(u1_orders_2(X0),X1)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f176,plain,
    ( m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r3_orders_2(sK0,sK2,sK1)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(forward_demodulation,[],[f61,f135])).

fof(f61,plain,
    ( r3_orders_2(sK0,sK2,sK1)
    | r3_orders_2(sK0,sK1,sK2)
    | m1_subset_1(k7_domain_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( ~ r7_relat_2(u1_orders_2(sK0),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2)
      | r2_hidden(k4_tarski(X0,X1),u1_orders_2(sK0))
      | r2_hidden(k4_tarski(X1,X0),u1_orders_2(sK0)) ) ),
    inference(resolution,[],[f64,f101])).

fof(f101,plain,(
    v1_relat_1(u1_orders_2(sK0)) ),
    inference(resolution,[],[f100,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f100,plain,(
    m1_subset_1(u1_orders_2(sK0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)))) ),
    inference(resolution,[],[f70,f57])).

fof(f70,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0))))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(u1_orders_2(X0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_orders_2)).

fof(f64,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(k4_tarski(X4,X5),X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X1)
      | ~ r7_relat_2(X0,X1)
      | r2_hidden(k4_tarski(X5,X4),X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
              & ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
              & r2_hidden(sK4(X0,X1),X1)
              & r2_hidden(sK3(X0,X1),X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f44,f45])).

fof(f45,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ~ r2_hidden(k4_tarski(X3,X2),X0)
          & ~ r2_hidden(k4_tarski(X2,X3),X0)
          & r2_hidden(X3,X1)
          & r2_hidden(X2,X1) )
     => ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
        & ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
        & r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X4,X5] :
                ( r2_hidden(k4_tarski(X5,X4),X0)
                | r2_hidden(k4_tarski(X4,X5),X0)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r7_relat_2(X0,X1)
            | ? [X2,X3] :
                ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) )
          & ( ! [X2,X3] :
                ( r2_hidden(k4_tarski(X3,X2),X0)
                | r2_hidden(k4_tarski(X2,X3),X0)
                | ~ r2_hidden(X3,X1)
                | ~ r2_hidden(X2,X1) )
            | ~ r7_relat_2(X0,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ( r2_hidden(k4_tarski(X3,X2),X0)
              | r2_hidden(k4_tarski(X2,X3),X0)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X2,X1) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r7_relat_2(X0,X1)
        <=> ! [X2,X3] :
              ~ ( ~ r2_hidden(k4_tarski(X3,X2),X0)
                & ~ r2_hidden(k4_tarski(X2,X3),X0)
                & r2_hidden(X3,X1)
                & r2_hidden(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_relat_2)).

fof(f949,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f947,f57])).

fof(f947,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f945,f74])).

fof(f945,plain,
    ( r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f919,f541])).

fof(f541,plain,
    ( r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f540,f57])).

fof(f540,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f539,f59])).

fof(f539,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f536,f58])).

fof(f536,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f534,f71])).

fof(f919,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f603,f917])).

fof(f917,plain,(
    sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f916,f57])).

fof(f916,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f915,f69])).

fof(f915,plain,
    ( ~ l1_struct_0(sK0)
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f914,f55])).

fof(f914,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f912,f75])).

fof(f912,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f911,f139])).

fof(f911,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f910,f901])).

fof(f901,plain,
    ( ~ v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f899,f139])).

fof(f899,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    inference(resolution,[],[f895,f232])).

fof(f895,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f894,f58])).

fof(f894,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f892,f59])).

fof(f892,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f891,f252])).

fof(f891,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f889,f139])).

fof(f889,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_orders_2(sK0,sK1,sK2)
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f888,f542])).

fof(f888,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f886,f57])).

fof(f886,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | r1_orders_2(sK0,sK1,sK2)
    | v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f884,f74])).

fof(f884,plain,
    ( r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | r1_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f873,f541])).

fof(f873,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f858])).

fof(f858,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK1),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f589,f854])).

fof(f854,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f853,f57])).

fof(f853,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f852,f69])).

fof(f852,plain,
    ( ~ l1_struct_0(sK0)
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f851,f55])).

fof(f851,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f850,f75])).

fof(f850,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f849,f139])).

fof(f849,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f847,f835])).

fof(f835,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f833,f57])).

fof(f833,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f832,f74])).

fof(f832,plain,
    ( r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f831,f59])).

fof(f831,plain,
    ( r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(resolution,[],[f614,f247])).

fof(f614,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK2),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f588,f597])).

fof(f597,plain,
    ( sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f596,f57])).

fof(f596,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f595,f69])).

fof(f595,plain,
    ( ~ l1_struct_0(sK0)
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f594,f55])).

fof(f594,plain,
    ( sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f593,f75])).

fof(f593,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f592,f139])).

fof(f592,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f590,f263])).

fof(f263,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tarski(X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | sK4(u1_orders_2(sK0),k2_tarski(X0,X1)) = X0
      | v6_orders_2(k2_tarski(X0,X1),sK0)
      | sK4(u1_orders_2(sK0),k2_tarski(X0,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f259,f57])).

fof(f259,plain,(
    ! [X0,X1] :
      ( sK4(u1_orders_2(sK0),k2_tarski(X0,X1)) = X1
      | sK4(u1_orders_2(sK0),k2_tarski(X0,X1)) = X0
      | v6_orders_2(k2_tarski(X0,X1),sK0)
      | ~ m1_subset_1(k2_tarski(X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f107,f74])).

fof(f107,plain,(
    ! [X4,X5] :
      ( r7_relat_2(u1_orders_2(sK0),k2_tarski(X4,X5))
      | sK4(u1_orders_2(sK0),k2_tarski(X4,X5)) = X5
      | sK4(u1_orders_2(sK0),k2_tarski(X4,X5)) = X4 ) ),
    inference(resolution,[],[f94,f103])).

fof(f103,plain,(
    ! [X0] :
      ( r2_hidden(sK4(u1_orders_2(sK0),X0),X0)
      | r7_relat_2(u1_orders_2(sK0),X0) ) ),
    inference(resolution,[],[f101,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK4(X0,X1),X1)
      | r7_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f590,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    inference(resolution,[],[f571,f232])).

fof(f571,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f570,f58])).

fof(f570,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f568,f59])).

fof(f568,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f560,f252])).

fof(f560,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f549])).

fof(f549,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f547,f372])).

fof(f372,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f263,f139])).

fof(f547,plain,
    ( ~ v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f542,f139])).

fof(f588,plain,
    ( ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK2),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f585,f101])).

fof(f585,plain,
    ( ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK2),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f68,f582])).

fof(f582,plain,
    ( sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f581,f57])).

fof(f581,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f580,f69])).

fof(f580,plain,
    ( ~ l1_struct_0(sK0)
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f579,f55])).

fof(f579,plain,
    ( sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f578,f75])).

fof(f578,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f577,f139])).

fof(f577,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f575,f268])).

fof(f268,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k2_tarski(X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | sK3(u1_orders_2(sK0),k2_tarski(X0,X1)) = X0
      | v6_orders_2(k2_tarski(X0,X1),sK0)
      | sK3(u1_orders_2(sK0),k2_tarski(X0,X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f264,f57])).

fof(f264,plain,(
    ! [X0,X1] :
      ( sK3(u1_orders_2(sK0),k2_tarski(X0,X1)) = X1
      | sK3(u1_orders_2(sK0),k2_tarski(X0,X1)) = X0
      | v6_orders_2(k2_tarski(X0,X1),sK0)
      | ~ m1_subset_1(k2_tarski(X0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0) ) ),
    inference(resolution,[],[f108,f74])).

fof(f108,plain,(
    ! [X6,X7] :
      ( r7_relat_2(u1_orders_2(sK0),k2_tarski(X6,X7))
      | sK3(u1_orders_2(sK0),k2_tarski(X6,X7)) = X7
      | sK3(u1_orders_2(sK0),k2_tarski(X6,X7)) = X6 ) ),
    inference(resolution,[],[f94,f104])).

fof(f104,plain,(
    ! [X1] :
      ( r2_hidden(sK3(u1_orders_2(sK0),X1),X1)
      | r7_relat_2(u1_orders_2(sK0),X1) ) ),
    inference(resolution,[],[f101,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | r2_hidden(sK3(X0,X1),X1)
      | r7_relat_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f575,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    inference(resolution,[],[f564,f232])).

fof(f564,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f563,f58])).

fof(f563,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f561,f59])).

fof(f561,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f559,f252])).

fof(f559,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f550])).

fof(f550,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f547,f388])).

fof(f388,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK2 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f268,f139])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK4(X0,X1),sK3(X0,X1)),X0)
      | r7_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f847,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    inference(resolution,[],[f843,f232])).

fof(f843,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f842,f58])).

fof(f842,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f840,f59])).

fof(f840,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f839,f252])).

fof(f839,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f838])).

fof(f838,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f837,f547])).

fof(f837,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f835,f139])).

fof(f589,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f586,f101])).

fof(f586,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f67,f582])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X0)
      | r7_relat_2(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f910,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f908,f57])).

fof(f908,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f907,f74])).

fof(f907,plain,
    ( r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f905])).

fof(f905,plain,
    ( r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(resolution,[],[f874,f898])).

fof(f898,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f897,f57])).

fof(f897,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f896,f58])).

fof(f896,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f893,f59])).

fof(f893,plain,
    ( sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f891,f71])).

fof(f874,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(duplicate_literal_removal,[],[f857])).

fof(f857,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f588,f854])).

fof(f603,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f600,f101])).

fof(f600,plain,
    ( ~ r2_hidden(k4_tarski(sK2,sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2))),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f68,f597])).

fof(f971,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f969,f57])).

fof(f969,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f968,f74])).

fof(f968,plain,
    ( r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f966])).

fof(f966,plain,
    ( r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(resolution,[],[f920,f959])).

fof(f959,plain,
    ( r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f958,f57])).

fof(f958,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f957,f58])).

fof(f957,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f954,f59])).

fof(f954,plain,
    ( sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f952,f71])).

fof(f920,plain,
    ( ~ r2_hidden(k4_tarski(sK1,sK2),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f604,f917])).

fof(f604,plain,
    ( ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK2),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f601,f101])).

fof(f601,plain,
    ( ~ r2_hidden(k4_tarski(sK3(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK2),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ v1_relat_1(u1_orders_2(sK0))
    | sK1 = sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(superposition,[],[f67,f597])).

fof(f941,plain,
    ( ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK1),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f932,f101])).

fof(f932,plain,
    ( ~ r2_hidden(k4_tarski(sK4(u1_orders_2(sK0),k2_tarski(sK1,sK2)),sK1),u1_orders_2(sK0))
    | r7_relat_2(u1_orders_2(sK0),k2_tarski(sK1,sK2))
    | ~ v1_relat_1(u1_orders_2(sK0)) ),
    inference(superposition,[],[f68,f917])).

fof(f1023,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v6_orders_2(k2_tarski(sK1,sK2),sK0) ),
    inference(resolution,[],[f1019,f232])).

fof(f1019,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1018,f58])).

fof(f1018,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f1016,f59])).

fof(f1016,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(resolution,[],[f1015,f252])).

fof(f1015,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(duplicate_literal_removal,[],[f1014])).

fof(f1014,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r1_orders_2(sK0,sK1,sK2)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f1013,f547])).

fof(f1013,plain,
    ( v6_orders_2(k2_tarski(sK1,sK2),sK0)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f1011,f139])).

%------------------------------------------------------------------------------
