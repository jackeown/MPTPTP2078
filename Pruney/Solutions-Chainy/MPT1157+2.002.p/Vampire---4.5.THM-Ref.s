%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:02 EST 2020

% Result     : Theorem 1.62s
% Output     : Refutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :  149 (1787 expanded)
%              Number of leaves         :   22 ( 587 expanded)
%              Depth                    :   25
%              Number of atoms          :  749 (16052 expanded)
%              Number of equality atoms :  105 ( 330 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f638,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f99,f112,f161,f168,f477,f480,f624,f632])).

fof(f632,plain,(
    ~ spl6_7 ),
    inference(avatar_contradiction_clause,[],[f627])).

fof(f627,plain,
    ( $false
    | ~ spl6_7 ),
    inference(resolution,[],[f476,f46])).

fof(f46,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).

fof(f27,plain,
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

fof(f28,plain,
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

fof(f29,plain,
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_orders_2)).

fof(f476,plain,
    ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(sK0))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f475])).

fof(f475,plain,
    ( spl6_7
  <=> ! [X2] : ~ m1_subset_1(X2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f624,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f623])).

fof(f623,plain,
    ( $false
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f622,f185])).

fof(f185,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_1
    | spl6_3 ),
    inference(backward_demodulation,[],[f175,f114])).

fof(f114,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | spl6_3 ),
    inference(resolution,[],[f113,f46])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0) )
    | spl6_3 ),
    inference(resolution,[],[f108,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f65,f67])).

fof(f67,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f65,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f108,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl6_3 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl6_3
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f175,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl6_1 ),
    inference(subsumption_resolution,[],[f49,f94])).

fof(f94,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl6_1
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f49,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).

fof(f622,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_1
    | spl6_3 ),
    inference(forward_demodulation,[],[f621,f508])).

fof(f508,plain,
    ( k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))
    | spl6_3 ),
    inference(backward_demodulation,[],[f188,f114])).

fof(f188,plain,(
    k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f103,f46])).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)) ) ),
    inference(resolution,[],[f88,f87])).

fof(f87,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X6) = a_2_0_orders_2(sK0,X6) ) ),
    inference(global_subsumption,[],[f45,f44,f43,f42,f80])).

fof(f80,plain,(
    ! [X6] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | k1_orders_2(sK0,X6) = a_2_0_orders_2(sK0,X6) ) ),
    inference(resolution,[],[f41,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f42,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f43,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f44,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f88,plain,(
    ! [X7] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),X7),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f45,f42,f81])).

fof(f81,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X7),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f41,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
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
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(f621,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f620,f132])).

fof(f132,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_3 ),
    inference(subsumption_resolution,[],[f131,f46])).

fof(f131,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_3 ),
    inference(superposition,[],[f88,f114])).

fof(f620,plain,
    ( ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f619,f47])).

fof(f47,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f619,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f616,f94])).

fof(f616,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_1
    | spl6_3 ),
    inference(superposition,[],[f89,f605])).

fof(f605,plain,
    ( sK1 = sK4(sK0,k2_tarski(sK1,sK1),sK2)
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f602,f185])).

fof(f602,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | sK1 = sK4(sK0,k2_tarski(sK1,sK1),sK2)
    | spl6_3 ),
    inference(resolution,[],[f525,f47])).

fof(f525,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
        | sK1 = sK4(sK0,k2_tarski(sK1,sK1),X0) )
    | spl6_3 ),
    inference(subsumption_resolution,[],[f524,f132])).

fof(f524,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = sK4(sK0,k2_tarski(sK1,sK1),X0) )
    | spl6_3 ),
    inference(duplicate_literal_removal,[],[f522])).

fof(f522,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | sK1 = sK4(sK0,k2_tarski(sK1,sK1),X0)
        | sK1 = sK4(sK0,k2_tarski(sK1,sK1),X0) )
    | spl6_3 ),
    inference(superposition,[],[f136,f508])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(sK0,k2_tarski(X1,X2)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | sK4(sK0,k2_tarski(X1,X2),X0) = X1
      | sK4(sK0,k2_tarski(X1,X2),X0) = X2 ) ),
    inference(resolution,[],[f90,f73])).

fof(f73,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k2_tarski(X0,X1))
      | X0 = X4
      | X1 = X4 ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( X1 = X4
      | X0 = X4
      | ~ r2_hidden(X4,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ( ( ( sK3(X0,X1,X2) != X1
              & sK3(X0,X1,X2) != X0 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X1
            | sK3(X0,X1,X2) = X0
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X1 != X4
                & X0 != X4 ) )
            & ( X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X2) ) )
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X1 != X3
              & X0 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X1 = X3
            | X0 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X1
            & sK3(X0,X1,X2) != X0 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X1
          | sK3(X0,X1,X2) = X0
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f90,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK4(sK0,X10,X11),X10)
      | r2_hidden(X11,a_2_0_orders_2(sK0,X10))
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f45,f44,f43,f42,f83])).

fof(f83,plain,(
    ! [X10,X11] :
      ( r2_hidden(sK4(sK0,X10,X11),X10)
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | r2_hidden(X11,a_2_0_orders_2(sK0,X10)) ) ),
    inference(resolution,[],[f41,f75])).

fof(f75,plain,(
    ! [X2,X3,X1] :
      ( v2_struct_0(X1)
      | r2_hidden(sK4(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | r2_hidden(X3,a_2_0_orders_2(X1,X2)) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK4(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK4(X1,X2,X3),X3)
                & r2_hidden(sK4(X1,X2,X3),X2)
                & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK5(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK5(X0,X1,X2) = X0
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f37,f39,f38])).

fof(f38,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK4(X1,X2,X3),X3)
        & r2_hidden(sK4(X1,X2,X3),X2)
        & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK5(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK5(X0,X1,X2) = X0
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f89,plain,(
    ! [X8,X9] :
      ( ~ r2_orders_2(sK0,sK4(sK0,X8,X9),X9)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X9,a_2_0_orders_2(sK0,X8)) ) ),
    inference(global_subsumption,[],[f45,f44,f43,f42,f82])).

fof(f82,plain,(
    ! [X8,X9] :
      ( ~ r2_orders_2(sK0,sK4(sK0,X8,X9),X9)
      | ~ m1_subset_1(X9,u1_struct_0(sK0))
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | r2_hidden(X9,a_2_0_orders_2(sK0,X8)) ) ),
    inference(resolution,[],[f41,f74])).

fof(f74,plain,(
    ! [X2,X3,X1] :
      ( v2_struct_0(X1)
      | ~ r2_orders_2(X1,sK4(X1,X2,X3),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | r2_hidden(X3,a_2_0_orders_2(X1,X2)) ) ),
    inference(equality_resolution,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ r2_orders_2(X1,sK4(X1,X2,X3),X3)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f480,plain,(
    spl6_6 ),
    inference(avatar_contradiction_clause,[],[f479])).

fof(f479,plain,
    ( $false
    | spl6_6 ),
    inference(subsumption_resolution,[],[f478,f46])).

fof(f478,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_6 ),
    inference(resolution,[],[f473,f88])).

fof(f473,plain,
    ( ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f471])).

fof(f471,plain,
    ( spl6_6
  <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f477,plain,
    ( ~ spl6_6
    | spl6_7
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f469,f166,f110,f475,f471])).

fof(f110,plain,
    ( spl6_4
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,k1_orders_2(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f166,plain,
    ( spl6_5
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f469,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_4
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f468,f248])).

fof(f248,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl6_4 ),
    inference(resolution,[],[f164,f46])).

fof(f164,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X3))) )
    | ~ spl6_4 ),
    inference(resolution,[],[f111,f88])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,k1_orders_2(sK0,X0)) )
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f468,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f377,f188])).

fof(f377,plain,
    ( ! [X2] :
        ( r2_hidden(X2,a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl6_5 ),
    inference(resolution,[],[f362,f90])).

fof(f362,plain,
    ( ! [X0] : ~ r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ spl6_5 ),
    inference(resolution,[],[f167,f46])).

fof(f167,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),X1)) )
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f166])).

fof(f168,plain,
    ( ~ spl6_3
    | spl6_5 ),
    inference(avatar_split_clause,[],[f104,f166,f106])).

fof(f104,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ v1_xboole_0(u1_struct_0(sK0))
      | ~ r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),X1)) ) ),
    inference(resolution,[],[f88,f50])).

fof(f50,plain,(
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

fof(f161,plain,
    ( ~ spl6_2
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f159,f70])).

fof(f70,plain,(
    ! [X4,X0] : r2_hidden(X4,k2_tarski(X0,X4)) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X4,X2,X0] :
      ( r2_hidden(X4,X2)
      | k2_tarski(X0,X4) != X2 ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f159,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK1))
    | ~ spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f157,f46])).

fof(f157,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK1))
    | ~ spl6_2
    | spl6_3 ),
    inference(resolution,[],[f152,f100])).

fof(f100,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl6_2 ),
    inference(subsumption_resolution,[],[f49,f98])).

fof(f98,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f96])).

fof(f96,plain,
    ( spl6_2
  <=> r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f152,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_tarski(sK1,sK1)) )
    | ~ spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f151,f130])).

fof(f130,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | ~ spl6_2
    | spl6_3 ),
    inference(backward_demodulation,[],[f98,f114])).

fof(f151,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
        | r2_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_tarski(sK1,sK1)) )
    | ~ spl6_2
    | spl6_3 ),
    inference(forward_demodulation,[],[f150,f134])).

fof(f134,plain,
    ( k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))
    | spl6_3 ),
    inference(resolution,[],[f132,f87])).

fof(f150,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
        | ~ r2_hidden(X0,k2_tarski(sK1,sK1)) )
    | ~ spl6_2
    | spl6_3 ),
    inference(subsumption_resolution,[],[f148,f132])).

fof(f148,plain,
    ( ! [X0] :
        ( r2_orders_2(sK0,X0,sK2)
        | ~ m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))
        | ~ r2_hidden(X0,k2_tarski(sK1,sK1)) )
    | ~ spl6_2
    | spl6_3 ),
    inference(superposition,[],[f85,f145])).

fof(f145,plain,
    ( sK2 = sK5(sK2,sK0,k2_tarski(sK1,sK1))
    | ~ spl6_2
    | spl6_3 ),
    inference(resolution,[],[f142,f130])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
        | sK5(X0,sK0,k2_tarski(sK1,sK1)) = X0 )
    | spl6_3 ),
    inference(forward_demodulation,[],[f133,f134])).

fof(f133,plain,
    ( ! [X0] :
        ( sK5(X0,sK0,k2_tarski(sK1,sK1)) = X0
        | ~ r2_hidden(X0,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) )
    | spl6_3 ),
    inference(resolution,[],[f132,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK5(X0,sK0,X1) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) ) ),
    inference(global_subsumption,[],[f45,f44,f43,f42,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | sK5(X0,sK0,X1) = X0 ) ),
    inference(resolution,[],[f41,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | sK5(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f85,plain,(
    ! [X4,X2,X3] :
      ( r2_orders_2(sK0,X2,sK5(X4,sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X4,a_2_0_orders_2(sK0,X3))
      | ~ r2_hidden(X2,X3) ) ),
    inference(global_subsumption,[],[f45,f44,f43,f42,f78])).

fof(f78,plain,(
    ! [X4,X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X4,a_2_0_orders_2(sK0,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | r2_orders_2(sK0,X2,sK5(X4,sK0,X3)) ) ),
    inference(resolution,[],[f41,f59])).

fof(f59,plain,(
    ! [X6,X2,X0,X1] :
      ( v2_struct_0(X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | r2_orders_2(X1,X6,sK5(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f112,plain,
    ( ~ spl6_3
    | spl6_4 ),
    inference(avatar_split_clause,[],[f101,f110,f106])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(u1_struct_0(sK0))
      | ~ r2_hidden(X1,k1_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f86,f50])).

fof(f86,plain,(
    ! [X5] :
      ( m1_subset_1(k1_orders_2(sK0,X5),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f45,f44,f43,f42,f79])).

fof(f79,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | m1_subset_1(k1_orders_2(sK0,X5),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f41,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

fof(f99,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f48,f96,f92])).

fof(f48,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:39:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (1391)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (1377)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (1384)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (1381)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (1382)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (1392)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.52  % (1385)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (1397)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (1399)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (1402)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.54  % (1380)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (1379)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (1406)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (1389)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (1398)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (1378)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (1406)Refutation not found, incomplete strategy% (1406)------------------------------
% 0.22/0.54  % (1406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (1406)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (1406)Memory used [KB]: 1663
% 0.22/0.54  % (1406)Time elapsed: 0.004 s
% 0.22/0.54  % (1406)------------------------------
% 0.22/0.54  % (1406)------------------------------
% 0.22/0.54  % (1390)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (1403)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.54  % (1400)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (1403)Refutation not found, incomplete strategy% (1403)------------------------------
% 0.22/0.55  % (1403)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1403)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (1403)Memory used [KB]: 6268
% 0.22/0.55  % (1403)Time elapsed: 0.128 s
% 0.22/0.55  % (1403)------------------------------
% 0.22/0.55  % (1403)------------------------------
% 0.22/0.55  % (1405)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (1386)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (1404)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (1395)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.55  % (1405)Refutation not found, incomplete strategy% (1405)------------------------------
% 0.22/0.55  % (1405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1405)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (1405)Memory used [KB]: 10746
% 0.22/0.55  % (1405)Time elapsed: 0.131 s
% 0.22/0.55  % (1405)------------------------------
% 0.22/0.55  % (1405)------------------------------
% 0.22/0.55  % (1383)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (1394)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.55  % (1393)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (1393)Refutation not found, incomplete strategy% (1393)------------------------------
% 0.22/0.55  % (1393)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (1393)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (1393)Memory used [KB]: 10618
% 0.22/0.55  % (1393)Time elapsed: 0.135 s
% 0.22/0.55  % (1393)------------------------------
% 0.22/0.55  % (1393)------------------------------
% 0.22/0.55  % (1387)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (1401)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.55  % (1396)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.56  % (1387)Refutation not found, incomplete strategy% (1387)------------------------------
% 0.22/0.56  % (1387)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (1387)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (1387)Memory used [KB]: 10746
% 0.22/0.56  % (1387)Time elapsed: 0.142 s
% 0.22/0.56  % (1387)------------------------------
% 0.22/0.56  % (1387)------------------------------
% 0.22/0.56  % (1388)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.62/0.59  % (1401)Refutation found. Thanks to Tanya!
% 1.62/0.59  % SZS status Theorem for theBenchmark
% 1.62/0.59  % SZS output start Proof for theBenchmark
% 1.62/0.59  fof(f638,plain,(
% 1.62/0.59    $false),
% 1.62/0.59    inference(avatar_sat_refutation,[],[f99,f112,f161,f168,f477,f480,f624,f632])).
% 1.62/0.59  fof(f632,plain,(
% 1.62/0.59    ~spl6_7),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f627])).
% 1.62/0.59  fof(f627,plain,(
% 1.62/0.59    $false | ~spl6_7),
% 1.62/0.59    inference(resolution,[],[f476,f46])).
% 1.62/0.59  fof(f46,plain,(
% 1.62/0.59    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f30,plain,(
% 1.62/0.59    (((~r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,sK2)) & (r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | r2_orders_2(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f29,f28,f27])).
% 1.62/0.59  fof(f27,plain,(
% 1.62/0.59    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~r2_orders_2(sK0,X1,X2)) & (r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | r2_orders_2(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f28,plain,(
% 1.62/0.59    ? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | ~r2_orders_2(sK0,X1,X2)) & (r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) | r2_orders_2(sK0,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,X2)) & (r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | r2_orders_2(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f29,plain,(
% 1.62/0.59    ? [X2] : ((~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,X2)) & (r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | r2_orders_2(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,sK2)) & (r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | r2_orders_2(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f26,plain,(
% 1.62/0.59    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.62/0.59    inference(flattening,[],[f25])).
% 1.62/0.59  fof(f25,plain,(
% 1.62/0.59    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.62/0.59    inference(nnf_transformation,[],[f13])).
% 1.62/0.59  fof(f13,plain,(
% 1.62/0.59    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.62/0.59    inference(flattening,[],[f12])).
% 1.62/0.59  fof(f12,plain,(
% 1.62/0.59    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f10])).
% 1.62/0.59  fof(f10,negated_conjecture,(
% 1.62/0.59    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 1.62/0.59    inference(negated_conjecture,[],[f9])).
% 1.62/0.59  fof(f9,conjecture,(
% 1.62/0.59    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_orders_2)).
% 1.62/0.59  fof(f476,plain,(
% 1.62/0.59    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl6_7),
% 1.62/0.59    inference(avatar_component_clause,[],[f475])).
% 1.62/0.59  fof(f475,plain,(
% 1.62/0.59    spl6_7 <=> ! [X2] : ~m1_subset_1(X2,u1_struct_0(sK0))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.62/0.59  fof(f624,plain,(
% 1.62/0.59    ~spl6_1 | spl6_3),
% 1.62/0.59    inference(avatar_contradiction_clause,[],[f623])).
% 1.62/0.59  fof(f623,plain,(
% 1.62/0.59    $false | (~spl6_1 | spl6_3)),
% 1.62/0.59    inference(subsumption_resolution,[],[f622,f185])).
% 1.62/0.59  fof(f185,plain,(
% 1.62/0.59    ~r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | (~spl6_1 | spl6_3)),
% 1.62/0.59    inference(backward_demodulation,[],[f175,f114])).
% 1.62/0.59  fof(f114,plain,(
% 1.62/0.59    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | spl6_3),
% 1.62/0.59    inference(resolution,[],[f113,f46])).
% 1.62/0.59  fof(f113,plain,(
% 1.62/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0)) ) | spl6_3),
% 1.62/0.59    inference(resolution,[],[f108,f68])).
% 1.62/0.59  fof(f68,plain,(
% 1.62/0.59    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 1.62/0.59    inference(definition_unfolding,[],[f65,f67])).
% 1.62/0.59  fof(f67,plain,(
% 1.62/0.59    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f2])).
% 1.62/0.59  fof(f2,axiom,(
% 1.62/0.59    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.62/0.59  fof(f65,plain,(
% 1.62/0.59    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f22])).
% 1.62/0.59  fof(f22,plain,(
% 1.62/0.59    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.62/0.59    inference(flattening,[],[f21])).
% 1.62/0.59  fof(f21,plain,(
% 1.62/0.59    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f7])).
% 1.62/0.59  fof(f7,axiom,(
% 1.62/0.59    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.62/0.59  fof(f108,plain,(
% 1.62/0.59    ~v1_xboole_0(u1_struct_0(sK0)) | spl6_3),
% 1.62/0.59    inference(avatar_component_clause,[],[f106])).
% 1.62/0.59  fof(f106,plain,(
% 1.62/0.59    spl6_3 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 1.62/0.59  fof(f175,plain,(
% 1.62/0.59    ~r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~spl6_1),
% 1.62/0.59    inference(subsumption_resolution,[],[f49,f94])).
% 1.62/0.59  fof(f94,plain,(
% 1.62/0.59    r2_orders_2(sK0,sK1,sK2) | ~spl6_1),
% 1.62/0.59    inference(avatar_component_clause,[],[f92])).
% 1.62/0.59  fof(f92,plain,(
% 1.62/0.59    spl6_1 <=> r2_orders_2(sK0,sK1,sK2)),
% 1.62/0.59    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.62/0.59  fof(f49,plain,(
% 1.62/0.59    ~r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~r2_orders_2(sK0,sK1,sK2)),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f622,plain,(
% 1.62/0.59    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | (~spl6_1 | spl6_3)),
% 1.62/0.59    inference(forward_demodulation,[],[f621,f508])).
% 1.62/0.59  fof(f508,plain,(
% 1.62/0.59    k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)) | spl6_3),
% 1.62/0.59    inference(backward_demodulation,[],[f188,f114])).
% 1.62/0.59  fof(f188,plain,(
% 1.62/0.59    k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.62/0.59    inference(resolution,[],[f103,f46])).
% 1.62/0.59  fof(f103,plain,(
% 1.62/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X0))) )),
% 1.62/0.59    inference(resolution,[],[f88,f87])).
% 1.62/0.59  fof(f87,plain,(
% 1.62/0.59    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | k1_orders_2(sK0,X6) = a_2_0_orders_2(sK0,X6)) )),
% 1.62/0.59    inference(global_subsumption,[],[f45,f44,f43,f42,f80])).
% 1.62/0.59  fof(f80,plain,(
% 1.62/0.59    ( ! [X6] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | k1_orders_2(sK0,X6) = a_2_0_orders_2(sK0,X6)) )),
% 1.62/0.59    inference(resolution,[],[f41,f64])).
% 1.62/0.59  fof(f64,plain,(
% 1.62/0.59    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f20])).
% 1.62/0.59  fof(f20,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.62/0.59    inference(flattening,[],[f19])).
% 1.62/0.59  fof(f19,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f4])).
% 1.62/0.59  fof(f4,axiom,(
% 1.62/0.59    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).
% 1.62/0.59  fof(f41,plain,(
% 1.62/0.59    ~v2_struct_0(sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f42,plain,(
% 1.62/0.59    v3_orders_2(sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f43,plain,(
% 1.62/0.59    v4_orders_2(sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f44,plain,(
% 1.62/0.59    v5_orders_2(sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f45,plain,(
% 1.62/0.59    l1_orders_2(sK0)),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f88,plain,(
% 1.62/0.59    ( ! [X7] : (m1_subset_1(k6_domain_1(u1_struct_0(sK0),X7),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X7,u1_struct_0(sK0))) )),
% 1.62/0.59    inference(global_subsumption,[],[f45,f42,f81])).
% 1.62/0.59  fof(f81,plain,(
% 1.62/0.59    ( ! [X7] : (~m1_subset_1(X7,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X7),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.62/0.59    inference(resolution,[],[f41,f66])).
% 1.62/0.59  fof(f66,plain,(
% 1.62/0.59    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.62/0.59    inference(cnf_transformation,[],[f24])).
% 1.62/0.59  fof(f24,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.62/0.59    inference(flattening,[],[f23])).
% 1.62/0.59  fof(f23,plain,(
% 1.62/0.59    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.62/0.59    inference(ennf_transformation,[],[f11])).
% 1.62/0.59  fof(f11,plain,(
% 1.62/0.59    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 1.62/0.59    inference(pure_predicate_removal,[],[f8])).
% 1.62/0.59  fof(f8,axiom,(
% 1.62/0.59    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).
% 1.62/0.59  fof(f621,plain,(
% 1.62/0.59    r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | (~spl6_1 | spl6_3)),
% 1.62/0.59    inference(subsumption_resolution,[],[f620,f132])).
% 1.62/0.59  fof(f132,plain,(
% 1.62/0.59    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_3),
% 1.62/0.59    inference(subsumption_resolution,[],[f131,f46])).
% 1.62/0.59  fof(f131,plain,(
% 1.62/0.59    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl6_3),
% 1.62/0.59    inference(superposition,[],[f88,f114])).
% 1.62/0.59  fof(f620,plain,(
% 1.62/0.59    ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | (~spl6_1 | spl6_3)),
% 1.62/0.59    inference(subsumption_resolution,[],[f619,f47])).
% 1.62/0.59  fof(f47,plain,(
% 1.62/0.59    m1_subset_1(sK2,u1_struct_0(sK0))),
% 1.62/0.59    inference(cnf_transformation,[],[f30])).
% 1.62/0.59  fof(f619,plain,(
% 1.62/0.59    ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | (~spl6_1 | spl6_3)),
% 1.62/0.59    inference(subsumption_resolution,[],[f616,f94])).
% 1.62/0.59  fof(f616,plain,(
% 1.62/0.59    ~r2_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | (~spl6_1 | spl6_3)),
% 1.62/0.59    inference(superposition,[],[f89,f605])).
% 1.62/0.59  fof(f605,plain,(
% 1.62/0.59    sK1 = sK4(sK0,k2_tarski(sK1,sK1),sK2) | (~spl6_1 | spl6_3)),
% 1.62/0.59    inference(subsumption_resolution,[],[f602,f185])).
% 1.62/0.59  fof(f602,plain,(
% 1.62/0.59    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK1 = sK4(sK0,k2_tarski(sK1,sK1),sK2) | spl6_3),
% 1.62/0.59    inference(resolution,[],[f525,f47])).
% 1.62/0.59  fof(f525,plain,(
% 1.62/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK1 = sK4(sK0,k2_tarski(sK1,sK1),X0)) ) | spl6_3),
% 1.62/0.59    inference(subsumption_resolution,[],[f524,f132])).
% 1.62/0.59  fof(f524,plain,(
% 1.62/0.59    ( ! [X0] : (r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = sK4(sK0,k2_tarski(sK1,sK1),X0)) ) | spl6_3),
% 1.62/0.59    inference(duplicate_literal_removal,[],[f522])).
% 1.62/0.59  fof(f522,plain,(
% 1.62/0.59    ( ! [X0] : (r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = sK4(sK0,k2_tarski(sK1,sK1),X0) | sK1 = sK4(sK0,k2_tarski(sK1,sK1),X0)) ) | spl6_3),
% 1.62/0.59    inference(superposition,[],[f136,f508])).
% 1.62/0.59  fof(f136,plain,(
% 1.62/0.59    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_0_orders_2(sK0,k2_tarski(X1,X2))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(k2_tarski(X1,X2),k1_zfmisc_1(u1_struct_0(sK0))) | sK4(sK0,k2_tarski(X1,X2),X0) = X1 | sK4(sK0,k2_tarski(X1,X2),X0) = X2) )),
% 1.62/0.59    inference(resolution,[],[f90,f73])).
% 1.62/0.59  fof(f73,plain,(
% 1.62/0.59    ( ! [X4,X0,X1] : (~r2_hidden(X4,k2_tarski(X0,X1)) | X0 = X4 | X1 = X4) )),
% 1.62/0.59    inference(equality_resolution,[],[f51])).
% 1.62/0.59  fof(f51,plain,(
% 1.62/0.59    ( ! [X4,X2,X0,X1] : (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2) | k2_tarski(X0,X1) != X2) )),
% 1.62/0.59    inference(cnf_transformation,[],[f35])).
% 1.62/0.59  fof(f35,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).
% 1.62/0.59  fof(f34,plain,(
% 1.62/0.59    ! [X2,X1,X0] : (? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X1 & sK3(X0,X1,X2) != X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X1 | sK3(X0,X1,X2) = X0 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f33,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X1 != X4 & X0 != X4)) & (X1 = X4 | X0 = X4 | ~r2_hidden(X4,X2))) | k2_tarski(X0,X1) != X2))),
% 1.62/0.59    inference(rectify,[],[f32])).
% 1.62/0.59  fof(f32,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.62/0.59    inference(flattening,[],[f31])).
% 1.62/0.59  fof(f31,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | k2_tarski(X0,X1) != X2))),
% 1.62/0.59    inference(nnf_transformation,[],[f1])).
% 1.62/0.59  fof(f1,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.62/0.59  fof(f90,plain,(
% 1.62/0.59    ( ! [X10,X11] : (r2_hidden(sK4(sK0,X10,X11),X10) | r2_hidden(X11,a_2_0_orders_2(sK0,X10)) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.62/0.59    inference(global_subsumption,[],[f45,f44,f43,f42,f83])).
% 1.62/0.59  fof(f83,plain,(
% 1.62/0.59    ( ! [X10,X11] : (r2_hidden(sK4(sK0,X10,X11),X10) | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | r2_hidden(X11,a_2_0_orders_2(sK0,X10))) )),
% 1.62/0.59    inference(resolution,[],[f41,f75])).
% 1.62/0.59  fof(f75,plain,(
% 1.62/0.59    ( ! [X2,X3,X1] : (v2_struct_0(X1) | r2_hidden(sK4(X1,X2,X3),X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | r2_hidden(X3,a_2_0_orders_2(X1,X2))) )),
% 1.62/0.59    inference(equality_resolution,[],[f61])).
% 1.62/0.59  fof(f61,plain,(
% 1.62/0.59    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | r2_hidden(sK4(X1,X2,X3),X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.62/0.59    inference(cnf_transformation,[],[f40])).
% 1.62/0.59  fof(f40,plain,(
% 1.62/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : ((~r2_orders_2(X1,sK4(X1,X2,X3),X3) & r2_hidden(sK4(X1,X2,X3),X2) & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((! [X6] : (r2_orders_2(X1,X6,sK5(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK5(X0,X1,X2) = X0 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.62/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f37,f39,f38])).
% 1.62/0.59  fof(f38,plain,(
% 1.62/0.59    ! [X3,X2,X1] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r2_orders_2(X1,sK4(X1,X2,X3),X3) & r2_hidden(sK4(X1,X2,X3),X2) & m1_subset_1(sK4(X1,X2,X3),u1_struct_0(X1))))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f39,plain,(
% 1.62/0.59    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (! [X6] : (r2_orders_2(X1,X6,sK5(X0,X1,X2)) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & sK5(X0,X1,X2) = X0 & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X1))))),
% 1.62/0.59    introduced(choice_axiom,[])).
% 1.62/0.59  fof(f37,plain,(
% 1.62/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (! [X6] : (r2_orders_2(X1,X6,X5) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1))) & X0 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.62/0.59    inference(rectify,[],[f36])).
% 1.62/0.59  fof(f36,plain,(
% 1.62/0.59    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.62/0.59    inference(nnf_transformation,[],[f16])).
% 1.62/0.59  fof(f16,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.62/0.59    inference(flattening,[],[f15])).
% 1.62/0.59  fof(f15,plain,(
% 1.62/0.59    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.62/0.59    inference(ennf_transformation,[],[f6])).
% 1.62/0.59  fof(f6,axiom,(
% 1.62/0.59    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.62/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 1.62/0.59  fof(f89,plain,(
% 1.62/0.59    ( ! [X8,X9] : (~r2_orders_2(sK0,sK4(sK0,X8,X9),X9) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X9,a_2_0_orders_2(sK0,X8))) )),
% 1.62/0.59    inference(global_subsumption,[],[f45,f44,f43,f42,f82])).
% 1.62/0.59  fof(f82,plain,(
% 1.62/0.59    ( ! [X8,X9] : (~r2_orders_2(sK0,sK4(sK0,X8,X9),X9) | ~m1_subset_1(X9,u1_struct_0(sK0)) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | r2_hidden(X9,a_2_0_orders_2(sK0,X8))) )),
% 1.62/0.59    inference(resolution,[],[f41,f74])).
% 1.62/0.59  fof(f74,plain,(
% 1.62/0.59    ( ! [X2,X3,X1] : (v2_struct_0(X1) | ~r2_orders_2(X1,sK4(X1,X2,X3),X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | r2_hidden(X3,a_2_0_orders_2(X1,X2))) )),
% 1.62/0.59    inference(equality_resolution,[],[f62])).
% 1.82/0.61  fof(f62,plain,(
% 1.82/0.61    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~r2_orders_2(X1,sK4(X1,X2,X3),X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f40])).
% 1.82/0.61  fof(f480,plain,(
% 1.82/0.61    spl6_6),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f479])).
% 1.82/0.61  fof(f479,plain,(
% 1.82/0.61    $false | spl6_6),
% 1.82/0.61    inference(subsumption_resolution,[],[f478,f46])).
% 1.82/0.61  fof(f478,plain,(
% 1.82/0.61    ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl6_6),
% 1.82/0.61    inference(resolution,[],[f473,f88])).
% 1.82/0.61  fof(f473,plain,(
% 1.82/0.61    ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_6),
% 1.82/0.61    inference(avatar_component_clause,[],[f471])).
% 1.82/0.61  fof(f471,plain,(
% 1.82/0.61    spl6_6 <=> m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.82/0.61  fof(f477,plain,(
% 1.82/0.61    ~spl6_6 | spl6_7 | ~spl6_4 | ~spl6_5),
% 1.82/0.61    inference(avatar_split_clause,[],[f469,f166,f110,f475,f471])).
% 1.82/0.61  fof(f110,plain,(
% 1.82/0.61    spl6_4 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,k1_orders_2(sK0,X0)))),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 1.82/0.61  fof(f166,plain,(
% 1.82/0.61    spl6_5 <=> ! [X1,X2] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),X1)))),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.82/0.61  fof(f469,plain,(
% 1.82/0.61    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl6_4 | ~spl6_5)),
% 1.82/0.61    inference(subsumption_resolution,[],[f468,f248])).
% 1.82/0.61  fof(f248,plain,(
% 1.82/0.61    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) ) | ~spl6_4),
% 1.82/0.61    inference(resolution,[],[f164,f46])).
% 1.82/0.61  fof(f164,plain,(
% 1.82/0.61    ( ! [X2,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X3)))) ) | ~spl6_4),
% 1.82/0.61    inference(resolution,[],[f111,f88])).
% 1.82/0.61  fof(f111,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,k1_orders_2(sK0,X0))) ) | ~spl6_4),
% 1.82/0.61    inference(avatar_component_clause,[],[f110])).
% 1.82/0.61  fof(f468,plain,(
% 1.82/0.61    ( ! [X2] : (r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_5),
% 1.82/0.61    inference(forward_demodulation,[],[f377,f188])).
% 1.82/0.61  fof(f377,plain,(
% 1.82/0.61    ( ! [X2] : (r2_hidden(X2,a_2_0_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(k6_domain_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl6_5),
% 1.82/0.61    inference(resolution,[],[f362,f90])).
% 1.82/0.61  fof(f362,plain,(
% 1.82/0.61    ( ! [X0] : (~r2_hidden(X0,k6_domain_1(u1_struct_0(sK0),sK1))) ) | ~spl6_5),
% 1.82/0.61    inference(resolution,[],[f167,f46])).
% 1.82/0.61  fof(f167,plain,(
% 1.82/0.61    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),X1))) ) | ~spl6_5),
% 1.82/0.61    inference(avatar_component_clause,[],[f166])).
% 1.82/0.61  fof(f168,plain,(
% 1.82/0.61    ~spl6_3 | spl6_5),
% 1.82/0.61    inference(avatar_split_clause,[],[f104,f166,f106])).
% 1.82/0.61  fof(f104,plain,(
% 1.82/0.61    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~v1_xboole_0(u1_struct_0(sK0)) | ~r2_hidden(X2,k6_domain_1(u1_struct_0(sK0),X1))) )),
% 1.82/0.61    inference(resolution,[],[f88,f50])).
% 1.82/0.61  fof(f50,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.82/0.61    inference(cnf_transformation,[],[f14])).
% 1.82/0.61  fof(f14,plain,(
% 1.82/0.61    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.82/0.61    inference(ennf_transformation,[],[f3])).
% 1.82/0.61  fof(f3,axiom,(
% 1.82/0.61    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.82/0.61  fof(f161,plain,(
% 1.82/0.61    ~spl6_2 | spl6_3),
% 1.82/0.61    inference(avatar_contradiction_clause,[],[f160])).
% 1.82/0.61  fof(f160,plain,(
% 1.82/0.61    $false | (~spl6_2 | spl6_3)),
% 1.82/0.61    inference(subsumption_resolution,[],[f159,f70])).
% 1.82/0.61  fof(f70,plain,(
% 1.82/0.61    ( ! [X4,X0] : (r2_hidden(X4,k2_tarski(X0,X4))) )),
% 1.82/0.61    inference(equality_resolution,[],[f69])).
% 1.82/0.61  fof(f69,plain,(
% 1.82/0.61    ( ! [X4,X2,X0] : (r2_hidden(X4,X2) | k2_tarski(X0,X4) != X2) )),
% 1.82/0.61    inference(equality_resolution,[],[f53])).
% 1.82/0.61  fof(f53,plain,(
% 1.82/0.61    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | k2_tarski(X0,X1) != X2) )),
% 1.82/0.61    inference(cnf_transformation,[],[f35])).
% 1.82/0.61  fof(f159,plain,(
% 1.82/0.61    ~r2_hidden(sK1,k2_tarski(sK1,sK1)) | (~spl6_2 | spl6_3)),
% 1.82/0.61    inference(subsumption_resolution,[],[f157,f46])).
% 1.82/0.61  fof(f157,plain,(
% 1.82/0.61    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~r2_hidden(sK1,k2_tarski(sK1,sK1)) | (~spl6_2 | spl6_3)),
% 1.82/0.61    inference(resolution,[],[f152,f100])).
% 1.82/0.61  fof(f100,plain,(
% 1.82/0.61    ~r2_orders_2(sK0,sK1,sK2) | ~spl6_2),
% 1.82/0.61    inference(subsumption_resolution,[],[f49,f98])).
% 1.82/0.61  fof(f98,plain,(
% 1.82/0.61    r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~spl6_2),
% 1.82/0.61    inference(avatar_component_clause,[],[f96])).
% 1.82/0.61  fof(f96,plain,(
% 1.82/0.61    spl6_2 <=> r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 1.82/0.61    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.82/0.61  fof(f152,plain,(
% 1.82/0.61    ( ! [X0] : (r2_orders_2(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_tarski(sK1,sK1))) ) | (~spl6_2 | spl6_3)),
% 1.82/0.61    inference(subsumption_resolution,[],[f151,f130])).
% 1.82/0.61  fof(f130,plain,(
% 1.82/0.61    r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | (~spl6_2 | spl6_3)),
% 1.82/0.61    inference(backward_demodulation,[],[f98,f114])).
% 1.82/0.61  fof(f151,plain,(
% 1.82/0.61    ( ! [X0] : (~r2_hidden(sK2,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | r2_orders_2(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k2_tarski(sK1,sK1))) ) | (~spl6_2 | spl6_3)),
% 1.82/0.61    inference(forward_demodulation,[],[f150,f134])).
% 1.82/0.61  fof(f134,plain,(
% 1.82/0.61    k1_orders_2(sK0,k2_tarski(sK1,sK1)) = a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)) | spl6_3),
% 1.82/0.61    inference(resolution,[],[f132,f87])).
% 1.82/0.61  fof(f150,plain,(
% 1.82/0.61    ( ! [X0] : (r2_orders_2(sK0,X0,sK2) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | ~r2_hidden(X0,k2_tarski(sK1,sK1))) ) | (~spl6_2 | spl6_3)),
% 1.82/0.61    inference(subsumption_resolution,[],[f148,f132])).
% 1.82/0.61  fof(f148,plain,(
% 1.82/0.61    ( ! [X0] : (r2_orders_2(sK0,X0,sK2) | ~m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(sK2,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1))) | ~r2_hidden(X0,k2_tarski(sK1,sK1))) ) | (~spl6_2 | spl6_3)),
% 1.82/0.61    inference(superposition,[],[f85,f145])).
% 1.82/0.61  fof(f145,plain,(
% 1.82/0.61    sK2 = sK5(sK2,sK0,k2_tarski(sK1,sK1)) | (~spl6_2 | spl6_3)),
% 1.82/0.61    inference(resolution,[],[f142,f130])).
% 1.82/0.61  fof(f142,plain,(
% 1.82/0.61    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | sK5(X0,sK0,k2_tarski(sK1,sK1)) = X0) ) | spl6_3),
% 1.82/0.61    inference(forward_demodulation,[],[f133,f134])).
% 1.82/0.61  fof(f133,plain,(
% 1.82/0.61    ( ! [X0] : (sK5(X0,sK0,k2_tarski(sK1,sK1)) = X0 | ~r2_hidden(X0,a_2_0_orders_2(sK0,k2_tarski(sK1,sK1)))) ) | spl6_3),
% 1.82/0.61    inference(resolution,[],[f132,f84])).
% 1.82/0.61  fof(f84,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | sK5(X0,sK0,X1) = X0 | ~r2_hidden(X0,a_2_0_orders_2(sK0,X1))) )),
% 1.82/0.61    inference(global_subsumption,[],[f45,f44,f43,f42,f77])).
% 1.82/0.61  fof(f77,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~r2_hidden(X0,a_2_0_orders_2(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | sK5(X0,sK0,X1) = X0) )),
% 1.82/0.61    inference(resolution,[],[f41,f58])).
% 1.82/0.61  fof(f58,plain,(
% 1.82/0.61    ( ! [X2,X0,X1] : (v2_struct_0(X1) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | sK5(X0,X1,X2) = X0) )),
% 1.82/0.61    inference(cnf_transformation,[],[f40])).
% 1.82/0.61  fof(f85,plain,(
% 1.82/0.61    ( ! [X4,X2,X3] : (r2_orders_2(sK0,X2,sK5(X4,sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X4,a_2_0_orders_2(sK0,X3)) | ~r2_hidden(X2,X3)) )),
% 1.82/0.61    inference(global_subsumption,[],[f45,f44,f43,f42,f78])).
% 1.82/0.61  fof(f78,plain,(
% 1.82/0.61    ( ! [X4,X2,X3] : (~r2_hidden(X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X4,a_2_0_orders_2(sK0,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | r2_orders_2(sK0,X2,sK5(X4,sK0,X3))) )),
% 1.82/0.61    inference(resolution,[],[f41,f59])).
% 1.82/0.61  fof(f59,plain,(
% 1.82/0.61    ( ! [X6,X2,X0,X1] : (v2_struct_0(X1) | ~r2_hidden(X6,X2) | ~m1_subset_1(X6,u1_struct_0(X1)) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | r2_orders_2(X1,X6,sK5(X0,X1,X2))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f40])).
% 1.82/0.61  fof(f112,plain,(
% 1.82/0.61    ~spl6_3 | spl6_4),
% 1.82/0.61    inference(avatar_split_clause,[],[f101,f110,f106])).
% 1.82/0.61  fof(f101,plain,(
% 1.82/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)) | ~r2_hidden(X1,k1_orders_2(sK0,X0))) )),
% 1.82/0.61    inference(resolution,[],[f86,f50])).
% 1.82/0.61  fof(f86,plain,(
% 1.82/0.61    ( ! [X5] : (m1_subset_1(k1_orders_2(sK0,X5),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.82/0.61    inference(global_subsumption,[],[f45,f44,f43,f42,f79])).
% 1.82/0.61  fof(f79,plain,(
% 1.82/0.61    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | m1_subset_1(k1_orders_2(sK0,X5),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.82/0.61    inference(resolution,[],[f41,f63])).
% 1.82/0.61  fof(f63,plain,(
% 1.82/0.61    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.82/0.61    inference(cnf_transformation,[],[f18])).
% 1.82/0.61  fof(f18,plain,(
% 1.82/0.61    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.82/0.61    inference(flattening,[],[f17])).
% 1.82/0.61  fof(f17,plain,(
% 1.82/0.61    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.82/0.61    inference(ennf_transformation,[],[f5])).
% 1.82/0.61  fof(f5,axiom,(
% 1.82/0.61    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.82/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).
% 1.82/0.61  fof(f99,plain,(
% 1.82/0.61    spl6_1 | spl6_2),
% 1.82/0.61    inference(avatar_split_clause,[],[f48,f96,f92])).
% 1.82/0.61  fof(f48,plain,(
% 1.82/0.61    r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | r2_orders_2(sK0,sK1,sK2)),
% 1.82/0.61    inference(cnf_transformation,[],[f30])).
% 1.82/0.61  % SZS output end Proof for theBenchmark
% 1.82/0.61  % (1401)------------------------------
% 1.82/0.61  % (1401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.82/0.61  % (1401)Termination reason: Refutation
% 1.82/0.61  
% 1.82/0.61  % (1401)Memory used [KB]: 11001
% 1.82/0.61  % (1401)Time elapsed: 0.176 s
% 1.82/0.61  % (1401)------------------------------
% 1.82/0.61  % (1401)------------------------------
% 1.82/0.61  % (1376)Success in time 0.243 s
%------------------------------------------------------------------------------
