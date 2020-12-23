%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 263 expanded)
%              Number of leaves         :   12 (  84 expanded)
%              Depth                    :   14
%              Number of atoms          :  296 (1540 expanded)
%              Number of equality atoms :   38 (  49 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f97,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f96])).

fof(f96,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f95])).

fof(f95,plain,
    ( $false
    | ~ spl3_1 ),
    inference(resolution,[],[f93,f35])).

fof(f35,plain,(
    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( r2_hidden(X1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).

fof(f93,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl3_1 ),
    inference(resolution,[],[f90,f34])).

fof(f34,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X3))) )
    | ~ spl3_1 ),
    inference(resolution,[],[f87,f57])).

fof(f57,plain,(
    ! [X0] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(global_subsumption,[],[f33,f30,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f29,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f30,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f33,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,k1_orders_2(sK0,X0)) )
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f61,f67])).

fof(f67,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl3_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(u1_struct_0(sK0))
      | ~ r2_hidden(X1,k1_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f58,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f58,plain,(
    ! [X1] :
      ( m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(global_subsumption,[],[f33,f32,f31,f30,f55])).

fof(f55,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f29,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

fof(f31,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f85,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f83,f75])).

fof(f75,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | spl3_1 ),
    inference(backward_demodulation,[],[f35,f74])).

fof(f74,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1)
    | spl3_1 ),
    inference(resolution,[],[f73,f34])).

fof(f73,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0) )
    | spl3_1 ),
    inference(resolution,[],[f68,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1) ) ),
    inference(definition_unfolding,[],[f43,f45])).

fof(f45,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f68,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f83,plain,
    ( ~ r2_hidden(sK1,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f80,f52])).

fof(f52,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f38,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK2(X0,X1) != X0
            | ~ r2_hidden(sK2(X0,X1),X1) )
          & ( sK2(X0,X1) = X0
            | r2_hidden(sK2(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK2(X0,X1) != X0
          | ~ r2_hidden(sK2(X0,X1),X1) )
        & ( sK2(X0,X1) = X0
          | r2_hidden(sK2(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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
    inference(rectify,[],[f25])).

fof(f25,plain,(
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

fof(f80,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK1,sK1))
    | ~ r2_hidden(sK1,k1_orders_2(sK0,k2_tarski(sK1,sK1)))
    | spl3_1 ),
    inference(resolution,[],[f62,f77])).

fof(f77,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_1 ),
    inference(subsumption_resolution,[],[f76,f34])).

fof(f76,plain,
    ( m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl3_1 ),
    inference(superposition,[],[f57,f74])).

fof(f62,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,X0)
      | ~ r2_hidden(sK1,k1_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f59,f34])).

fof(f59,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X3)
      | ~ r2_hidden(X2,k1_orders_2(sK0,X3)) ) ),
    inference(global_subsumption,[],[f33,f32,f31,f30,f56])).

fof(f56,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | ~ r2_hidden(X2,k1_orders_2(sK0,X3)) ) ),
    inference(resolution,[],[f29,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ r2_hidden(X1,k1_orders_2(X0,X2)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n008.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 13:55:30 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (8459)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.51  % (8467)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.51  % (8445)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (8451)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.51  % (8444)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.52  % (8467)Refutation not found, incomplete strategy% (8467)------------------------------
% 0.22/0.52  % (8467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8451)Refutation not found, incomplete strategy% (8451)------------------------------
% 0.22/0.52  % (8451)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (8467)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (8467)Memory used [KB]: 6268
% 0.22/0.52  % (8467)Time elapsed: 0.097 s
% 0.22/0.52  % (8467)------------------------------
% 0.22/0.52  % (8467)------------------------------
% 0.22/0.52  % (8447)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (8451)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (8451)Memory used [KB]: 10746
% 0.22/0.52  % (8451)Time elapsed: 0.109 s
% 0.22/0.52  % (8451)------------------------------
% 0.22/0.52  % (8451)------------------------------
% 0.22/0.52  % (8442)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (8442)Refutation not found, incomplete strategy% (8442)------------------------------
% 0.22/0.53  % (8442)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (8442)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (8442)Memory used [KB]: 1663
% 0.22/0.53  % (8442)Time elapsed: 0.106 s
% 0.22/0.53  % (8442)------------------------------
% 0.22/0.53  % (8442)------------------------------
% 0.22/0.53  % (8441)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (8446)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.53  % (8463)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (8465)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (8465)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f97,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(avatar_sat_refutation,[],[f85,f96])).
% 0.22/0.54  fof(f96,plain,(
% 0.22/0.54    ~spl3_1),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f95])).
% 0.22/0.54  fof(f95,plain,(
% 0.22/0.54    $false | ~spl3_1),
% 0.22/0.54    inference(resolution,[],[f93,f35])).
% 0.22/0.54  fof(f35,plain,(
% 0.22/0.54    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f24,plain,(
% 0.22/0.54    (r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f23,f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f23,plain,(
% 0.22/0.54    ? [X1] : (r2_hidden(X1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X1,u1_struct_0(sK0))) => (r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f9])).
% 0.22/0.54  fof(f9,negated_conjecture,(
% 0.22/0.54    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.22/0.54    inference(negated_conjecture,[],[f8])).
% 0.22/0.54  fof(f8,conjecture,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).
% 0.22/0.54  fof(f93,plain,(
% 0.22/0.54    ( ! [X0] : (~r2_hidden(X0,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))) ) | ~spl3_1),
% 0.22/0.54    inference(resolution,[],[f90,f34])).
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f90,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X3)))) ) | ~spl3_1),
% 0.22/0.54    inference(resolution,[],[f87,f57])).
% 0.22/0.54  fof(f57,plain,(
% 0.22/0.54    ( ! [X0] : (m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.22/0.54    inference(global_subsumption,[],[f33,f30,f54])).
% 0.22/0.54  fof(f54,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | m1_subset_1(k6_domain_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.54    inference(resolution,[],[f29,f44])).
% 0.22/0.54  fof(f44,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f21])).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f20])).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f10])).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.54    inference(pure_predicate_removal,[],[f6])).
% 0.22/0.54  fof(f6,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ~v2_struct_0(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f30,plain,(
% 0.22/0.54    v3_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f33,plain,(
% 0.22/0.54    l1_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f87,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,k1_orders_2(sK0,X0))) ) | ~spl3_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f61,f67])).
% 0.22/0.54  fof(f67,plain,(
% 0.22/0.54    v1_xboole_0(u1_struct_0(sK0)) | ~spl3_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f66])).
% 0.22/0.54  fof(f66,plain,(
% 0.22/0.54    spl3_1 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.22/0.54    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.54  fof(f61,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(u1_struct_0(sK0)) | ~r2_hidden(X1,k1_orders_2(sK0,X0))) )),
% 0.22/0.54    inference(resolution,[],[f58,f36])).
% 0.22/0.54  fof(f36,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f13])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.54    inference(ennf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.54  fof(f58,plain,(
% 0.22/0.54    ( ! [X1] : (m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.54    inference(global_subsumption,[],[f33,f32,f31,f30,f55])).
% 0.22/0.54  fof(f55,plain,(
% 0.22/0.54    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | m1_subset_1(k1_orders_2(sK0,X1),k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.54    inference(resolution,[],[f29,f42])).
% 0.22/0.54  fof(f42,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f17])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f16])).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    v4_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f32,plain,(
% 0.22/0.54    v5_orders_2(sK0)),
% 0.22/0.54    inference(cnf_transformation,[],[f24])).
% 0.22/0.54  fof(f85,plain,(
% 0.22/0.54    spl3_1),
% 0.22/0.54    inference(avatar_contradiction_clause,[],[f84])).
% 0.22/0.54  fof(f84,plain,(
% 0.22/0.54    $false | spl3_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f83,f75])).
% 0.22/0.54  fof(f75,plain,(
% 0.22/0.54    r2_hidden(sK1,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | spl3_1),
% 0.22/0.54    inference(backward_demodulation,[],[f35,f74])).
% 0.22/0.54  fof(f74,plain,(
% 0.22/0.54    k6_domain_1(u1_struct_0(sK0),sK1) = k2_tarski(sK1,sK1) | spl3_1),
% 0.22/0.54    inference(resolution,[],[f73,f34])).
% 0.22/0.54  fof(f73,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_tarski(X0,X0) = k6_domain_1(u1_struct_0(sK0),X0)) ) | spl3_1),
% 0.22/0.54    inference(resolution,[],[f68,f50])).
% 0.22/0.54  fof(f50,plain,(
% 0.22/0.54    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f43,f45])).
% 0.22/0.54  fof(f45,plain,(
% 0.22/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.54  fof(f43,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.54    inference(flattening,[],[f18])).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f5])).
% 0.22/0.54  fof(f5,axiom,(
% 0.22/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.54  fof(f68,plain,(
% 0.22/0.54    ~v1_xboole_0(u1_struct_0(sK0)) | spl3_1),
% 0.22/0.54    inference(avatar_component_clause,[],[f66])).
% 0.22/0.54  fof(f83,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | spl3_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f80,f52])).
% 0.22/0.54  fof(f52,plain,(
% 0.22/0.54    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 0.22/0.54    inference(equality_resolution,[],[f51])).
% 0.22/0.54  fof(f51,plain,(
% 0.22/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 0.22/0.54    inference(equality_resolution,[],[f48])).
% 0.22/0.54  fof(f48,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 0.22/0.54    inference(definition_unfolding,[],[f38,f45])).
% 0.22/0.54  fof(f38,plain,(
% 0.22/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 0.22/0.54    inference(cnf_transformation,[],[f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f26,f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK2(X0,X1) != X0 | ~r2_hidden(sK2(X0,X1),X1)) & (sK2(X0,X1) = X0 | r2_hidden(sK2(X0,X1),X1))))),
% 0.22/0.54    introduced(choice_axiom,[])).
% 0.22/0.54  fof(f26,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(rectify,[],[f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 0.22/0.54    inference(nnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.22/0.54  fof(f80,plain,(
% 0.22/0.54    ~r2_hidden(sK1,k2_tarski(sK1,sK1)) | ~r2_hidden(sK1,k1_orders_2(sK0,k2_tarski(sK1,sK1))) | spl3_1),
% 0.22/0.54    inference(resolution,[],[f62,f77])).
% 0.22/0.54  fof(f77,plain,(
% 0.22/0.54    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_1),
% 0.22/0.54    inference(subsumption_resolution,[],[f76,f34])).
% 0.22/0.54  fof(f76,plain,(
% 0.22/0.54    m1_subset_1(k2_tarski(sK1,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | spl3_1),
% 0.22/0.54    inference(superposition,[],[f57,f74])).
% 0.22/0.54  fof(f62,plain,(
% 0.22/0.54    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X0) | ~r2_hidden(sK1,k1_orders_2(sK0,X0))) )),
% 0.22/0.54    inference(resolution,[],[f59,f34])).
% 0.22/0.54  fof(f59,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,X3) | ~r2_hidden(X2,k1_orders_2(sK0,X3))) )),
% 0.22/0.54    inference(global_subsumption,[],[f33,f32,f31,f30,f56])).
% 0.22/0.54  fof(f56,plain,(
% 0.22/0.54    ( ! [X2,X3] : (~r2_hidden(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | ~r2_hidden(X2,k1_orders_2(sK0,X3))) )),
% 0.22/0.54    inference(resolution,[],[f29,f41])).
% 0.22/0.54  fof(f41,plain,(
% 0.22/0.54    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | ~r2_hidden(X1,k1_orders_2(X0,X2))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f15])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.54    inference(flattening,[],[f14])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,axiom,(
% 0.22/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (8465)------------------------------
% 0.22/0.54  % (8465)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8465)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (8465)Memory used [KB]: 10746
% 0.22/0.54  % (8465)Time elapsed: 0.121 s
% 0.22/0.54  % (8465)------------------------------
% 0.22/0.54  % (8465)------------------------------
% 0.22/0.54  % (8443)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (8449)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (8440)Success in time 0.175 s
%------------------------------------------------------------------------------
