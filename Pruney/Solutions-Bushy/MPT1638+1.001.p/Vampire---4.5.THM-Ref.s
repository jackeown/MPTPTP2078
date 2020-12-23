%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1638+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:13 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  138 (4131 expanded)
%              Number of leaves         :   17 (1270 expanded)
%              Depth                    :   50
%              Number of atoms          :  522 (26444 expanded)
%              Number of equality atoms :  100 ( 997 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f349,plain,(
    $false ),
    inference(global_subsumption,[],[f58,f348])).

fof(f348,plain,(
    ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f347,f63])).

fof(f63,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f347,plain,(
    ~ l1_struct_0(sK4) ),
    inference(global_subsumption,[],[f57,f346])).

fof(f346,plain,
    ( ~ l1_struct_0(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f345,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f345,plain,(
    v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f344,f92])).

fof(f92,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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
    inference(rectify,[],[f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f344,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ r2_hidden(sK5,k1_tarski(sK5))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f330,f316])).

fof(f316,plain,
    ( ~ r2_hidden(sK6,k6_waybel_0(sK4,sK5))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(global_subsumption,[],[f62,f315])).

fof(f315,plain,
    ( r1_orders_2(sK4,sK5,sK6)
    | ~ r2_hidden(sK6,k6_waybel_0(sK4,sK5))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f307,f192])).

fof(f192,plain,(
    ! [X0] :
      ( sP2(k1_tarski(sK5),sK4,X0)
      | ~ r2_hidden(X0,k6_waybel_0(sK4,sK5))
      | v1_xboole_0(u1_struct_0(sK4)) ) ),
    inference(resolution,[],[f181,f142])).

fof(f142,plain,(
    ! [X2] :
      ( sP3(X2,sK4,k1_tarski(sK5))
      | v1_xboole_0(u1_struct_0(sK4)) ) ),
    inference(resolution,[],[f140,f113])).

fof(f113,plain,
    ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(global_subsumption,[],[f59,f111])).

fof(f111,plain,
    ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(superposition,[],[f68,f105])).

fof(f105,plain,(
    k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5) ),
    inference(global_subsumption,[],[f58,f104])).

fof(f104,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5)
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f103,f63])).

fof(f103,plain,
    ( ~ l1_struct_0(sK4)
    | k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5) ),
    inference(global_subsumption,[],[f57,f102])).

fof(f102,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f100,f64])).

fof(f100,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | k6_domain_1(u1_struct_0(sK4),sK5) = k1_tarski(sK5) ),
    inference(resolution,[],[f67,f59])).

fof(f67,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f59,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( ( ~ r1_orders_2(sK4,sK5,sK6)
      | ~ r2_hidden(sK6,k6_waybel_0(sK4,sK5)) )
    & ( r1_orders_2(sK4,sK5,sK6)
      | r2_hidden(sK6,k6_waybel_0(sK4,sK5)) )
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f39,f38,f37])).

fof(f37,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r1_orders_2(X0,X1,X2)
                  | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) )
                & ( r1_orders_2(X0,X1,X2)
                  | r2_hidden(X2,k6_waybel_0(X0,X1)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(sK4,X1,X2)
                | ~ r2_hidden(X2,k6_waybel_0(sK4,X1)) )
              & ( r1_orders_2(sK4,X1,X2)
                | r2_hidden(X2,k6_waybel_0(sK4,X1)) )
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r1_orders_2(sK4,X1,X2)
              | ~ r2_hidden(X2,k6_waybel_0(sK4,X1)) )
            & ( r1_orders_2(sK4,X1,X2)
              | r2_hidden(X2,k6_waybel_0(sK4,X1)) )
            & m1_subset_1(X2,u1_struct_0(sK4)) )
        & m1_subset_1(X1,u1_struct_0(sK4)) )
   => ( ? [X2] :
          ( ( ~ r1_orders_2(sK4,sK5,X2)
            | ~ r2_hidden(X2,k6_waybel_0(sK4,sK5)) )
          & ( r1_orders_2(sK4,sK5,X2)
            | r2_hidden(X2,k6_waybel_0(sK4,sK5)) )
          & m1_subset_1(X2,u1_struct_0(sK4)) )
      & m1_subset_1(sK5,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X2] :
        ( ( ~ r1_orders_2(sK4,sK5,X2)
          | ~ r2_hidden(X2,k6_waybel_0(sK4,sK5)) )
        & ( r1_orders_2(sK4,sK5,X2)
          | r2_hidden(X2,k6_waybel_0(sK4,sK5)) )
        & m1_subset_1(X2,u1_struct_0(sK4)) )
   => ( ( ~ r1_orders_2(sK4,sK5,sK6)
        | ~ r2_hidden(sK6,k6_waybel_0(sK4,sK5)) )
      & ( r1_orders_2(sK4,sK5,sK6)
        | r2_hidden(sK6,k6_waybel_0(sK4,sK5)) )
      & m1_subset_1(sK6,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X1,X2)
                | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X1,X2)
                | r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r1_orders_2(X0,X1,X2)
                | ~ r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & ( r1_orders_2(X0,X1,X2)
                | r2_hidden(X2,k6_waybel_0(X0,X1)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <~> r1_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k6_waybel_0(X0,X1))
                <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k6_waybel_0(X0,X1))
              <=> r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_waybel_0)).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | sP3(X1,sK4,X0) ) ),
    inference(global_subsumption,[],[f57,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | sP3(X1,sK4,X0)
      | v2_struct_0(sK4) ) ),
    inference(resolution,[],[f90,f58])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP3(X0,X1,X2)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f28,f33,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( sP2(X2,X1,X0)
    <=> ? [X3] :
          ( ? [X4] :
              ( r2_hidden(X4,X2)
              & r1_orders_2(X1,X4,X3)
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> sP2(X2,X1,X0) )
      | ~ sP3(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_waybel_0)).

fof(f181,plain,(
    ! [X1] :
      ( ~ sP3(X1,sK4,k1_tarski(sK5))
      | sP2(k1_tarski(sK5),sK4,X1)
      | ~ r2_hidden(X1,k6_waybel_0(sK4,sK5)) ) ),
    inference(backward_demodulation,[],[f165,f180])).

fof(f180,plain,(
    k6_waybel_0(sK4,sK5) = k4_waybel_0(sK4,k1_tarski(sK5)) ),
    inference(forward_demodulation,[],[f174,f105])).

fof(f174,plain,(
    k6_waybel_0(sK4,sK5) = k4_waybel_0(sK4,k6_domain_1(u1_struct_0(sK4),sK5)) ),
    inference(resolution,[],[f171,f59])).

fof(f171,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
      | k4_waybel_0(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k6_waybel_0(sK4,X0) ) ),
    inference(global_subsumption,[],[f57,f170])).

fof(f170,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK4))
      | k4_waybel_0(sK4,k6_domain_1(u1_struct_0(sK4),X0)) = k6_waybel_0(sK4,X0)
      | v2_struct_0(sK4) ) ),
    inference(resolution,[],[f65,f58])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_waybel_0)).

fof(f165,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k4_waybel_0(sK4,k1_tarski(sK5)))
      | sP2(k1_tarski(sK5),sK4,X1)
      | ~ sP3(X1,sK4,k1_tarski(sK5)) ) ),
    inference(superposition,[],[f82,f163])).

fof(f163,plain,(
    k4_waybel_0(sK4,k1_tarski(sK5)) = a_2_1_waybel_0(sK4,k1_tarski(sK5)) ),
    inference(global_subsumption,[],[f58,f162])).

fof(f162,plain,
    ( k4_waybel_0(sK4,k1_tarski(sK5)) = a_2_1_waybel_0(sK4,k1_tarski(sK5))
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f161,f63])).

fof(f161,plain,
    ( ~ l1_struct_0(sK4)
    | k4_waybel_0(sK4,k1_tarski(sK5)) = a_2_1_waybel_0(sK4,k1_tarski(sK5)) ),
    inference(global_subsumption,[],[f57,f160])).

fof(f160,plain,
    ( k4_waybel_0(sK4,k1_tarski(sK5)) = a_2_1_waybel_0(sK4,k1_tarski(sK5))
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f158,f64])).

fof(f158,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | k4_waybel_0(sK4,k1_tarski(sK5)) = a_2_1_waybel_0(sK4,k1_tarski(sK5)) ),
    inference(resolution,[],[f156,f113])).

fof(f156,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | k4_waybel_0(sK4,X0) = a_2_1_waybel_0(sK4,X0) ) ),
    inference(global_subsumption,[],[f57,f155])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK4)))
      | k4_waybel_0(sK4,X0) = a_2_1_waybel_0(sK4,X0)
      | v2_struct_0(sK4) ) ),
    inference(resolution,[],[f66,f58])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k4_waybel_0(X0,X1) = a_2_1_waybel_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_waybel_0)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_waybel_0(X1,X2)) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f307,plain,
    ( ~ sP2(k1_tarski(sK5),sK4,sK6)
    | r1_orders_2(sK4,sK5,sK6) ),
    inference(backward_demodulation,[],[f287,f306])).

fof(f306,plain,(
    sK5 = sK11(k1_tarski(sK5),sK4,sK6) ),
    inference(global_subsumption,[],[f58,f305])).

fof(f305,plain,
    ( sK5 = sK11(k1_tarski(sK5),sK4,sK6)
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f304,f63])).

% (18247)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f304,plain,
    ( ~ l1_struct_0(sK4)
    | sK5 = sK11(k1_tarski(sK5),sK4,sK6) ),
    inference(global_subsumption,[],[f57,f303])).

fof(f303,plain,
    ( sK5 = sK11(k1_tarski(sK5),sK4,sK6)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f302,f64])).

fof(f302,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | sK5 = sK11(k1_tarski(sK5),sK4,sK6) ),
    inference(resolution,[],[f300,f92])).

fof(f300,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | v1_xboole_0(u1_struct_0(sK4))
    | sK5 = sK11(k1_tarski(sK5),sK4,sK6) ),
    inference(duplicate_literal_removal,[],[f299])).

fof(f299,plain,
    ( sK5 = sK11(k1_tarski(sK5),sK4,sK6)
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ r2_hidden(sK5,k1_tarski(sK5))
    | v1_xboole_0(u1_struct_0(sK4))
    | sK5 = sK11(k1_tarski(sK5),sK4,sK6) ),
    inference(resolution,[],[f276,f193])).

fof(f193,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k6_waybel_0(sK4,sK5))
      | v1_xboole_0(u1_struct_0(sK4))
      | sK5 = sK11(k1_tarski(sK5),sK4,X0) ) ),
    inference(resolution,[],[f192,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(k1_tarski(X0),X1,X2)
      | sK11(k1_tarski(X0),X1,X2) = X0 ) ),
    inference(resolution,[],[f88,f93])).

fof(f93,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK11(X0,X1,X2),X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r1_orders_2(X1,X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r2_hidden(sK11(X0,X1,X2),X0)
          & r1_orders_2(X1,sK11(X0,X1,X2),sK10(X0,X1,X2))
          & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))
          & sK10(X0,X1,X2) = X2
          & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11])],[f53,f55,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X0)
              & r1_orders_2(X1,X6,X5)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X0)
            & r1_orders_2(X1,X6,sK10(X0,X1,X2))
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK10(X0,X1,X2) = X2
        & m1_subset_1(sK10(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X0)
          & r1_orders_2(X1,X6,sK10(X0,X1,X2))
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK11(X0,X1,X2),X0)
        & r1_orders_2(X1,sK11(X0,X1,X2),sK10(X0,X1,X2))
        & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r1_orders_2(X1,X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X5] :
            ( ? [X6] :
                ( r2_hidden(X6,X0)
                & r1_orders_2(X1,X6,X5)
                & m1_subset_1(X6,u1_struct_0(X1)) )
            & X2 = X5
            & m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ( sP2(X2,X1,X0)
        | ! [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(X4,X2)
                | ~ r1_orders_2(X1,X4,X3)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r1_orders_2(X1,X4,X3)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP2(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f276,plain,
    ( r2_hidden(sK6,k6_waybel_0(sK4,sK5))
    | sK5 = sK11(k1_tarski(sK5),sK4,sK6)
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ r2_hidden(sK5,k1_tarski(sK5)) ),
    inference(duplicate_literal_removal,[],[f267])).

fof(f267,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | sK5 = sK11(k1_tarski(sK5),sK4,sK6)
    | v1_xboole_0(u1_struct_0(sK4))
    | r2_hidden(sK6,k6_waybel_0(sK4,sK5))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f256,f195])).

fof(f195,plain,(
    ! [X0] :
      ( ~ sP2(k1_tarski(sK5),sK4,X0)
      | r2_hidden(X0,k6_waybel_0(sK4,sK5))
      | v1_xboole_0(u1_struct_0(sK4)) ) ),
    inference(resolution,[],[f182,f142])).

fof(f182,plain,(
    ! [X0] :
      ( ~ sP3(X0,sK4,k1_tarski(sK5))
      | ~ sP2(k1_tarski(sK5),sK4,X0)
      | r2_hidden(X0,k6_waybel_0(sK4,sK5)) ) ),
    inference(backward_demodulation,[],[f164,f180])).

fof(f164,plain,(
    ! [X0] :
      ( r2_hidden(X0,k4_waybel_0(sK4,k1_tarski(sK5)))
      | ~ sP2(k1_tarski(sK5),sK4,X0)
      | ~ sP3(X0,sK4,k1_tarski(sK5)) ) ),
    inference(superposition,[],[f83,f163])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_waybel_0(X1,X2))
      | ~ sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f256,plain,(
    ! [X1] :
      ( sP2(X1,sK4,sK6)
      | ~ r2_hidden(sK5,X1)
      | sK5 = sK11(k1_tarski(sK5),sK4,sK6)
      | v1_xboole_0(u1_struct_0(sK4)) ) ),
    inference(global_subsumption,[],[f60,f254])).

fof(f254,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK5,X1)
      | sP2(X1,sK4,sK6)
      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
      | sK5 = sK11(k1_tarski(sK5),sK4,sK6)
      | v1_xboole_0(u1_struct_0(sK4)) ) ),
    inference(resolution,[],[f247,f204])).

fof(f204,plain,
    ( r1_orders_2(sK4,sK5,sK6)
    | sK5 = sK11(k1_tarski(sK5),sK4,sK6)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f193,f61])).

fof(f61,plain,
    ( r2_hidden(sK6,k6_waybel_0(sK4,sK5))
    | r1_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f247,plain,(
    ! [X0,X1] :
      ( ~ r1_orders_2(sK4,sK5,X1)
      | ~ r2_hidden(sK5,X0)
      | sP2(X0,sK4,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK4)) ) ),
    inference(resolution,[],[f95,f59])).

fof(f95,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r2_hidden(X4,X0)
      | ~ r1_orders_2(X1,X4,X3)
      | sP2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP2(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | ~ r1_orders_2(X1,X4,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f60,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f287,plain,
    ( r1_orders_2(sK4,sK11(k1_tarski(sK5),sK4,sK6),sK6)
    | ~ sP2(k1_tarski(sK5),sK4,sK6) ),
    inference(superposition,[],[f87,f284])).

fof(f284,plain,(
    sK6 = sK10(k1_tarski(sK5),sK4,sK6) ),
    inference(global_subsumption,[],[f58,f283])).

fof(f283,plain,
    ( sK6 = sK10(k1_tarski(sK5),sK4,sK6)
    | ~ l1_orders_2(sK4) ),
    inference(resolution,[],[f282,f63])).

fof(f282,plain,
    ( ~ l1_struct_0(sK4)
    | sK6 = sK10(k1_tarski(sK5),sK4,sK6) ),
    inference(global_subsumption,[],[f57,f281])).

fof(f281,plain,
    ( sK6 = sK10(k1_tarski(sK5),sK4,sK6)
    | ~ l1_struct_0(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f280,f64])).

fof(f280,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | sK6 = sK10(k1_tarski(sK5),sK4,sK6) ),
    inference(duplicate_literal_removal,[],[f277])).

fof(f277,plain,
    ( sK6 = sK10(k1_tarski(sK5),sK4,sK6)
    | v1_xboole_0(u1_struct_0(sK4))
    | sK6 = sK10(k1_tarski(sK5),sK4,sK6) ),
    inference(resolution,[],[f261,f92])).

fof(f261,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK5,X2)
      | sK6 = sK10(k1_tarski(sK5),sK4,sK6)
      | v1_xboole_0(u1_struct_0(sK4))
      | sK6 = sK10(X2,sK4,sK6) ) ),
    inference(resolution,[],[f255,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | sK10(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f255,plain,(
    ! [X0] :
      ( sP2(X0,sK4,sK6)
      | ~ r2_hidden(sK5,X0)
      | sK6 = sK10(k1_tarski(sK5),sK4,sK6)
      | v1_xboole_0(u1_struct_0(sK4)) ) ),
    inference(global_subsumption,[],[f60,f253])).

fof(f253,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK5,X0)
      | sP2(X0,sK4,sK6)
      | ~ m1_subset_1(sK6,u1_struct_0(sK4))
      | sK6 = sK10(k1_tarski(sK5),sK4,sK6)
      | v1_xboole_0(u1_struct_0(sK4)) ) ),
    inference(resolution,[],[f247,f207])).

fof(f207,plain,
    ( r1_orders_2(sK4,sK5,sK6)
    | sK6 = sK10(k1_tarski(sK5),sK4,sK6)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f194,f61])).

fof(f194,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,k6_waybel_0(sK4,sK5))
      | v1_xboole_0(u1_struct_0(sK4))
      | sK10(k1_tarski(sK5),sK4,X1) = X1 ) ),
    inference(resolution,[],[f192,f85])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X1,sK11(X0,X1,X2),sK10(X0,X1,X2))
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f62,plain,
    ( ~ r2_hidden(sK6,k6_waybel_0(sK4,sK5))
    | ~ r1_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f330,plain,
    ( r2_hidden(sK6,k6_waybel_0(sK4,sK5))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ r2_hidden(sK5,k1_tarski(sK5)) ),
    inference(duplicate_literal_removal,[],[f321])).

fof(f321,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | v1_xboole_0(u1_struct_0(sK4))
    | r2_hidden(sK6,k6_waybel_0(sK4,sK5))
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f319,f195])).

fof(f319,plain,(
    ! [X0] :
      ( sP2(X0,sK4,sK6)
      | ~ r2_hidden(sK5,X0)
      | v1_xboole_0(u1_struct_0(sK4)) ) ),
    inference(global_subsumption,[],[f60,f318])).

fof(f318,plain,(
    ! [X0] :
      ( v1_xboole_0(u1_struct_0(sK4))
      | ~ r2_hidden(sK5,X0)
      | sP2(X0,sK4,sK6)
      | ~ m1_subset_1(sK6,u1_struct_0(sK4)) ) ),
    inference(resolution,[],[f317,f247])).

fof(f317,plain,
    ( r1_orders_2(sK4,sK5,sK6)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f316,f61])).

fof(f57,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f58,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

%------------------------------------------------------------------------------
