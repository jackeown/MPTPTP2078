%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1657+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:16 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 298 expanded)
%              Number of leaves         :    9 (  84 expanded)
%              Depth                    :   25
%              Number of atoms          :  463 (2066 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   17 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f121,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f45,f115,f120])).

fof(f120,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f119,f41,f37])).

fof(f37,plain,
    ( spl4_1
  <=> r2_yellow_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f41,plain,
    ( spl4_2
  <=> r2_yellow_0(sK1,k4_waybel_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f119,plain,
    ( r2_yellow_0(sK1,k4_waybel_0(sK1,sK2))
    | ~ r2_yellow_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f118,f26])).

fof(f26,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ( ~ r2_yellow_0(sK1,k4_waybel_0(sK1,sK2))
      | ~ r2_yellow_0(sK1,sK2) )
    & ( r2_yellow_0(sK1,k4_waybel_0(sK1,sK2))
      | r2_yellow_0(sK1,sK2) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    & l1_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f14,f16,f15])).

fof(f15,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_yellow_0(X0,k4_waybel_0(X0,X1))
              | ~ r2_yellow_0(X0,X1) )
            & ( r2_yellow_0(X0,k4_waybel_0(X0,X1))
              | r2_yellow_0(X0,X1) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ r2_yellow_0(sK1,k4_waybel_0(sK1,X1))
            | ~ r2_yellow_0(sK1,X1) )
          & ( r2_yellow_0(sK1,k4_waybel_0(sK1,X1))
            | r2_yellow_0(sK1,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
      & l1_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X1] :
        ( ( ~ r2_yellow_0(sK1,k4_waybel_0(sK1,X1))
          | ~ r2_yellow_0(sK1,X1) )
        & ( r2_yellow_0(sK1,k4_waybel_0(sK1,X1))
          | r2_yellow_0(sK1,X1) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ~ r2_yellow_0(sK1,k4_waybel_0(sK1,sK2))
        | ~ r2_yellow_0(sK1,sK2) )
      & ( r2_yellow_0(sK1,k4_waybel_0(sK1,sK2))
        | r2_yellow_0(sK1,sK2) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,k4_waybel_0(X0,X1))
            | ~ r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,k4_waybel_0(X0,X1))
            | r2_yellow_0(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,k4_waybel_0(X0,X1))
            | ~ r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,k4_waybel_0(X0,X1))
            | r2_yellow_0(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_yellow_0(X0,X1)
          <~> r2_yellow_0(X0,k4_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( r2_yellow_0(X0,X1)
          <~> r2_yellow_0(X0,k4_waybel_0(X0,X1)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_yellow_0(X0,X1)
            <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_yellow_0(X0,X1)
          <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_0)).

fof(f118,plain,
    ( ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,k4_waybel_0(sK1,sK2))
    | ~ r2_yellow_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f117,f23])).

fof(f23,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f117,plain,
    ( v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,k4_waybel_0(sK1,sK2))
    | ~ r2_yellow_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f116,f24])).

fof(f24,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f116,plain,
    ( ~ v3_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,k4_waybel_0(sK1,sK2))
    | ~ r2_yellow_0(sK1,sK2) ),
    inference(subsumption_resolution,[],[f82,f25])).

fof(f25,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ l1_orders_2(sK1)
    | r2_yellow_0(sK1,k4_waybel_0(sK1,sK2))
    | ~ r2_yellow_0(sK1,sK2) ),
    inference(resolution,[],[f81,f27])).

fof(f27,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f17])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,k4_waybel_0(X0,X1))
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f74,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,sK3(X0,X2,k4_waybel_0(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | r2_yellow_0(X0,k4_waybel_0(X0,X1))
      | ~ r1_lattice3(X0,X1,sK3(X0,X2,k4_waybel_0(X0,X1)))
      | ~ r2_yellow_0(X0,X2) ) ),
    inference(subsumption_resolution,[],[f53,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ( sP0(sK3(X0,X1,X2),X2,X0,X1)
            & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f12,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( sP0(X3,X2,X0,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sP0(sK3(X0,X1,X2),X2,X0,X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( sP0(X3,X2,X0,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f10,f11])).

fof(f11,plain,(
    ! [X3,X2,X0,X1] :
      ( ( r1_lattice3(X0,X1,X3)
      <~> r1_lattice3(X0,X2,X3) )
      | ~ sP0(X3,X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r1_lattice3(X0,X1,X3)
              <~> r1_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r2_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r1_lattice3(X0,X1,X3)
                <=> r1_lattice3(X0,X2,X3) ) ) )
         => r2_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_yellow_0)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,sK3(X0,X2,k4_waybel_0(X0,X1)))
      | ~ m1_subset_1(sK3(X0,X2,k4_waybel_0(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | r2_yellow_0(X0,k4_waybel_0(X0,X1))
      | ~ r1_lattice3(X0,X2,sK3(X0,X2,k4_waybel_0(X0,X1)))
      | ~ r2_yellow_0(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X1,sK3(X0,X2,k4_waybel_0(X0,X1)))
      | ~ m1_subset_1(sK3(X0,X2,k4_waybel_0(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | r2_yellow_0(X0,k4_waybel_0(X0,X1))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r1_lattice3(X0,X2,sK3(X0,X2,k4_waybel_0(X0,X1)))
      | ~ r2_yellow_0(X0,X2) ) ),
    inference(resolution,[],[f30,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,sK3(X0,X1,X2))
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(resolution,[],[f35,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | ~ r1_lattice3(X2,X3,X0)
      | ~ r1_lattice3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( ~ r1_lattice3(X2,X1,X0)
          | ~ r1_lattice3(X2,X3,X0) )
        & ( r1_lattice3(X2,X1,X0)
          | r1_lattice3(X2,X3,X0) ) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f19])).

fof(f19,plain,(
    ! [X3,X2,X0,X1] :
      ( ( ( ~ r1_lattice3(X0,X2,X3)
          | ~ r1_lattice3(X0,X1,X3) )
        & ( r1_lattice3(X0,X2,X3)
          | r1_lattice3(X0,X1,X3) ) )
      | ~ sP0(X3,X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( sP0(sK3(X0,X1,X2),X2,X0,X1)
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattice3(X0,X1,X2)
                  | ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
                & ( r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
                  | ~ r1_lattice3(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattice3(X0,X1,X2)
              <=> r1_lattice3(X0,k4_waybel_0(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_waybel_0)).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X1,k4_waybel_0(X0,X1)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_yellow_0(X0,k4_waybel_0(X0,X1))
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(factoring,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X2,sK3(X0,X2,k4_waybel_0(X0,X1)))
      | r1_lattice3(X0,X1,sK3(X0,X2,k4_waybel_0(X0,X1)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_yellow_0(X0,k4_waybel_0(X0,X1))
      | ~ r2_yellow_0(X0,X2) ) ),
    inference(subsumption_resolution,[],[f60,f34])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X2,k4_waybel_0(X0,X1)))
      | ~ m1_subset_1(sK3(X0,X2,k4_waybel_0(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | r1_lattice3(X0,X2,sK3(X0,X2,k4_waybel_0(X0,X1)))
      | r2_yellow_0(X0,k4_waybel_0(X0,X1))
      | ~ r2_yellow_0(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X2,k4_waybel_0(X0,X1)))
      | ~ m1_subset_1(sK3(X0,X2,k4_waybel_0(X0,X1)),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | r1_lattice3(X0,X2,sK3(X0,X2,k4_waybel_0(X0,X1)))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | r2_yellow_0(X0,k4_waybel_0(X0,X1))
      | ~ r2_yellow_0(X0,X2) ) ),
    inference(resolution,[],[f31,f47])).

fof(f47,plain,(
    ! [X4,X5,X3] :
      ( r1_lattice3(X3,X5,sK3(X3,X4,X5))
      | r1_lattice3(X3,X4,sK3(X3,X4,X5))
      | ~ l1_orders_2(X3)
      | v2_struct_0(X3)
      | r2_yellow_0(X3,X5)
      | ~ r2_yellow_0(X3,X4) ) ),
    inference(resolution,[],[f35,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_lattice3(X2,X3,X0)
      | r1_lattice3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),X2)
      | r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f115,plain,
    ( spl4_1
    | ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f114])).

fof(f114,plain,
    ( $false
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f113,f26])).

fof(f113,plain,
    ( ~ l1_orders_2(sK1)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f112,f25])).

fof(f112,plain,
    ( ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f111,f39])).

fof(f39,plain,
    ( ~ r2_yellow_0(sK1,sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f111,plain,
    ( r2_yellow_0(sK1,sK2)
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f110,f27])).

fof(f110,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_yellow_0(sK1,sK2)
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f109,f23])).

fof(f109,plain,
    ( v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_yellow_0(sK1,sK2)
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f108,f24])).

fof(f108,plain,
    ( ~ v3_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_yellow_0(sK1,sK2)
    | ~ v4_orders_2(sK1)
    | ~ l1_orders_2(sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f107,f42])).

% (21384)Refutation not found, incomplete strategy% (21384)------------------------------
% (21384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21373)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% (21384)Termination reason: Refutation not found, incomplete strategy

% (21384)Memory used [KB]: 9850
% (21384)Time elapsed: 0.093 s
% (21384)------------------------------
% (21384)------------------------------
% (21381)Refutation not found, incomplete strategy% (21381)------------------------------
% (21381)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21381)Termination reason: Refutation not found, incomplete strategy

% (21381)Memory used [KB]: 5373
% (21381)Time elapsed: 0.054 s
% (21381)------------------------------
% (21381)------------------------------
fof(f42,plain,
    ( r2_yellow_0(sK1,k4_waybel_0(sK1,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f107,plain,(
    ! [X4,X5] :
      ( ~ r2_yellow_0(X4,k4_waybel_0(X4,X5))
      | ~ v3_orders_2(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | r2_yellow_0(X4,X5)
      | ~ v4_orders_2(X4)
      | ~ l1_orders_2(X4) ) ),
    inference(subsumption_resolution,[],[f106,f34])).

fof(f106,plain,(
    ! [X4,X5] :
      ( ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | r2_yellow_0(X4,X5)
      | ~ r2_yellow_0(X4,k4_waybel_0(X4,X5))
      | ~ l1_orders_2(X4)
      | ~ m1_subset_1(sK3(X4,k4_waybel_0(X4,X5),X5),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f103,f62])).

fof(f62,plain,(
    ! [X4,X5,X3] :
      ( r1_lattice3(X3,X5,sK3(X3,k4_waybel_0(X3,X4),X5))
      | r1_lattice3(X3,X4,sK3(X3,k4_waybel_0(X3,X4),X5))
      | ~ l1_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | r2_yellow_0(X3,X5)
      | ~ r2_yellow_0(X3,k4_waybel_0(X3,X4)) ) ),
    inference(subsumption_resolution,[],[f59,f34])).

fof(f59,plain,(
    ! [X4,X5,X3] :
      ( r1_lattice3(X3,X4,sK3(X3,k4_waybel_0(X3,X4),X5))
      | ~ m1_subset_1(sK3(X3,k4_waybel_0(X3,X4),X5),u1_struct_0(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3)
      | r1_lattice3(X3,X5,sK3(X3,k4_waybel_0(X3,X4),X5))
      | r2_yellow_0(X3,X5)
      | ~ r2_yellow_0(X3,k4_waybel_0(X3,X4)) ) ),
    inference(duplicate_literal_removal,[],[f56])).

fof(f56,plain,(
    ! [X4,X5,X3] :
      ( r1_lattice3(X3,X4,sK3(X3,k4_waybel_0(X3,X4),X5))
      | ~ m1_subset_1(sK3(X3,k4_waybel_0(X3,X4),X5),u1_struct_0(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3)
      | r1_lattice3(X3,X5,sK3(X3,k4_waybel_0(X3,X4),X5))
      | ~ l1_orders_2(X3)
      | v2_struct_0(X3)
      | r2_yellow_0(X3,X5)
      | ~ r2_yellow_0(X3,k4_waybel_0(X3,X4)) ) ),
    inference(resolution,[],[f31,f47])).

fof(f103,plain,(
    ! [X4,X5] :
      ( ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | r2_yellow_0(X4,X5)
      | ~ r2_yellow_0(X4,k4_waybel_0(X4,X5))
      | ~ l1_orders_2(X4)
      | ~ r1_lattice3(X4,X5,sK3(X4,k4_waybel_0(X4,X5),X5))
      | ~ m1_subset_1(sK3(X4,k4_waybel_0(X4,X5),X5),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X4,X5] :
      ( ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | r2_yellow_0(X4,X5)
      | ~ r2_yellow_0(X4,k4_waybel_0(X4,X5))
      | ~ l1_orders_2(X4)
      | ~ r1_lattice3(X4,X5,sK3(X4,k4_waybel_0(X4,X5),X5))
      | ~ m1_subset_1(sK3(X4,k4_waybel_0(X4,X5),X5),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_orders_2(X4)
      | ~ v4_orders_2(X4)
      | ~ v3_orders_2(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f98,f30])).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(X0,k4_waybel_0(X0,X1),sK3(X0,k4_waybel_0(X0,X1),X1))
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_yellow_0(X0,X1)
      | ~ r2_yellow_0(X0,k4_waybel_0(X0,X1))
      | ~ l1_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f95])).

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_yellow_0(X0,X1)
      | ~ r2_yellow_0(X0,k4_waybel_0(X0,X1))
      | r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r1_lattice3(X0,k4_waybel_0(X0,X1),sK3(X0,k4_waybel_0(X0,X1),X1))
      | ~ r2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ),
    inference(resolution,[],[f88,f46])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,k4_waybel_0(X0,X1),X1))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_yellow_0(X0,X1)
      | ~ r2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ),
    inference(factoring,[],[f62])).

fof(f45,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f28,f41,f37])).

fof(f28,plain,
    ( r2_yellow_0(sK1,k4_waybel_0(sK1,sK2))
    | r2_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f29,f41,f37])).

fof(f29,plain,
    ( ~ r2_yellow_0(sK1,k4_waybel_0(sK1,sK2))
    | ~ r2_yellow_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f17])).

%------------------------------------------------------------------------------
