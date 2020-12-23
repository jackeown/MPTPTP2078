%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1563+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:06 EST 2020

% Result     : Theorem 2.82s
% Output     : Refutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  188 ( 765 expanded)
%              Number of leaves         :   19 ( 197 expanded)
%              Depth                    :   37
%              Number of atoms          : 1489 (6943 expanded)
%              Number of equality atoms :   92 ( 436 expanded)
%              Maximal formula depth    :   27 (  11 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2387,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f2377,f2386])).

fof(f2386,plain,(
    ~ spl7_1 ),
    inference(avatar_contradiction_clause,[],[f2385])).

fof(f2385,plain,
    ( $false
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f2384,f54])).

fof(f54,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( k13_lattice3(sK0,sK1,sK2) != k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v1_lattice3(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k13_lattice3(X0,X1,X2) != k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(sK0,X1,X2) != k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v1_lattice3(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k13_lattice3(sK0,X1,X2) != k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X2))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k13_lattice3(sK0,sK1,X2) != k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK1,X2))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( k13_lattice3(sK0,sK1,X2) != k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK1,X2))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k13_lattice3(sK0,sK1,sK2) != k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,X1,X2) != k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k13_lattice3(X0,X1,X2) != k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v1_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k13_lattice3(X0,X1,X2) = k1_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_yellow_0)).

fof(f2384,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f2383,f53])).

fof(f53,plain,(
    v1_lattice3(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f2383,plain,
    ( ~ v1_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl7_1 ),
    inference(resolution,[],[f2382,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v1_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v1_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattice3)).

fof(f2382,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(subsumption_resolution,[],[f2381,f92])).

fof(f92,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f58,f54])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f2381,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_1 ),
    inference(resolution,[],[f98,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f98,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl7_1
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f2377,plain,(
    spl7_2 ),
    inference(avatar_contradiction_clause,[],[f2376])).

fof(f2376,plain,
    ( $false
    | spl7_2 ),
    inference(subsumption_resolution,[],[f2375,f56])).

fof(f56,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f2375,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f2374,f53])).

fof(f2374,plain,
    ( ~ v1_lattice3(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f2373,f55])).

fof(f55,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f36])).

fof(f2373,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f2372,f52])).

fof(f52,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f36])).

fof(f2372,plain,
    ( ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f2367,f54])).

fof(f2367,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v1_lattice3(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl7_2 ),
    inference(resolution,[],[f2126,f1363])).

fof(f1363,plain,(
    ! [X76,X77,X75] :
      ( r2_lattice3(X75,k2_tarski(X76,X77),k13_lattice3(X75,X76,X77))
      | ~ l1_orders_2(X75)
      | ~ v5_orders_2(X75)
      | ~ m1_subset_1(X76,u1_struct_0(X75))
      | ~ v1_lattice3(X75)
      | ~ m1_subset_1(X77,u1_struct_0(X75)) ) ),
    inference(subsumption_resolution,[],[f1342,f1262])).

fof(f1262,plain,(
    ! [X2,X0,X1] :
      ( r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1261,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k13_lattice3)).

fof(f1261,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(k13_lattice3(X1,X0,X2),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1260,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X2,X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f90,f86])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X2,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,X3,sK4(X0,X1,X2,X3))
                        & r1_orders_2(X0,X2,sK4(X0,X1,X2,X3))
                        & r1_orders_2(X0,X1,sK4(X0,X1,X2,X3))
                        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f44,f45])).

fof(f45,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X3,X4)
          & r1_orders_2(X0,X2,X4)
          & r1_orders_2(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X3,sK4(X0,X1,X2,X3))
        & r1_orders_2(X0,X2,sK4(X0,X1,X2,X3))
        & r1_orders_2(X0,X1,sK4(X0,X1,X2,X3))
        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X3,X5)
                            | ~ r1_orders_2(X0,X2,X5)
                            | ~ r1_orders_2(X0,X1,X5)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k13_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X3,X4)
                          & r1_orders_2(X0,X2,X4)
                          & r1_orders_2(X0,X1,X4)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X2,X3)
                      | ~ r1_orders_2(X0,X1,X3) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X3,X4)
                            | ~ r1_orders_2(X0,X2,X4)
                            | ~ r1_orders_2(X0,X1,X4)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X2,X3)
                        & r1_orders_2(X0,X1,X3) )
                      | k13_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X3,X4)
                          | ~ r1_orders_2(X0,X2,X4)
                          | ~ r1_orders_2(X0,X1,X4)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k13_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X2,X4)
                              & r1_orders_2(X0,X1,X4) )
                           => r1_orders_2(X0,X3,X4) ) )
                      & r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X3) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_yellow_0)).

fof(f1260,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X2,k13_lattice3(X1,X0,X2))
      | ~ m1_subset_1(k13_lattice3(X1,X0,X2),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1259,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f91,f86])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,X1,k13_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,X3)
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1259,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X0,k13_lattice3(X1,X0,X2))
      | ~ r1_orders_2(X1,X2,k13_lattice3(X1,X0,X2))
      | ~ m1_subset_1(k13_lattice3(X1,X0,X2),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f1250])).

fof(f1250,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_orders_2(X1,X0,k13_lattice3(X1,X0,X2))
      | ~ r1_orders_2(X1,X2,k13_lattice3(X1,X0,X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(k13_lattice3(X1,X0,X2),u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f529,f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X3,X1)
                      | ~ r1_orders_2(X0,X2,X1) )
                    & ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                      | ~ r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                      | ~ r1_orders_2(X0,X1,X3)
                      | ~ r1_orders_2(X0,X1,X2) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                      | ~ r1_lattice3(X0,k2_tarski(X2,X3),X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) )
                     => r2_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r2_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X3,X1)
                        & r1_orders_2(X0,X2,X1) ) )
                    & ( ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) )
                     => r1_lattice3(X0,k2_tarski(X2,X3),X1) )
                    & ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
                     => ( r1_orders_2(X0,X1,X3)
                        & r1_orders_2(X0,X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_yellow_0)).

fof(f529,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_lattice3(X8,k2_tarski(X7,X9),k13_lattice3(X8,X9,X7))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ v1_lattice3(X8)
      | ~ v5_orders_2(X8)
      | r1_yellow_0(X8,k2_tarski(X7,X9))
      | ~ m1_subset_1(X7,u1_struct_0(X8)) ) ),
    inference(subsumption_resolution,[],[f524,f86])).

fof(f524,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X7,u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ v1_lattice3(X8)
      | ~ v5_orders_2(X8)
      | r1_yellow_0(X8,k2_tarski(X7,X9))
      | ~ r2_lattice3(X8,k2_tarski(X7,X9),k13_lattice3(X8,X9,X7))
      | ~ m1_subset_1(k13_lattice3(X8,X9,X7),u1_struct_0(X8)) ) ),
    inference(duplicate_literal_removal,[],[f517])).

fof(f517,plain,(
    ! [X8,X7,X9] :
      ( ~ m1_subset_1(X7,u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ v1_lattice3(X8)
      | ~ v5_orders_2(X8)
      | r1_yellow_0(X8,k2_tarski(X7,X9))
      | ~ r2_lattice3(X8,k2_tarski(X7,X9),k13_lattice3(X8,X9,X7))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ m1_subset_1(X7,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | r1_yellow_0(X8,k2_tarski(X7,X9))
      | ~ r2_lattice3(X8,k2_tarski(X7,X9),k13_lattice3(X8,X9,X7))
      | ~ m1_subset_1(k13_lattice3(X8,X9,X7),u1_struct_0(X8))
      | ~ v5_orders_2(X8) ) ),
    inference(resolution,[],[f291,f117])).

fof(f117,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,X4,sK5(X3,k2_tarski(X5,X4),X6))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r1_yellow_0(X3,k2_tarski(X5,X4))
      | ~ r2_lattice3(X3,k2_tarski(X5,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f114,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
                  & r2_lattice3(X0,X1,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,sK6(X0,X1),X5)
                  | ~ r2_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,sK6(X0,X1))
              & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f48,f50,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
        & r2_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X4,X5)
              | ~ r2_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r2_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,sK6(X0,X1),X5)
            | ~ r2_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r2_lattice3(X0,X1,sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X4,X5)
                    | ~ r2_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r2_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r1_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r1_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X2,X3) ) )
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow_0)).

fof(f114,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,X4,sK5(X3,k2_tarski(X5,X4),X6))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X5,X4),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r1_yellow_0(X3,k2_tarski(X5,X4))
      | ~ r2_lattice3(X3,k2_tarski(X5,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f113])).

fof(f113,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,X4,sK5(X3,k2_tarski(X5,X4),X6))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X5,X4),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r1_yellow_0(X3,k2_tarski(X5,X4))
      | ~ r2_lattice3(X3,k2_tarski(X5,X4),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(resolution,[],[f64,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK5(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f64,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f291,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK5(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X6)))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f288,f86])).

fof(f288,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK5(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X6)))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(k13_lattice3(X4,X5,X6),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f279])).

fof(f279,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK5(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X6)))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X6))
      | ~ m1_subset_1(k13_lattice3(X4,X5,X6),u1_struct_0(X4))
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f187,f111])).

fof(f111,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,X4,sK5(X3,k2_tarski(X4,X5),X6))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r1_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r2_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f108,f82])).

fof(f108,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,X4,sK5(X3,k2_tarski(X4,X5),X6))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r1_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r2_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,X4,sK5(X3,k2_tarski(X4,X5),X6))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r1_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r2_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(resolution,[],[f63,f83])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f187,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ r1_orders_2(X0,X1,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,k13_lattice3(X0,X1,X3)) ) ),
    inference(subsumption_resolution,[],[f186,f86])).

fof(f186,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ r1_orders_2(X0,X3,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,k13_lattice3(X0,X1,X3))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X3),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f185,f82])).

fof(f185,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ m1_subset_1(sK5(X0,X2,k13_lattice3(X0,X1,X3)),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,k13_lattice3(X0,X1,X3))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X3),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ m1_subset_1(sK5(X0,X2,k13_lattice3(X0,X1,X3)),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X3,sK5(X0,X2,k13_lattice3(X0,X1,X3)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X2,k13_lattice3(X0,X1,X3))
      | ~ m1_subset_1(k13_lattice3(X0,X1,X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f159,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK5(X0,X1,X2))
      | r1_yellow_0(X0,X1)
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f159,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,k13_lattice3(X0,X3,X1),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,k13_lattice3(X0,X3,X1),X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f89,f86])).

fof(f89,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_subset_1(k13_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,k13_lattice3(X0,X1,X2),X5)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X3,X5)
      | ~ r1_orders_2(X0,X2,X5)
      | ~ r1_orders_2(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k13_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1342,plain,(
    ! [X76,X77,X75] :
      ( r2_lattice3(X75,k2_tarski(X76,X77),k13_lattice3(X75,X76,X77))
      | ~ r1_yellow_0(X75,k2_tarski(X76,X77))
      | ~ l1_orders_2(X75)
      | ~ v5_orders_2(X75)
      | ~ m1_subset_1(X76,u1_struct_0(X75))
      | ~ v1_lattice3(X75)
      | ~ m1_subset_1(X77,u1_struct_0(X75)) ) ),
    inference(duplicate_literal_removal,[],[f1315])).

fof(f1315,plain,(
    ! [X76,X77,X75] :
      ( r2_lattice3(X75,k2_tarski(X76,X77),k13_lattice3(X75,X76,X77))
      | ~ r1_yellow_0(X75,k2_tarski(X76,X77))
      | ~ l1_orders_2(X75)
      | ~ v5_orders_2(X75)
      | ~ m1_subset_1(X76,u1_struct_0(X75))
      | ~ l1_orders_2(X75)
      | ~ v1_lattice3(X75)
      | ~ v5_orders_2(X75)
      | ~ m1_subset_1(X77,u1_struct_0(X75))
      | ~ r1_yellow_0(X75,k2_tarski(X76,X77)) ) ),
    inference(superposition,[],[f80,f761])).

fof(f761,plain,(
    ! [X2,X0,X1] :
      ( k13_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r1_yellow_0(X1,k2_tarski(X2,X0)) ) ),
    inference(subsumption_resolution,[],[f760,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f760,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k13_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(sK6(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f759,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,k2_tarski(X2,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f115,f79])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,k2_tarski(X2,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,k2_tarski(X2,X1)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,k2_tarski(X2,X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,k2_tarski(X2,X1)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_tarski(X2,X1))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f64,f80])).

fof(f759,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k13_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,X0,sK6(X1,k2_tarski(X2,X0)))
      | ~ m1_subset_1(sK6(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f758,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,k2_tarski(X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f109,f79])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,k2_tarski(X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,sK6(X0,k2_tarski(X1,X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f63,f80])).

fof(f758,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k13_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,X2,sK6(X1,k2_tarski(X2,X0)))
      | ~ r1_orders_2(X1,X0,sK6(X1,k2_tarski(X2,X0)))
      | ~ m1_subset_1(sK6(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f747])).

fof(f747,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k13_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,X2,sK6(X1,k2_tarski(X2,X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k13_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,X0,sK6(X1,k2_tarski(X2,X0)))
      | ~ r1_orders_2(X1,X2,sK6(X1,k2_tarski(X2,X0)))
      | ~ m1_subset_1(sK6(X1,k2_tarski(X2,X0)),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1) ) ),
    inference(resolution,[],[f392,f76])).

fof(f76,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,sK4(X0,X1,X2,X3))
      | k13_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f392,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ r1_orders_2(X9,X11,sK4(X9,X10,X12,sK6(X9,k2_tarski(X11,X12))))
      | ~ m1_subset_1(X12,u1_struct_0(X9))
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ l1_orders_2(X9)
      | ~ v1_lattice3(X9)
      | ~ v5_orders_2(X9)
      | k13_lattice3(X9,X10,X12) = sK6(X9,k2_tarski(X11,X12))
      | ~ r1_yellow_0(X9,k2_tarski(X11,X12))
      | ~ r1_orders_2(X9,X10,sK6(X9,k2_tarski(X11,X12)))
      | ~ m1_subset_1(X11,u1_struct_0(X9)) ) ),
    inference(subsumption_resolution,[],[f391,f79])).

fof(f391,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ r1_orders_2(X9,X10,sK6(X9,k2_tarski(X11,X12)))
      | ~ m1_subset_1(X12,u1_struct_0(X9))
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ l1_orders_2(X9)
      | ~ v1_lattice3(X9)
      | ~ v5_orders_2(X9)
      | k13_lattice3(X9,X10,X12) = sK6(X9,k2_tarski(X11,X12))
      | ~ r1_yellow_0(X9,k2_tarski(X11,X12))
      | ~ r1_orders_2(X9,X11,sK4(X9,X10,X12,sK6(X9,k2_tarski(X11,X12))))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | ~ m1_subset_1(sK6(X9,k2_tarski(X11,X12)),u1_struct_0(X9)) ) ),
    inference(subsumption_resolution,[],[f390,f116])).

fof(f390,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ r1_orders_2(X9,X10,sK6(X9,k2_tarski(X11,X12)))
      | ~ m1_subset_1(X12,u1_struct_0(X9))
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ l1_orders_2(X9)
      | ~ v1_lattice3(X9)
      | ~ v5_orders_2(X9)
      | k13_lattice3(X9,X10,X12) = sK6(X9,k2_tarski(X11,X12))
      | ~ r1_yellow_0(X9,k2_tarski(X11,X12))
      | ~ r1_orders_2(X9,X12,sK6(X9,k2_tarski(X11,X12)))
      | ~ r1_orders_2(X9,X11,sK4(X9,X10,X12,sK6(X9,k2_tarski(X11,X12))))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | ~ m1_subset_1(sK6(X9,k2_tarski(X11,X12)),u1_struct_0(X9)) ) ),
    inference(subsumption_resolution,[],[f384,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))
      | k13_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f384,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ r1_orders_2(X9,X10,sK6(X9,k2_tarski(X11,X12)))
      | ~ m1_subset_1(X12,u1_struct_0(X9))
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ l1_orders_2(X9)
      | ~ v1_lattice3(X9)
      | ~ v5_orders_2(X9)
      | k13_lattice3(X9,X10,X12) = sK6(X9,k2_tarski(X11,X12))
      | ~ m1_subset_1(sK4(X9,X10,X12,sK6(X9,k2_tarski(X11,X12))),u1_struct_0(X9))
      | ~ r1_yellow_0(X9,k2_tarski(X11,X12))
      | ~ r1_orders_2(X9,X12,sK6(X9,k2_tarski(X11,X12)))
      | ~ r1_orders_2(X9,X11,sK4(X9,X10,X12,sK6(X9,k2_tarski(X11,X12))))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | ~ m1_subset_1(sK6(X9,k2_tarski(X11,X12)),u1_struct_0(X9)) ) ),
    inference(duplicate_literal_removal,[],[f379])).

fof(f379,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ r1_orders_2(X9,X10,sK6(X9,k2_tarski(X11,X12)))
      | ~ m1_subset_1(X12,u1_struct_0(X9))
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ l1_orders_2(X9)
      | ~ v1_lattice3(X9)
      | ~ v5_orders_2(X9)
      | k13_lattice3(X9,X10,X12) = sK6(X9,k2_tarski(X11,X12))
      | ~ m1_subset_1(sK4(X9,X10,X12,sK6(X9,k2_tarski(X11,X12))),u1_struct_0(X9))
      | ~ r1_yellow_0(X9,k2_tarski(X11,X12))
      | ~ r1_orders_2(X9,X12,sK6(X9,k2_tarski(X11,X12)))
      | ~ r1_orders_2(X9,X11,sK4(X9,X10,X12,sK6(X9,k2_tarski(X11,X12))))
      | ~ m1_subset_1(X12,u1_struct_0(X9))
      | ~ m1_subset_1(X11,u1_struct_0(X9))
      | k13_lattice3(X9,X10,X12) = sK6(X9,k2_tarski(X11,X12))
      | ~ r1_orders_2(X9,X12,sK6(X9,k2_tarski(X11,X12)))
      | ~ r1_orders_2(X9,X10,sK6(X9,k2_tarski(X11,X12)))
      | ~ m1_subset_1(sK6(X9,k2_tarski(X11,X12)),u1_struct_0(X9))
      | ~ m1_subset_1(X12,u1_struct_0(X9))
      | ~ m1_subset_1(X10,u1_struct_0(X9))
      | ~ l1_orders_2(X9)
      | ~ v1_lattice3(X9)
      | ~ v5_orders_2(X9) ) ),
    inference(resolution,[],[f219,f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK4(X0,X1,X2,X3))
      | k13_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f219,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK4(X0,X4,X1,sK6(X0,k2_tarski(X2,X3))))
      | ~ r1_orders_2(X0,X4,sK6(X0,k2_tarski(X2,X3)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k13_lattice3(X0,X4,X1) = sK6(X0,k2_tarski(X2,X3))
      | ~ m1_subset_1(sK4(X0,X4,X1,sK6(X0,k2_tarski(X2,X3))),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X2,X3))
      | ~ r1_orders_2(X0,X1,sK6(X0,k2_tarski(X2,X3)))
      | ~ r1_orders_2(X0,X2,sK4(X0,X4,X1,sK6(X0,k2_tarski(X2,X3))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,sK6(X0,k2_tarski(X2,X3)))
      | ~ r1_orders_2(X0,X4,sK6(X0,k2_tarski(X2,X3)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k13_lattice3(X0,X4,X1) = sK6(X0,k2_tarski(X2,X3))
      | ~ m1_subset_1(sK4(X0,X4,X1,sK6(X0,k2_tarski(X2,X3))),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,k2_tarski(X2,X3))
      | ~ r1_orders_2(X0,X3,sK4(X0,X4,X1,sK6(X0,k2_tarski(X2,X3))))
      | ~ r1_orders_2(X0,X2,sK4(X0,X4,X1,sK6(X0,k2_tarski(X2,X3))))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(sK4(X0,X4,X1,sK6(X0,k2_tarski(X2,X3))),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f145,f65])).

fof(f145,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_lattice3(X0,X3,sK4(X0,X1,X2,sK6(X0,X3)))
      | ~ r1_orders_2(X0,X2,sK6(X0,X3))
      | ~ r1_orders_2(X0,X1,sK6(X0,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k13_lattice3(X0,X1,X2) = sK6(X0,X3)
      | ~ m1_subset_1(sK4(X0,X1,X2,sK6(X0,X3)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X3) ) ),
    inference(subsumption_resolution,[],[f144,f79])).

fof(f144,plain,(
    ! [X2,X0,X3,X1] :
      ( k13_lattice3(X0,X1,X2) = sK6(X0,X3)
      | ~ r1_orders_2(X0,X2,sK6(X0,X3))
      | ~ r1_orders_2(X0,X1,sK6(X0,X3))
      | ~ m1_subset_1(sK6(X0,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_lattice3(X0,X3,sK4(X0,X1,X2,sK6(X0,X3)))
      | ~ m1_subset_1(sK4(X0,X1,X2,sK6(X0,X3)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X3) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( k13_lattice3(X0,X1,X2) = sK6(X0,X3)
      | ~ r1_orders_2(X0,X2,sK6(X0,X3))
      | ~ r1_orders_2(X0,X1,sK6(X0,X3))
      | ~ m1_subset_1(sK6(X0,X3),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ r2_lattice3(X0,X3,sK4(X0,X1,X2,sK6(X0,X3)))
      | ~ m1_subset_1(sK4(X0,X1,X2,sK6(X0,X3)),u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X3)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f78,f81])).

fof(f81,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,sK6(X0,X1),X5)
      | ~ r2_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X3,sK4(X0,X1,X2,X3))
      | k13_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X2,X3)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v1_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_lattice3(X0,X1,sK6(X0,X1))
      | ~ r1_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f2126,plain,
    ( ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),k13_lattice3(sK0,sK1,sK2))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f2125,f56])).

fof(f2125,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),k13_lattice3(sK0,sK1,sK2))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f2124,f52])).

fof(f2124,plain,
    ( ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),k13_lattice3(sK0,sK1,sK2))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f2123,f53])).

fof(f2123,plain,
    ( ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),k13_lattice3(sK0,sK1,sK2))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f2122,f54])).

fof(f2122,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),k13_lattice3(sK0,sK1,sK2))
    | spl7_2 ),
    inference(subsumption_resolution,[],[f2094,f55])).

fof(f2094,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),k13_lattice3(sK0,sK1,sK2))
    | spl7_2 ),
    inference(trivial_inequality_removal,[],[f2071])).

fof(f2071,plain,
    ( k13_lattice3(sK0,sK1,sK2) != k13_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v1_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r2_lattice3(sK0,k2_tarski(sK1,sK2),k13_lattice3(sK0,sK1,sK2))
    | spl7_2 ),
    inference(superposition,[],[f101,f790])).

fof(f790,plain,(
    ! [X4,X5,X3] :
      ( k13_lattice3(X4,X5,X3) = k1_yellow_0(X4,k2_tarski(X5,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ r2_lattice3(X4,k2_tarski(X5,X3),k13_lattice3(X4,X5,X3)) ) ),
    inference(subsumption_resolution,[],[f789,f86])).

fof(f789,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X3) = k1_yellow_0(X4,k2_tarski(X5,X3))
      | ~ r2_lattice3(X4,k2_tarski(X5,X3),k13_lattice3(X4,X5,X3))
      | ~ m1_subset_1(k13_lattice3(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f785,f578])).

fof(f578,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X1,k2_tarski(X2,X0),k13_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f577,f86])).

fof(f577,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r2_lattice3(X1,k2_tarski(X2,X0),k13_lattice3(X1,X2,X0))
      | ~ m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f564])).

fof(f564,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v1_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r2_lattice3(X1,k2_tarski(X2,X0),k13_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r1_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r2_lattice3(X1,k2_tarski(X2,X0),k13_lattice3(X1,X2,X0))
      | ~ m1_subset_1(k13_lattice3(X1,X2,X0),u1_struct_0(X1))
      | ~ v5_orders_2(X1) ) ),
    inference(resolution,[],[f292,f111])).

fof(f292,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,X9,sK5(X8,k2_tarski(X10,X11),k13_lattice3(X8,X9,X11)))
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ v1_lattice3(X8)
      | ~ v5_orders_2(X8)
      | r1_yellow_0(X8,k2_tarski(X10,X11))
      | ~ r2_lattice3(X8,k2_tarski(X10,X11),k13_lattice3(X8,X9,X11))
      | ~ m1_subset_1(X10,u1_struct_0(X8)) ) ),
    inference(subsumption_resolution,[],[f287,f86])).

fof(f287,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,X9,sK5(X8,k2_tarski(X10,X11),k13_lattice3(X8,X9,X11)))
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ v1_lattice3(X8)
      | ~ v5_orders_2(X8)
      | r1_yellow_0(X8,k2_tarski(X10,X11))
      | ~ r2_lattice3(X8,k2_tarski(X10,X11),k13_lattice3(X8,X9,X11))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ m1_subset_1(k13_lattice3(X8,X9,X11),u1_struct_0(X8)) ) ),
    inference(duplicate_literal_removal,[],[f280])).

fof(f280,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_orders_2(X8,X9,sK5(X8,k2_tarski(X10,X11),k13_lattice3(X8,X9,X11)))
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ m1_subset_1(X9,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | ~ v1_lattice3(X8)
      | ~ v5_orders_2(X8)
      | r1_yellow_0(X8,k2_tarski(X10,X11))
      | ~ r2_lattice3(X8,k2_tarski(X10,X11),k13_lattice3(X8,X9,X11))
      | ~ m1_subset_1(X11,u1_struct_0(X8))
      | ~ m1_subset_1(X10,u1_struct_0(X8))
      | ~ l1_orders_2(X8)
      | r1_yellow_0(X8,k2_tarski(X10,X11))
      | ~ r2_lattice3(X8,k2_tarski(X10,X11),k13_lattice3(X8,X9,X11))
      | ~ m1_subset_1(k13_lattice3(X8,X9,X11),u1_struct_0(X8))
      | ~ v5_orders_2(X8) ) ),
    inference(resolution,[],[f187,f117])).

fof(f785,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X3) = k1_yellow_0(X4,k2_tarski(X5,X3))
      | ~ r2_lattice3(X4,k2_tarski(X5,X3),k13_lattice3(X4,X5,X3))
      | ~ r1_yellow_0(X4,k2_tarski(X5,X3))
      | ~ m1_subset_1(k13_lattice3(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f770])).

fof(f770,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X3) = k1_yellow_0(X4,k2_tarski(X5,X3))
      | ~ r2_lattice3(X4,k2_tarski(X5,X3),k13_lattice3(X4,X5,X3))
      | ~ r1_yellow_0(X4,k2_tarski(X5,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r2_lattice3(X4,k2_tarski(X5,X3),k13_lattice3(X4,X5,X3))
      | ~ r1_yellow_0(X4,k2_tarski(X5,X3))
      | ~ m1_subset_1(k13_lattice3(X4,X5,X3),u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | k13_lattice3(X4,X5,X3) = k1_yellow_0(X4,k2_tarski(X5,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f307,f123])).

fof(f123,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_orders_2(X4,X5,sK3(X4,k2_tarski(X5,X6),X7))
      | ~ r2_lattice3(X4,k2_tarski(X5,X6),X7)
      | ~ r1_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | k1_yellow_0(X4,k2_tarski(X5,X6)) = X7
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f120,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
                & r2_lattice3(X0,X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X2,X3)
          & r2_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
        & r2_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X2,X4)
                    | ~ r2_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X2,X3)
                    | ~ r2_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r2_lattice3(X0,X1,X2) )
              | k1_yellow_0(X0,X1) != X2 ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X2,X3)
                  | ~ r2_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r2_lattice3(X0,X1,X2) ) )
          | ~ r1_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r1_yellow_0(X0,X1)
           => ( k1_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r2_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X2,X3) ) )
                & r2_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_yellow_0)).

fof(f120,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_yellow_0(X4,k2_tarski(X5,X6)) = X7
      | ~ r2_lattice3(X4,k2_tarski(X5,X6),X7)
      | ~ r1_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r1_orders_2(X4,X5,sK3(X4,k2_tarski(X5,X6),X7))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK3(X4,k2_tarski(X5,X6),X7),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X6,X4,X7,X5] :
      ( k1_yellow_0(X4,k2_tarski(X5,X6)) = X7
      | ~ r2_lattice3(X4,k2_tarski(X5,X6),X7)
      | ~ r1_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r1_orders_2(X4,X5,sK3(X4,k2_tarski(X5,X6),X7))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK3(X4,k2_tarski(X5,X6),X7),u1_struct_0(X4))
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f69,f63])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_lattice3(X0,X1,sK3(X0,X1,X2))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f307,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X7) = k1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ m1_subset_1(X6,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f304,f86])).

fof(f304,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X7) = k1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ m1_subset_1(k13_lattice3(X4,X5,X7),u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f295])).

fof(f295,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X7) = k1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ r2_lattice3(X4,k2_tarski(X6,X7),k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ m1_subset_1(k13_lattice3(X4,X5,X7),u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | k13_lattice3(X4,X5,X7) = k1_yellow_0(X4,k2_tarski(X6,X7))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f189,f122])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X2,sK3(X0,k2_tarski(X1,X2),X3))
      | ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k1_yellow_0(X0,k2_tarski(X1,X2)) = X3
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f121,f68])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_yellow_0(X0,k2_tarski(X1,X2)) = X3
      | ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X2,sK3(X0,k2_tarski(X1,X2),X3))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0,k2_tarski(X1,X2),X3),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f118])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_yellow_0(X0,k2_tarski(X1,X2)) = X3
      | ~ r2_lattice3(X0,k2_tarski(X1,X2),X3)
      | ~ r1_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,X2,sK3(X0,k2_tarski(X1,X2),X3))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0,k2_tarski(X1,X2),X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f69,f64])).

fof(f189,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X7,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ r1_orders_2(X4,X5,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X7) = k1_yellow_0(X4,X6)
      | ~ r2_lattice3(X4,X6,k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,X6) ) ),
    inference(subsumption_resolution,[],[f188,f86])).

fof(f188,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ r1_orders_2(X4,X7,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X7) = k1_yellow_0(X4,X6)
      | ~ r2_lattice3(X4,X6,k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,X6)
      | ~ m1_subset_1(k13_lattice3(X4,X5,X7),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f184,f68])).

fof(f184,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(sK3(X4,X6,k13_lattice3(X4,X5,X7)),u1_struct_0(X4))
      | ~ r1_orders_2(X4,X7,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X7) = k1_yellow_0(X4,X6)
      | ~ r2_lattice3(X4,X6,k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,X6)
      | ~ m1_subset_1(k13_lattice3(X4,X5,X7),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,X5,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(sK3(X4,X6,k13_lattice3(X4,X5,X7)),u1_struct_0(X4))
      | ~ r1_orders_2(X4,X7,sK3(X4,X6,k13_lattice3(X4,X5,X7)))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v1_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k13_lattice3(X4,X5,X7) = k1_yellow_0(X4,X6)
      | ~ r2_lattice3(X4,X6,k13_lattice3(X4,X5,X7))
      | ~ r1_yellow_0(X4,X6)
      | ~ m1_subset_1(k13_lattice3(X4,X5,X7),u1_struct_0(X4))
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f159,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X2,sK3(X0,X1,X2))
      | k1_yellow_0(X0,X1) = X2
      | ~ r2_lattice3(X0,X1,X2)
      | ~ r1_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,
    ( k13_lattice3(sK0,sK1,sK2) != k1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | spl7_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl7_2
  <=> k13_lattice3(sK0,sK1,sK2) = k1_yellow_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f102,plain,
    ( spl7_1
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f95,f100,f97])).

fof(f95,plain,
    ( k13_lattice3(sK0,sK1,sK2) != k1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f94,f55])).

fof(f94,plain,
    ( k13_lattice3(sK0,sK1,sK2) != k1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f93,f56])).

fof(f93,plain,
    ( k13_lattice3(sK0,sK1,sK2) != k1_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f57,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,X0)
        & m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(f57,plain,(
    k13_lattice3(sK0,sK1,sK2) != k1_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(cnf_transformation,[],[f36])).

%------------------------------------------------------------------------------
