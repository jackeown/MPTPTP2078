%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1562+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:06 EST 2020

% Result     : Theorem 2.40s
% Output     : Refutation 2.40s
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
fof(f2228,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f126,f2219])).

fof(f2219,plain,(
    spl7_4 ),
    inference(avatar_contradiction_clause,[],[f2218])).

fof(f2218,plain,
    ( $false
    | spl7_4 ),
    inference(subsumption_resolution,[],[f2217,f61])).

fof(f61,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k12_lattice3(sK0,sK1,sK2) != k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK1,sK2))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v5_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k12_lattice3(X0,X1,X2) != k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(sK0,X1,X2) != k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v5_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k12_lattice3(sK0,X1,X2) != k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),X1,X2))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k12_lattice3(sK0,sK1,X2) != k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK1,X2))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( k12_lattice3(sK0,sK1,X2) != k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK1,X2))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k12_lattice3(sK0,sK1,sK2) != k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK1,sK2))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,X2) != k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k12_lattice3(X0,X1,X2) != k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f14,plain,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k12_lattice3(X0,X1,X2) = k2_yellow_0(X0,k7_domain_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_yellow_0)).

fof(f2217,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl7_4 ),
    inference(subsumption_resolution,[],[f2216,f58])).

fof(f58,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f2216,plain,
    ( ~ v2_lattice3(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl7_4 ),
    inference(subsumption_resolution,[],[f2215,f60])).

fof(f60,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f41])).

fof(f2215,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl7_4 ),
    inference(subsumption_resolution,[],[f2214,f57])).

fof(f57,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f2214,plain,
    ( ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl7_4 ),
    inference(subsumption_resolution,[],[f2209,f59])).

fof(f59,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f41])).

fof(f2209,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v2_lattice3(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl7_4 ),
    inference(resolution,[],[f2124,f1341])).

fof(f1341,plain,(
    ! [X76,X77,X75] :
      ( r1_lattice3(X75,k2_tarski(X76,X77),k12_lattice3(X75,X76,X77))
      | ~ l1_orders_2(X75)
      | ~ v5_orders_2(X75)
      | ~ m1_subset_1(X76,u1_struct_0(X75))
      | ~ v2_lattice3(X75)
      | ~ m1_subset_1(X77,u1_struct_0(X75)) ) ),
    inference(subsumption_resolution,[],[f1320,f1238])).

fof(f1238,plain,(
    ! [X2,X0,X1] :
      ( r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1237,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k12_lattice3)).

fof(f1237,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(k12_lattice3(X1,X0,X2),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1236,f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f167])).

fof(f167,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f97,f93])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f49,f50])).

fof(f50,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
        & m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k12_lattice3(X0,X1,X2) = X3
                      | ? [X4] :
                          ( ~ r1_orders_2(X0,X4,X3)
                          & r1_orders_2(X0,X4,X2)
                          & r1_orders_2(X0,X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X4] :
                            ( r1_orders_2(X0,X4,X3)
                            | ~ r1_orders_2(X0,X4,X2)
                            | ~ r1_orders_2(X0,X4,X1)
                            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k12_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r1_orders_2(X0,X4,X3)
                          | ~ r1_orders_2(X0,X4,X2)
                          | ~ r1_orders_2(X0,X4,X1)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k12_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_yellow_0)).

fof(f1236,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_orders_2(X1,k12_lattice3(X1,X0,X2),X2)
      | ~ m1_subset_1(k12_lattice3(X1,X0,X2),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f1235,f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f98,f93])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | r1_orders_2(X0,k12_lattice3(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X1)
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1235,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_orders_2(X1,k12_lattice3(X1,X0,X2),X0)
      | ~ r1_orders_2(X1,k12_lattice3(X1,X0,X2),X2)
      | ~ m1_subset_1(k12_lattice3(X1,X0,X2),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f1226])).

fof(f1226,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r1_orders_2(X1,k12_lattice3(X1,X0,X2),X0)
      | ~ r1_orders_2(X1,k12_lattice3(X1,X0,X2),X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(k12_lattice3(X1,X0,X2),u1_struct_0(X1))
      | ~ l1_orders_2(X1) ) ),
    inference(resolution,[],[f510,f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_yellow_0)).

fof(f510,plain,(
    ! [X4,X5,X3] :
      ( ~ r1_lattice3(X4,k2_tarski(X3,X5),k12_lattice3(X4,X5,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X3,X5))
      | ~ m1_subset_1(X3,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f507,f93])).

fof(f507,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X3,X5))
      | ~ r1_lattice3(X4,k2_tarski(X3,X5),k12_lattice3(X4,X5,X3))
      | ~ m1_subset_1(k12_lattice3(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f498])).

fof(f498,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X3,X5))
      | ~ r1_lattice3(X4,k2_tarski(X3,X5),k12_lattice3(X4,X5,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X3,X5))
      | ~ r1_lattice3(X4,k2_tarski(X3,X5),k12_lattice3(X4,X5,X3))
      | ~ m1_subset_1(k12_lattice3(X4,X5,X3),u1_struct_0(X4))
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f336,f145])).

fof(f145,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK5(X3,k2_tarski(X4,X5),X6),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f142,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
                  & r1_lattice3(X0,X1,sK5(X0,X1,X2))
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ( ! [X5] :
                  ( r1_orders_2(X0,X5,sK6(X0,X1))
                  | ~ r1_lattice3(X0,X1,X5)
                  | ~ m1_subset_1(X5,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,sK6(X0,X1))
              & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f53,f55,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK5(X0,X1,X2))
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( ! [X5] :
              ( r1_orders_2(X0,X5,X4)
              | ~ r1_lattice3(X0,X1,X5)
              | ~ m1_subset_1(X5,u1_struct_0(X0)) )
          & r1_lattice3(X0,X1,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ! [X5] :
            ( r1_orders_2(X0,X5,sK6(X0,X1))
            | ~ r1_lattice3(X0,X1,X5)
            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
        & r1_lattice3(X0,X1,sK6(X0,X1))
        & m1_subset_1(sK6(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X4] :
                ( ! [X5] :
                    ( r1_orders_2(X0,X5,X4)
                    | ~ r1_lattice3(X0,X1,X5)
                    | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X4)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
            | ! [X2] :
                ( ? [X3] :
                    ( ~ r1_orders_2(X0,X3,X2)
                    & r1_lattice3(X0,X1,X3)
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r1_lattice3(X0,X1,X2)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & ( ? [X2] :
                ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ r2_yellow_0(X0,X1) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( r2_yellow_0(X0,X1)
        <=> ? [X2] :
              ( ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r1_lattice3(X0,X1,X3)
                   => r1_orders_2(X0,X3,X2) ) )
              & r1_lattice3(X0,X1,X2)
              & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_yellow_0)).

fof(f142,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK5(X3,k2_tarski(X4,X5),X6),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK5(X3,k2_tarski(X4,X5),X6),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(resolution,[],[f66,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f336,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,k2_tarski(X1,X2),k12_lattice3(X0,X3,X1)),X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),k12_lattice3(X0,X3,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f335,f93])).

fof(f335,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,k2_tarski(X1,X2),k12_lattice3(X0,X3,X1)),X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),k12_lattice3(X0,X3,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(k12_lattice3(X0,X3,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f324])).

fof(f324,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,k2_tarski(X1,X2),k12_lattice3(X0,X3,X1)),X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),k12_lattice3(X0,X3,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),k12_lattice3(X0,X3,X1))
      | ~ m1_subset_1(k12_lattice3(X0,X3,X1),u1_struct_0(X0))
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f225,f139])).

fof(f139,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK5(X3,k2_tarski(X4,X5),X6),X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(subsumption_resolution,[],[f136,f87])).

fof(f136,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK5(X3,k2_tarski(X4,X5),X6),X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ v5_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f135])).

fof(f135,plain,(
    ! [X6,X4,X5,X3] :
      ( r1_orders_2(X3,sK5(X3,k2_tarski(X4,X5),X6),X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK5(X3,k2_tarski(X4,X5),X6),u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | r2_yellow_0(X3,k2_tarski(X4,X5))
      | ~ r1_lattice3(X3,k2_tarski(X4,X5),X6)
      | ~ m1_subset_1(X6,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(resolution,[],[f65,f88])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_lattice3(X0,k2_tarski(X2,X3),X1)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f225,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X3)
      | ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,k12_lattice3(X0,X2,X3)) ) ),
    inference(subsumption_resolution,[],[f224,f93])).

fof(f224,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X2)
      | ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,k12_lattice3(X0,X2,X3))
      | ~ m1_subset_1(k12_lattice3(X0,X2,X3),u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f223,f87])).

fof(f223,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X2)
      | ~ m1_subset_1(sK5(X0,X1,k12_lattice3(X0,X2,X3)),u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,k12_lattice3(X0,X2,X3))
      | ~ m1_subset_1(k12_lattice3(X0,X2,X3),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f214])).

fof(f214,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X2)
      | ~ m1_subset_1(sK5(X0,X1,k12_lattice3(X0,X2,X3)),u1_struct_0(X0))
      | ~ r1_orders_2(X0,sK5(X0,X1,k12_lattice3(X0,X2,X3)),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,k12_lattice3(X0,X2,X3))
      | ~ m1_subset_1(k12_lattice3(X0,X2,X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f180,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK5(X0,X1,X2),X2)
      | r2_yellow_0(X0,X1)
      | ~ r1_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f180,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X1,k12_lattice3(X0,X3,X2))
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | ~ r1_orders_2(X0,X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,k12_lattice3(X0,X3,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f96,f93])).

fof(f96,plain,(
    ! [X2,X0,X5,X1] :
      ( ~ m1_subset_1(k12_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | r1_orders_2(X0,X5,k12_lattice3(X0,X1,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r1_orders_2(X0,X5,X3)
      | ~ r1_orders_2(X0,X5,X2)
      | ~ r1_orders_2(X0,X5,X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | k12_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1320,plain,(
    ! [X76,X77,X75] :
      ( r1_lattice3(X75,k2_tarski(X76,X77),k12_lattice3(X75,X76,X77))
      | ~ r2_yellow_0(X75,k2_tarski(X76,X77))
      | ~ l1_orders_2(X75)
      | ~ v5_orders_2(X75)
      | ~ m1_subset_1(X76,u1_struct_0(X75))
      | ~ v2_lattice3(X75)
      | ~ m1_subset_1(X77,u1_struct_0(X75)) ) ),
    inference(duplicate_literal_removal,[],[f1291])).

fof(f1291,plain,(
    ! [X76,X77,X75] :
      ( r1_lattice3(X75,k2_tarski(X76,X77),k12_lattice3(X75,X76,X77))
      | ~ r2_yellow_0(X75,k2_tarski(X76,X77))
      | ~ l1_orders_2(X75)
      | ~ v5_orders_2(X75)
      | ~ m1_subset_1(X76,u1_struct_0(X75))
      | ~ l1_orders_2(X75)
      | ~ v2_lattice3(X75)
      | ~ v5_orders_2(X75)
      | ~ m1_subset_1(X77,u1_struct_0(X75))
      | ~ r2_yellow_0(X75,k2_tarski(X76,X77)) ) ),
    inference(superposition,[],[f85,f746])).

fof(f746,plain,(
    ! [X2,X0,X1] :
      ( k12_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_yellow_0(X1,k2_tarski(X2,X0)) ) ),
    inference(subsumption_resolution,[],[f745,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK6(X0,X1),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f745,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k12_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(sK6(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f744,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK6(X0,k2_tarski(X1,X2)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f143,f84])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK6(X0,k2_tarski(X1,X2)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK6(X0,k2_tarski(X1,X2)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f66,f85])).

fof(f744,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k12_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,sK6(X1,k2_tarski(X2,X0)),X0)
      | ~ m1_subset_1(sK6(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f743,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK6(X0,k2_tarski(X1,X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f137,f84])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK6(X0,k2_tarski(X1,X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,sK6(X0,k2_tarski(X1,X2)),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK6(X0,k2_tarski(X1,X2)),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f65,f85])).

fof(f743,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k12_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,sK6(X1,k2_tarski(X2,X0)),X2)
      | ~ r1_orders_2(X1,sK6(X1,k2_tarski(X2,X0)),X0)
      | ~ m1_subset_1(sK6(X1,k2_tarski(X2,X0)),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f732])).

fof(f732,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | k12_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,sK6(X1,k2_tarski(X2,X0)),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k12_lattice3(X1,X2,X0) = sK6(X1,k2_tarski(X2,X0))
      | ~ r1_orders_2(X1,sK6(X1,k2_tarski(X2,X0)),X0)
      | ~ r1_orders_2(X1,sK6(X1,k2_tarski(X2,X0)),X2)
      | ~ m1_subset_1(sK6(X1,k2_tarski(X2,X0)),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1) ) ),
    inference(resolution,[],[f432,f81])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK4(X0,X1,X2,X3),X1)
      | k12_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f432,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK4(X4,X7,X6,sK6(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k12_lattice3(X4,X7,X6) = sK6(X4,k2_tarski(X5,X6))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK6(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X5,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f431,f84])).

fof(f431,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK6(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k12_lattice3(X4,X7,X6) = sK6(X4,k2_tarski(X5,X6))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK4(X4,X7,X6,sK6(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK6(X4,k2_tarski(X5,X6)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f430,f144])).

fof(f430,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK6(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k12_lattice3(X4,X7,X6) = sK6(X4,k2_tarski(X5,X6))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK6(X4,k2_tarski(X5,X6)),X6)
      | ~ r1_orders_2(X4,sK4(X4,X7,X6,sK6(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK6(X4,k2_tarski(X5,X6)),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f426,f80])).

fof(f80,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X3),u1_struct_0(X0))
      | k12_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f426,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK6(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k12_lattice3(X4,X7,X6) = sK6(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(sK4(X4,X7,X6,sK6(X4,k2_tarski(X5,X6))),u1_struct_0(X4))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK6(X4,k2_tarski(X5,X6)),X6)
      | ~ r1_orders_2(X4,sK4(X4,X7,X6,sK6(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK6(X4,k2_tarski(X5,X6)),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f419])).

fof(f419,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK6(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k12_lattice3(X4,X7,X6) = sK6(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(sK4(X4,X7,X6,sK6(X4,k2_tarski(X5,X6))),u1_struct_0(X4))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK6(X4,k2_tarski(X5,X6)),X6)
      | ~ r1_orders_2(X4,sK4(X4,X7,X6,sK6(X4,k2_tarski(X5,X6))),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | k12_lattice3(X4,X7,X6) = sK6(X4,k2_tarski(X5,X6))
      | ~ r1_orders_2(X4,sK6(X4,k2_tarski(X5,X6)),X6)
      | ~ r1_orders_2(X4,sK6(X4,k2_tarski(X5,X6)),X7)
      | ~ m1_subset_1(sK6(X4,k2_tarski(X5,X6)),u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f267,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK4(X0,X1,X2,X3),X2)
      | k12_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f267,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X4,X3,sK6(X0,k2_tarski(X1,X2))),X2)
      | ~ r1_orders_2(X0,sK6(X0,k2_tarski(X1,X2)),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sK6(X0,k2_tarski(X1,X2)) = k12_lattice3(X0,X4,X3)
      | ~ m1_subset_1(sK4(X0,X4,X3,sK6(X0,k2_tarski(X1,X2))),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,sK6(X0,k2_tarski(X1,X2)),X3)
      | ~ r1_orders_2(X0,sK4(X0,X4,X3,sK6(X0,k2_tarski(X1,X2))),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f266])).

fof(f266,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK6(X0,k2_tarski(X1,X2)),X3)
      | ~ r1_orders_2(X0,sK6(X0,k2_tarski(X1,X2)),X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | sK6(X0,k2_tarski(X1,X2)) = k12_lattice3(X0,X4,X3)
      | ~ m1_subset_1(sK4(X0,X4,X3,sK6(X0,k2_tarski(X1,X2))),u1_struct_0(X0))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_orders_2(X0,sK4(X0,X4,X3,sK6(X0,k2_tarski(X1,X2))),X2)
      | ~ r1_orders_2(X0,sK4(X0,X4,X3,sK6(X0,k2_tarski(X1,X2))),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK4(X0,X4,X3,sK6(X0,k2_tarski(X1,X2))),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f178,f67])).

fof(f178,plain,(
    ! [X6,X8,X7,X9] :
      ( ~ r1_lattice3(X6,X9,sK4(X6,X7,X8,sK6(X6,X9)))
      | ~ r1_orders_2(X6,sK6(X6,X9),X8)
      | ~ r1_orders_2(X6,sK6(X6,X9),X7)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v5_orders_2(X6)
      | k12_lattice3(X6,X7,X8) = sK6(X6,X9)
      | ~ m1_subset_1(sK4(X6,X7,X8,sK6(X6,X9)),u1_struct_0(X6))
      | ~ r2_yellow_0(X6,X9) ) ),
    inference(subsumption_resolution,[],[f175,f84])).

fof(f175,plain,(
    ! [X6,X8,X7,X9] :
      ( k12_lattice3(X6,X7,X8) = sK6(X6,X9)
      | ~ r1_orders_2(X6,sK6(X6,X9),X8)
      | ~ r1_orders_2(X6,sK6(X6,X9),X7)
      | ~ m1_subset_1(sK6(X6,X9),u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v5_orders_2(X6)
      | ~ r1_lattice3(X6,X9,sK4(X6,X7,X8,sK6(X6,X9)))
      | ~ m1_subset_1(sK4(X6,X7,X8,sK6(X6,X9)),u1_struct_0(X6))
      | ~ r2_yellow_0(X6,X9) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X6,X8,X7,X9] :
      ( k12_lattice3(X6,X7,X8) = sK6(X6,X9)
      | ~ r1_orders_2(X6,sK6(X6,X9),X8)
      | ~ r1_orders_2(X6,sK6(X6,X9),X7)
      | ~ m1_subset_1(sK6(X6,X9),u1_struct_0(X6))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l1_orders_2(X6)
      | ~ v2_lattice3(X6)
      | ~ v5_orders_2(X6)
      | ~ r1_lattice3(X6,X9,sK4(X6,X7,X8,sK6(X6,X9)))
      | ~ m1_subset_1(sK4(X6,X7,X8,sK6(X6,X9)),u1_struct_0(X6))
      | ~ r2_yellow_0(X6,X9)
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6) ) ),
    inference(resolution,[],[f83,f86])).

fof(f86,plain,(
    ! [X0,X5,X1] :
      ( r1_orders_2(X0,X5,sK6(X0,X1))
      | ~ r1_lattice3(X0,X1,X5)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK4(X0,X1,X2,X3),X3)
      | k12_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f85,plain,(
    ! [X0,X1] :
      ( r1_lattice3(X0,X1,sK6(X0,X1))
      | ~ r2_yellow_0(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f2124,plain,
    ( ~ r1_lattice3(sK0,k2_tarski(sK1,sK2),k12_lattice3(sK0,sK1,sK2))
    | spl7_4 ),
    inference(subsumption_resolution,[],[f2123,f61])).

fof(f2123,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_tarski(sK1,sK2),k12_lattice3(sK0,sK1,sK2))
    | spl7_4 ),
    inference(subsumption_resolution,[],[f2122,f57])).

fof(f2122,plain,
    ( ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_tarski(sK1,sK2),k12_lattice3(sK0,sK1,sK2))
    | spl7_4 ),
    inference(subsumption_resolution,[],[f2121,f58])).

fof(f2121,plain,
    ( ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_tarski(sK1,sK2),k12_lattice3(sK0,sK1,sK2))
    | spl7_4 ),
    inference(subsumption_resolution,[],[f2120,f59])).

fof(f2120,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_tarski(sK1,sK2),k12_lattice3(sK0,sK1,sK2))
    | spl7_4 ),
    inference(subsumption_resolution,[],[f2111,f60])).

fof(f2111,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_tarski(sK1,sK2),k12_lattice3(sK0,sK1,sK2))
    | spl7_4 ),
    inference(trivial_inequality_removal,[],[f2086])).

fof(f2086,plain,
    ( k12_lattice3(sK0,sK1,sK2) != k12_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ r1_lattice3(sK0,k2_tarski(sK1,sK2),k12_lattice3(sK0,sK1,sK2))
    | spl7_4 ),
    inference(superposition,[],[f125,f779])).

fof(f779,plain,(
    ! [X4,X5,X3] :
      ( k12_lattice3(X4,X5,X3) = k2_yellow_0(X4,k2_tarski(X5,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ r1_lattice3(X4,k2_tarski(X5,X3),k12_lattice3(X4,X5,X3)) ) ),
    inference(subsumption_resolution,[],[f778,f93])).

fof(f778,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k12_lattice3(X4,X5,X3) = k2_yellow_0(X4,k2_tarski(X5,X3))
      | ~ r1_lattice3(X4,k2_tarski(X5,X3),k12_lattice3(X4,X5,X3))
      | ~ m1_subset_1(k12_lattice3(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f774,f530])).

fof(f530,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X1,k2_tarski(X2,X0),k12_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f529,f93])).

fof(f529,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_lattice3(X1,k2_tarski(X2,X0),k12_lattice3(X1,X2,X0))
      | ~ m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f518])).

fof(f518,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v2_lattice3(X1)
      | ~ v5_orders_2(X1)
      | r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_lattice3(X1,k2_tarski(X2,X0),k12_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | r2_yellow_0(X1,k2_tarski(X2,X0))
      | ~ r1_lattice3(X1,k2_tarski(X2,X0),k12_lattice3(X1,X2,X0))
      | ~ m1_subset_1(k12_lattice3(X1,X2,X0),u1_struct_0(X1))
      | ~ v5_orders_2(X1) ) ),
    inference(resolution,[],[f337,f139])).

fof(f337,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK5(X4,k2_tarski(X5,X6),k12_lattice3(X4,X7,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_lattice3(X4,k2_tarski(X5,X6),k12_lattice3(X4,X7,X6))
      | ~ m1_subset_1(X5,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f334,f93])).

fof(f334,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK5(X4,k2_tarski(X5,X6),k12_lattice3(X4,X7,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_lattice3(X4,k2_tarski(X5,X6),k12_lattice3(X4,X7,X6))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(k12_lattice3(X4,X7,X6),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK5(X4,k2_tarski(X5,X6),k12_lattice3(X4,X7,X6)),X7)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_lattice3(X4,k2_tarski(X5,X6),k12_lattice3(X4,X7,X6))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ r1_lattice3(X4,k2_tarski(X5,X6),k12_lattice3(X4,X7,X6))
      | ~ m1_subset_1(k12_lattice3(X4,X7,X6),u1_struct_0(X4))
      | ~ v5_orders_2(X4) ) ),
    inference(resolution,[],[f225,f145])).

fof(f774,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k12_lattice3(X4,X5,X3) = k2_yellow_0(X4,k2_tarski(X5,X3))
      | ~ r1_lattice3(X4,k2_tarski(X5,X3),k12_lattice3(X4,X5,X3))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X3))
      | ~ m1_subset_1(k12_lattice3(X4,X5,X3),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f759])).

fof(f759,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k12_lattice3(X4,X5,X3) = k2_yellow_0(X4,k2_tarski(X5,X3))
      | ~ r1_lattice3(X4,k2_tarski(X5,X3),k12_lattice3(X4,X5,X3))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X3))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ r1_lattice3(X4,k2_tarski(X5,X3),k12_lattice3(X4,X5,X3))
      | ~ r2_yellow_0(X4,k2_tarski(X5,X3))
      | ~ m1_subset_1(k12_lattice3(X4,X5,X3),u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | k12_lattice3(X4,X5,X3) = k2_yellow_0(X4,k2_tarski(X5,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f352,f153])).

fof(f153,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_orders_2(X4,sK3(X4,k2_tarski(X5,X6),X7),X5)
      | ~ r1_lattice3(X4,k2_tarski(X5,X6),X7)
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | k2_yellow_0(X4,k2_tarski(X5,X6)) = X7
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f150,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r1_lattice3(X0,X1,sK3(X0,X1,X2))
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r1_lattice3(X0,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r1_lattice3(X0,X1,sK3(X0,X1,X2))
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X4] :
                    ( r1_orders_2(X0,X4,X2)
                    | ~ r1_lattice3(X0,X1,X4)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k2_yellow_0(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r1_lattice3(X0,X1,X3)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r1_lattice3(X0,X1,X2) )
            & ( ( ! [X3] :
                    ( r1_orders_2(X0,X3,X2)
                    | ~ r1_lattice3(X0,X1,X3)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r1_lattice3(X0,X1,X2) )
              | k2_yellow_0(X0,X1) != X2 ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k2_yellow_0(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r1_lattice3(X0,X1,X3)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r1_lattice3(X0,X1,X2) ) )
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_yellow_0(X0,X1)
           => ( k2_yellow_0(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r1_lattice3(X0,X1,X3)
                     => r1_orders_2(X0,X3,X2) ) )
                & r1_lattice3(X0,X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_yellow_0)).

fof(f150,plain,(
    ! [X6,X4,X7,X5] :
      ( k2_yellow_0(X4,k2_tarski(X5,X6)) = X7
      | ~ r1_lattice3(X4,k2_tarski(X5,X6),X7)
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r1_orders_2(X4,sK3(X4,k2_tarski(X5,X6),X7),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK3(X4,k2_tarski(X5,X6),X7),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f149])).

fof(f149,plain,(
    ! [X6,X4,X7,X5] :
      ( k2_yellow_0(X4,k2_tarski(X5,X6)) = X7
      | ~ r1_lattice3(X4,k2_tarski(X5,X6),X7)
      | ~ r2_yellow_0(X4,k2_tarski(X5,X6))
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | r1_orders_2(X4,sK3(X4,k2_tarski(X5,X6),X7),X5)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(sK3(X4,k2_tarski(X5,X6),X7),u1_struct_0(X4))
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f74,f65])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_lattice3(X0,X1,sK3(X0,X1,X2))
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f352,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,k2_tarski(X1,X2),k12_lattice3(X0,X3,X2)),X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k2_yellow_0(X0,k2_tarski(X1,X2)) = k12_lattice3(X0,X3,X2)
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),k12_lattice3(X0,X3,X2))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f351,f93])).

fof(f351,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,k2_tarski(X1,X2),k12_lattice3(X0,X3,X2)),X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k2_yellow_0(X0,k2_tarski(X1,X2)) = k12_lattice3(X0,X3,X2)
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),k12_lattice3(X0,X3,X2))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k12_lattice3(X0,X3,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f340])).

fof(f340,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,k2_tarski(X1,X2),k12_lattice3(X0,X3,X2)),X3)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k2_yellow_0(X0,k2_tarski(X1,X2)) = k12_lattice3(X0,X3,X2)
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),k12_lattice3(X0,X3,X2))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),k12_lattice3(X0,X3,X2))
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(k12_lattice3(X0,X3,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,k2_tarski(X1,X2)) = k12_lattice3(X0,X3,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f227,f152])).

fof(f152,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK3(X0,k2_tarski(X1,X2),X3),X2)
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | k2_yellow_0(X0,k2_tarski(X1,X2)) = X3
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(subsumption_resolution,[],[f151,f73])).

fof(f151,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_yellow_0(X0,k2_tarski(X1,X2)) = X3
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK3(X0,k2_tarski(X1,X2),X3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0,k2_tarski(X1,X2),X3),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f148])).

fof(f148,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_yellow_0(X0,k2_tarski(X1,X2)) = X3
      | ~ r1_lattice3(X0,k2_tarski(X1,X2),X3)
      | ~ r2_yellow_0(X0,k2_tarski(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | r1_orders_2(X0,sK3(X0,k2_tarski(X1,X2),X3),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK3(X0,k2_tarski(X1,X2),X3),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(resolution,[],[f74,f66])).

fof(f227,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK3(X4,X5,k12_lattice3(X4,X6,X7)),X7)
      | ~ r1_orders_2(X4,sK3(X4,X5,k12_lattice3(X4,X6,X7)),X6)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k12_lattice3(X4,X6,X7) = k2_yellow_0(X4,X5)
      | ~ r1_lattice3(X4,X5,k12_lattice3(X4,X6,X7))
      | ~ r2_yellow_0(X4,X5) ) ),
    inference(subsumption_resolution,[],[f226,f93])).

fof(f226,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK3(X4,X5,k12_lattice3(X4,X6,X7)),X6)
      | ~ r1_orders_2(X4,sK3(X4,X5,k12_lattice3(X4,X6,X7)),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k12_lattice3(X4,X6,X7) = k2_yellow_0(X4,X5)
      | ~ r1_lattice3(X4,X5,k12_lattice3(X4,X6,X7))
      | ~ r2_yellow_0(X4,X5)
      | ~ m1_subset_1(k12_lattice3(X4,X6,X7),u1_struct_0(X4)) ) ),
    inference(subsumption_resolution,[],[f222,f73])).

fof(f222,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK3(X4,X5,k12_lattice3(X4,X6,X7)),X6)
      | ~ m1_subset_1(sK3(X4,X5,k12_lattice3(X4,X6,X7)),u1_struct_0(X4))
      | ~ r1_orders_2(X4,sK3(X4,X5,k12_lattice3(X4,X6,X7)),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k12_lattice3(X4,X6,X7) = k2_yellow_0(X4,X5)
      | ~ r1_lattice3(X4,X5,k12_lattice3(X4,X6,X7))
      | ~ r2_yellow_0(X4,X5)
      | ~ m1_subset_1(k12_lattice3(X4,X6,X7),u1_struct_0(X4)) ) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_orders_2(X4,sK3(X4,X5,k12_lattice3(X4,X6,X7)),X6)
      | ~ m1_subset_1(sK3(X4,X5,k12_lattice3(X4,X6,X7)),u1_struct_0(X4))
      | ~ r1_orders_2(X4,sK3(X4,X5,k12_lattice3(X4,X6,X7)),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l1_orders_2(X4)
      | ~ v2_lattice3(X4)
      | ~ v5_orders_2(X4)
      | k12_lattice3(X4,X6,X7) = k2_yellow_0(X4,X5)
      | ~ r1_lattice3(X4,X5,k12_lattice3(X4,X6,X7))
      | ~ r2_yellow_0(X4,X5)
      | ~ m1_subset_1(k12_lattice3(X4,X6,X7),u1_struct_0(X4))
      | ~ l1_orders_2(X4) ) ),
    inference(resolution,[],[f180,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | k2_yellow_0(X0,X1) = X2
      | ~ r1_lattice3(X0,X1,X2)
      | ~ r2_yellow_0(X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f125,plain,
    ( k12_lattice3(sK0,sK1,sK2) != k2_yellow_0(sK0,k2_tarski(sK1,sK2))
    | spl7_4 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl7_4
  <=> k12_lattice3(sK0,sK1,sK2) = k2_yellow_0(sK0,k2_tarski(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f126,plain,
    ( spl7_2
    | ~ spl7_4 ),
    inference(avatar_split_clause,[],[f122,f124,f106])).

fof(f106,plain,
    ( spl7_2
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f122,plain,
    ( k12_lattice3(sK0,sK1,sK2) != k2_yellow_0(sK0,k2_tarski(sK1,sK2))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f121,f60])).

fof(f121,plain,
    ( k12_lattice3(sK0,sK1,sK2) != k2_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f116,f61])).

fof(f116,plain,
    ( k12_lattice3(sK0,sK1,sK2) != k2_yellow_0(sK0,k2_tarski(sK1,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(superposition,[],[f62,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k7_domain_1(X0,X1,X2) = k2_tarski(X1,X2)
      | ~ m1_subset_1(X2,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_domain_1)).

fof(f62,plain,(
    k12_lattice3(sK0,sK1,sK2) != k2_yellow_0(sK0,k7_domain_1(u1_struct_0(sK0),sK1,sK2)) ),
    inference(cnf_transformation,[],[f41])).

fof(f120,plain,(
    ~ spl7_2 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f118,f59])).

fof(f118,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f117,f58])).

fof(f117,plain,
    ( ~ v2_lattice3(sK0)
    | ~ l1_orders_2(sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f115,f64])).

fof(f64,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f115,plain,
    ( v2_struct_0(sK0)
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f114,f99])).

fof(f99,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f63,f59])).

fof(f63,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f114,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_2 ),
    inference(resolution,[],[f107,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f107,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f106])).

%------------------------------------------------------------------------------
