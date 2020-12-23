%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1572+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:07 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  198 (10707924 expanded)
%              Number of leaves         :   10 (3762915 expanded)
%              Depth                    :  104
%              Number of atoms          :  962 (80077881 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   11 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f484,plain,(
    $false ),
    inference(global_subsumption,[],[f482,f481])).

fof(f481,plain,(
    ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    inference(unit_resulting_resolution,[],[f35,f36,f430,f434,f479,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattice3(X0,X2,sK5(X0,X1,X2))
      | ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | ~ r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ( ( ~ r1_lattice3(X0,X2,sK5(X0,X1,X2))
              | ~ r1_lattice3(X0,X1,sK5(X0,X1,X2)) )
            & ( r1_lattice3(X0,X2,sK5(X0,X1,X2))
              | r1_lattice3(X0,X1,sK5(X0,X1,X2)) )
            & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f28,f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r1_lattice3(X0,X2,X3)
            | ~ r1_lattice3(X0,X1,X3) )
          & ( r1_lattice3(X0,X2,X3)
            | r1_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r1_lattice3(X0,X2,sK5(X0,X1,X2))
          | ~ r1_lattice3(X0,X1,sK5(X0,X1,X2)) )
        & ( r1_lattice3(X0,X2,sK5(X0,X1,X2))
          | r1_lattice3(X0,X1,sK5(X0,X1,X2)) )
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r2_yellow_0(X0,X2)
          | ~ r2_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r1_lattice3(X0,X2,X3)
                | ~ r1_lattice3(X0,X1,X3) )
              & ( r1_lattice3(X0,X2,X3)
                | r1_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f479,plain,(
    r1_lattice3(sK2,sK3,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f478,f434])).

fof(f478,plain,
    ( r1_lattice3(sK2,sK3,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    inference(duplicate_literal_removal,[],[f477])).

fof(f477,plain,
    ( r1_lattice3(sK2,sK3,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | r1_lattice3(sK2,sK3,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    inference(resolution,[],[f460,f438])).

fof(f438,plain,(
    ! [X0] :
      ( r1_lattice3(sK2,X0,sK5(sK2,sK3,X0))
      | r1_lattice3(sK2,sK3,sK5(sK2,sK3,X0))
      | r2_yellow_0(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f437,f35])).

fof(f437,plain,(
    ! [X0] :
      ( r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X0,sK5(sK2,sK3,X0))
      | r1_lattice3(sK2,sK3,sK5(sK2,sK3,X0))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f435,f36])).

fof(f435,plain,(
    ! [X0] :
      ( r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X0,sK5(sK2,sK3,X0))
      | r1_lattice3(sK2,sK3,sK5(sK2,sK3,X0))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f430,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | r1_lattice3(X0,X2,sK5(X0,X1,X2))
      | r1_lattice3(X0,X1,sK5(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f460,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
      | r1_lattice3(sK2,X0,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ) ),
    inference(subsumption_resolution,[],[f459,f35])).

fof(f459,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
      | r1_lattice3(sK2,X0,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f455,f36])).

fof(f455,plain,(
    ! [X0] :
      ( ~ r1_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
      | r1_lattice3(sK2,X0,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f441,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | r1_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r1_lattice3(X0,X1,X2)
              | ~ r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r1_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
              | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( ( r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r1_lattice3(X0,X1,X2) )
            & ( r1_lattice3(X0,X1,X2)
             => r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) )
            & ( r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
             => r2_lattice3(X0,X1,X2) )
            & ( r2_lattice3(X0,X1,X2)
             => r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_yellow_0)).

fof(f441,plain,(
    m1_subset_1(sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))),u1_struct_0(sK2)) ),
    inference(unit_resulting_resolution,[],[f35,f36,f430,f434,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_yellow_0(X0,X1)
      | r2_yellow_0(X0,X2)
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f434,plain,(
    ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f337,f430])).

fof(f337,plain,
    ( ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_yellow_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f265,f322])).

fof(f322,plain,(
    ~ sP0(sK2,sK3) ),
    inference(unit_resulting_resolution,[],[f320,f34])).

% (25828)lrs+1011_2:1_add=large:afr=on:afp=4000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:gs=on:irw=on:nm=64:nwc=1:sas=z3:stl=30:sos=on:sp=reverse_arity:thf=on:urr=on:updr=off_81 on theBenchmark
fof(f34,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
        & r1_yellow_0(X0,X1) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
        & r1_yellow_0(X0,X1) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f320,plain,(
    r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    inference(global_subsumption,[],[f312,f316])).

fof(f316,plain,
    ( r2_lattice3(sK2,sK3,sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    inference(factoring,[],[f283])).

fof(f283,plain,(
    ! [X0] :
      ( r2_lattice3(sK2,X0,sK4(sK2,sK3,k3_xboole_0(X0,u1_struct_0(sK2))))
      | r2_lattice3(sK2,sK3,sK4(sK2,sK3,k3_xboole_0(X0,u1_struct_0(sK2))))
      | r1_yellow_0(sK2,k3_xboole_0(X0,u1_struct_0(sK2))) ) ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,(
    ! [X0] :
      ( r1_yellow_0(sK2,k3_xboole_0(X0,u1_struct_0(sK2)))
      | r2_lattice3(sK2,X0,sK4(sK2,sK3,k3_xboole_0(X0,u1_struct_0(sK2))))
      | r2_lattice3(sK2,sK3,sK4(sK2,sK3,k3_xboole_0(X0,u1_struct_0(sK2))))
      | r1_yellow_0(sK2,k3_xboole_0(X0,u1_struct_0(sK2))) ) ),
    inference(resolution,[],[f275,f260])).

fof(f260,plain,(
    ! [X0] :
      ( r2_lattice3(sK2,X0,sK4(sK2,sK3,X0))
      | r2_lattice3(sK2,sK3,sK4(sK2,sK3,X0))
      | r1_yellow_0(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f259,f35])).

fof(f259,plain,(
    ! [X0] :
      ( r1_yellow_0(sK2,X0)
      | r2_lattice3(sK2,X0,sK4(sK2,sK3,X0))
      | r2_lattice3(sK2,sK3,sK4(sK2,sK3,X0))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f257,f36])).

fof(f257,plain,(
    ! [X0] :
      ( r1_yellow_0(sK2,X0)
      | r2_lattice3(sK2,X0,sK4(sK2,sK3,X0))
      | r2_lattice3(sK2,sK3,sK4(sK2,sK3,X0))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f251,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | r2_lattice3(X0,X2,sK4(X0,X1,X2))
      | r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ( ( ~ r2_lattice3(X0,X2,sK4(X0,X1,X2))
              | ~ r2_lattice3(X0,X1,sK4(X0,X1,X2)) )
            & ( r2_lattice3(X0,X2,sK4(X0,X1,X2))
              | r2_lattice3(X0,X1,sK4(X0,X1,X2)) )
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f24,f25])).

fof(f25,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_lattice3(X0,X2,X3)
            | ~ r2_lattice3(X0,X1,X3) )
          & ( r2_lattice3(X0,X2,X3)
            | r2_lattice3(X0,X1,X3) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ( ~ r2_lattice3(X0,X2,sK4(X0,X1,X2))
          | ~ r2_lattice3(X0,X1,sK4(X0,X1,X2)) )
        & ( r2_lattice3(X0,X2,sK4(X0,X1,X2))
          | r2_lattice3(X0,X1,sK4(X0,X1,X2)) )
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( ~ r2_lattice3(X0,X2,X3)
                | ~ r2_lattice3(X0,X1,X3) )
              & ( r2_lattice3(X0,X2,X3)
                | r2_lattice3(X0,X1,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r1_yellow_0(X0,X2)
          | ~ r1_yellow_0(X0,X1)
          | ? [X3] :
              ( ( r2_lattice3(X0,X1,X3)
              <~> r2_lattice3(X0,X2,X3) )
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ( r1_yellow_0(X0,X1)
            & ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_lattice3(X0,X1,X3)
                <=> r2_lattice3(X0,X2,X3) ) ) )
         => r1_yellow_0(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_yellow_0)).

fof(f251,plain,(
    r1_yellow_0(sK2,sK3) ),
    inference(global_subsumption,[],[f235,f238])).

fof(f238,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    inference(subsumption_resolution,[],[f237,f190])).

fof(f190,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,sK3) ),
    inference(global_subsumption,[],[f189])).

fof(f189,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,sK3) ),
    inference(global_subsumption,[],[f186])).

fof(f186,plain,
    ( r1_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    inference(global_subsumption,[],[f183])).

fof(f183,plain,
    ( r1_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f182,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | r1_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f182,plain,
    ( r1_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f181,f104])).

fof(f104,plain,
    ( r2_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,sK3) ),
    inference(global_subsumption,[],[f100,f103])).

fof(f103,plain,
    ( r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    inference(subsumption_resolution,[],[f102,f54])).

fof(f54,plain,
    ( r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r2_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,sK3) ),
    inference(resolution,[],[f52,f33])).

fof(f52,plain,
    ( sP0(sK2,sK3)
    | r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    inference(resolution,[],[f31,f37])).

fof(f37,plain,
    ( sP1(sK3,sK2)
    | r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | sP0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ( ~ r2_yellow_0(sK2,sK3)
        & r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) )
      | ( ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
        & r2_yellow_0(sK2,sK3) )
      | sP1(sK3,sK2)
      | sP0(sK2,sK3) )
    & l1_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f16,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ r2_yellow_0(X0,X1)
              & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
            | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
              & r2_yellow_0(X0,X1) )
            | sP1(X1,X0)
            | sP0(X0,X1) )
        & l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ r2_yellow_0(sK2,X1)
            & r2_yellow_0(sK2,k3_xboole_0(X1,u1_struct_0(sK2))) )
          | ( ~ r2_yellow_0(sK2,k3_xboole_0(X1,u1_struct_0(sK2)))
            & r2_yellow_0(sK2,X1) )
          | sP1(X1,sK2)
          | sP0(sK2,X1) )
      & l1_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ( ~ r2_yellow_0(sK2,X1)
          & r2_yellow_0(sK2,k3_xboole_0(X1,u1_struct_0(sK2))) )
        | ( ~ r2_yellow_0(sK2,k3_xboole_0(X1,u1_struct_0(sK2)))
          & r2_yellow_0(sK2,X1) )
        | sP1(X1,sK2)
        | sP0(sK2,X1) )
   => ( ( ~ r2_yellow_0(sK2,sK3)
        & r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) )
      | ( ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
        & r2_yellow_0(sK2,sK3) )
      | sP1(sK3,sK2)
      | sP0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,X1)
            & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r2_yellow_0(X0,X1) )
          | sP1(X1,X0)
          | sP0(X0,X1) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f7,f15,f14])).

fof(f15,plain,(
    ! [X1,X0] :
      ( ( ~ r1_yellow_0(X0,X1)
        & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
      | ~ sP1(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,X1)
            & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r2_yellow_0(X0,X1) )
          | ( ~ r1_yellow_0(X0,X1)
            & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ r2_yellow_0(X0,X1)
            & r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r2_yellow_0(X0,X1) )
          | ( ~ r1_yellow_0(X0,X1)
            & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          | ( ~ r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
            & r1_yellow_0(X0,X1) ) )
      & l1_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
             => r2_yellow_0(X0,X1) )
            & ( r2_yellow_0(X0,X1)
             => r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
            & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
             => r1_yellow_0(X0,X1) )
            & ( r1_yellow_0(X0,X1)
             => r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r2_yellow_0(X0,X1) )
          & ( r2_yellow_0(X0,X1)
           => r2_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
          & ( r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0)))
           => r1_yellow_0(X0,X1) )
          & ( r1_yellow_0(X0,X1)
           => r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_yellow_0)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | r1_yellow_0(X1,k3_xboole_0(X0,u1_struct_0(X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_yellow_0(X1,X0)
        & r1_yellow_0(X1,k3_xboole_0(X0,u1_struct_0(X1))) )
      | ~ sP1(X0,X1) ) ),
    inference(rectify,[],[f17])).

fof(f17,plain,(
    ! [X1,X0] :
      ( ( ~ r1_yellow_0(X0,X1)
        & r1_yellow_0(X0,k3_xboole_0(X1,u1_struct_0(X0))) )
      | ~ sP1(X1,X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f102,plain,
    ( r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    inference(subsumption_resolution,[],[f101,f35])).

fof(f101,plain,
    ( r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f99,f36])).

fof(f99,plain,
    ( r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f98])).

fof(f98,plain,
    ( r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f92,f50])).

fof(f92,plain,
    ( r1_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,
    ( r1_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    inference(factoring,[],[f85])).

fof(f85,plain,(
    ! [X0] :
      ( r1_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ) ),
    inference(duplicate_literal_removal,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( r1_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,sK3)
      | r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3) ) ),
    inference(resolution,[],[f70,f73])).

fof(f73,plain,(
    ! [X0] :
      ( r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f72,f35])).

fof(f72,plain,(
    ! [X0] :
      ( r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | v2_struct_0(sK2)
      | r2_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f71,f36])).

fof(f71,plain,(
    ! [X0] :
      ( r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2)
      | r2_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3) ) ),
    inference(resolution,[],[f49,f54])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
      | r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X1)
      | r2_yellow_0(sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f69,f35])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
      | r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
      | v2_struct_0(sK2)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X1)
      | r2_yellow_0(sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f68,f36])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
      | r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X1)
      | r2_yellow_0(sK2,sK3) ) ),
    inference(resolution,[],[f44,f58])).

% (25824)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
fof(f58,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0),u1_struct_0(sK2))
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f57,f35])).

fof(f57,plain,(
    ! [X0] :
      ( r2_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0)
      | m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0),u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f56,f36])).

fof(f56,plain,(
    ! [X0] :
      ( r2_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0)
      | m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0),u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f54,f48])).

fof(f100,plain,
    ( r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,
    ( r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3) ),
    inference(resolution,[],[f92,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
      | r1_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X1)
      | r2_yellow_0(sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f66,f35])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
      | r1_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
      | v2_struct_0(sK2)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X1)
      | r2_yellow_0(sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f65,f36])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
      | r1_lattice3(sK2,k3_xboole_0(X0,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X1)
      | r2_yellow_0(sK2,sK3) ) ),
    inference(resolution,[],[f43,f58])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_lattice3(X0,X1,X2)
      | r1_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f181,plain,
    ( r1_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_yellow_0(sK2,sK3)
    | sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f178,f31])).

fof(f178,plain,
    ( r1_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_yellow_0(sK2,sK3)
    | sP1(sK3,sK2)
    | sP0(sK2,sK3) ),
    inference(resolution,[],[f167,f40])).

fof(f40,plain,
    ( ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_yellow_0(sK2,sK3)
    | sP1(sK3,sK2)
    | sP0(sK2,sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f167,plain,
    ( r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    inference(subsumption_resolution,[],[f153,f150])).

fof(f150,plain,
    ( r1_lattice3(sK2,sK3,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,
    ( r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,sK3)
    | r1_lattice3(sK2,sK3,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    inference(resolution,[],[f139,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,k3_xboole_0(X1,u1_struct_0(sK2)),sK5(sK2,sK3,X0))
      | r2_yellow_0(sK2,X0)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r1_lattice3(sK2,X1,sK5(sK2,sK3,X0)) ) ),
    inference(subsumption_resolution,[],[f115,f35])).

fof(f115,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | ~ r1_lattice3(sK2,k3_xboole_0(X1,u1_struct_0(sK2)),sK5(sK2,sK3,X0))
      | r1_lattice3(sK2,X1,sK5(sK2,sK3,X0))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f111,f36])).

fof(f111,plain,(
    ! [X0,X1] :
      ( r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | ~ r1_lattice3(sK2,k3_xboole_0(X1,u1_struct_0(sK2)),sK5(sK2,sK3,X0))
      | r1_lattice3(sK2,X1,sK5(sK2,sK3,X0))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f110,f44])).

fof(f110,plain,(
    ! [X1] :
      ( m1_subset_1(sK5(sK2,sK3,X1),u1_struct_0(sK2))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X1)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ) ),
    inference(subsumption_resolution,[],[f109,f35])).

fof(f109,plain,(
    ! [X1] :
      ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X1)
      | m1_subset_1(sK5(sK2,sK3,X1),u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f106,f36])).

fof(f106,plain,(
    ! [X1] :
      ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X1)
      | m1_subset_1(sK5(sK2,sK3,X1),u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f104,f48])).

fof(f139,plain,
    ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    inference(factoring,[],[f131])).

fof(f131,plain,(
    ! [X1] :
      ( r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,X1))
      | r1_lattice3(sK2,X1,sK5(sK2,sK3,X1))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X1)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X1] :
      ( r2_yellow_0(sK2,X1)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,X1))
      | r1_lattice3(sK2,X1,sK5(sK2,sK3,X1))
      | r2_yellow_0(sK2,X1)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3) ) ),
    inference(resolution,[],[f118,f108])).

fof(f108,plain,(
    ! [X0] :
      ( r1_lattice3(sK2,X0,sK5(sK2,sK3,X0))
      | r1_lattice3(sK2,sK3,sK5(sK2,sK3,X0))
      | r2_yellow_0(sK2,X0)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f107,f35])).

fof(f107,plain,(
    ! [X0] :
      ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X0,sK5(sK2,sK3,X0))
      | r1_lattice3(sK2,sK3,sK5(sK2,sK3,X0))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f105,f36])).

fof(f105,plain,(
    ! [X0] :
      ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X0,sK5(sK2,sK3,X0))
      | r1_lattice3(sK2,sK3,sK5(sK2,sK3,X0))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f104,f49])).

fof(f118,plain,(
    ! [X2,X3] :
      ( ~ r1_lattice3(sK2,X3,sK5(sK2,sK3,X2))
      | r2_yellow_0(sK2,X2)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | r1_yellow_0(sK2,sK3)
      | r1_lattice3(sK2,k3_xboole_0(X3,u1_struct_0(sK2)),sK5(sK2,sK3,X2)) ) ),
    inference(subsumption_resolution,[],[f117,f35])).

fof(f117,plain,(
    ! [X2,X3] :
      ( r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X2)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | ~ r1_lattice3(sK2,X3,sK5(sK2,sK3,X2))
      | r1_lattice3(sK2,k3_xboole_0(X3,u1_struct_0(sK2)),sK5(sK2,sK3,X2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f112,f36])).

fof(f112,plain,(
    ! [X2,X3] :
      ( r1_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X2)
      | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
      | ~ r1_lattice3(sK2,X3,sK5(sK2,sK3,X2))
      | r1_lattice3(sK2,k3_xboole_0(X3,u1_struct_0(sK2)),sK5(sK2,sK3,X2))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f110,f43])).

fof(f153,plain,
    ( r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f152,f104])).

fof(f152,plain,
    ( r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f151,f35])).

fof(f151,plain,
    ( r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f148,f36])).

fof(f148,plain,
    ( r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f147])).

fof(f147,plain,
    ( r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r1_lattice3(sK2,sK3,sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f139,f50])).

fof(f237,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    inference(subsumption_resolution,[],[f236,f35])).

fof(f236,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f234,f36])).

fof(f234,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,
    ( r1_yellow_0(sK2,sK3)
    | ~ r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r1_yellow_0(sK2,sK3)
    | ~ r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f221,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_lattice3(X0,X2,sK4(X0,X1,X2))
      | ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | ~ r2_lattice3(X0,X1,sK4(X0,X1,X2))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f221,plain,
    ( r2_lattice3(sK2,sK3,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | r1_yellow_0(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f220])).

fof(f220,plain,
    ( r2_lattice3(sK2,sK3,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | r1_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,sK3) ),
    inference(factoring,[],[f216])).

fof(f216,plain,(
    ! [X0] :
      ( r2_lattice3(sK2,sK3,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r2_lattice3(sK2,X0,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,(
    ! [X0] :
      ( r1_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,X0)
      | r2_lattice3(sK2,sK3,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r2_lattice3(sK2,X0,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,X0) ) ),
    inference(resolution,[],[f206,f194])).

fof(f194,plain,(
    ! [X0] :
      ( r2_lattice3(sK2,X0,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f193,f35])).

fof(f193,plain,(
    ! [X0] :
      ( r1_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,X0)
      | r2_lattice3(sK2,X0,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f191,f36])).

fof(f191,plain,(
    ! [X0] :
      ( r1_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,X0)
      | r2_lattice3(sK2,X0,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f190,f46])).

fof(f206,plain,(
    ! [X4,X5] :
      ( ~ r2_lattice3(sK2,k3_xboole_0(X5,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X4))
      | r1_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,X4)
      | r2_lattice3(sK2,X5,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X4)) ) ),
    inference(subsumption_resolution,[],[f205,f35])).

fof(f205,plain,(
    ! [X4,X5] :
      ( r1_yellow_0(sK2,X4)
      | r1_yellow_0(sK2,sK3)
      | ~ r2_lattice3(sK2,k3_xboole_0(X5,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X4))
      | r2_lattice3(sK2,X5,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X4))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f199,f36])).

fof(f199,plain,(
    ! [X4,X5] :
      ( r1_yellow_0(sK2,X4)
      | r1_yellow_0(sK2,sK3)
      | ~ r2_lattice3(sK2,k3_xboole_0(X5,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X4))
      | r2_lattice3(sK2,X5,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X4))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f196,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f196,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2))
      | r1_yellow_0(sK2,X1)
      | r1_yellow_0(sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f195,f35])).

fof(f195,plain,(
    ! [X1] :
      ( r1_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,X1)
      | m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f192,f36])).

fof(f192,plain,(
    ! [X1] :
      ( r1_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,X1)
      | m1_subset_1(sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f190,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_yellow_0(X0,X1)
      | r1_yellow_0(X0,X2)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f235,plain,
    ( r1_yellow_0(sK2,sK3)
    | r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,
    ( r1_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,sK3)
    | r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    inference(resolution,[],[f221,f208])).

fof(f208,plain,(
    ! [X6,X7] :
      ( ~ r2_lattice3(sK2,X7,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X6))
      | r1_yellow_0(sK2,sK3)
      | r1_yellow_0(sK2,X6)
      | r2_lattice3(sK2,k3_xboole_0(X7,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X6)) ) ),
    inference(subsumption_resolution,[],[f207,f35])).

fof(f207,plain,(
    ! [X6,X7] :
      ( r1_yellow_0(sK2,X6)
      | r1_yellow_0(sK2,sK3)
      | ~ r2_lattice3(sK2,X7,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X6))
      | r2_lattice3(sK2,k3_xboole_0(X7,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X6))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f200,f36])).

fof(f200,plain,(
    ! [X6,X7] :
      ( r1_yellow_0(sK2,X6)
      | r1_yellow_0(sK2,sK3)
      | ~ r2_lattice3(sK2,X7,sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X6))
      | r2_lattice3(sK2,k3_xboole_0(X7,u1_struct_0(sK2)),sK4(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X6))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f196,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | r2_lattice3(X0,k3_xboole_0(X1,u1_struct_0(X0)),X2)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f275,plain,(
    ! [X4,X5] :
      ( ~ r2_lattice3(sK2,k3_xboole_0(X5,u1_struct_0(sK2)),sK4(sK2,sK3,X4))
      | r1_yellow_0(sK2,X4)
      | r2_lattice3(sK2,X5,sK4(sK2,sK3,X4)) ) ),
    inference(subsumption_resolution,[],[f274,f35])).

fof(f274,plain,(
    ! [X4,X5] :
      ( r1_yellow_0(sK2,X4)
      | ~ r2_lattice3(sK2,k3_xboole_0(X5,u1_struct_0(sK2)),sK4(sK2,sK3,X4))
      | r2_lattice3(sK2,X5,sK4(sK2,sK3,X4))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f268,f36])).

fof(f268,plain,(
    ! [X4,X5] :
      ( r1_yellow_0(sK2,X4)
      | ~ r2_lattice3(sK2,k3_xboole_0(X5,u1_struct_0(sK2)),sK4(sK2,sK3,X4))
      | r2_lattice3(sK2,X5,sK4(sK2,sK3,X4))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f262,f42])).

fof(f262,plain,(
    ! [X1] :
      ( m1_subset_1(sK4(sK2,sK3,X1),u1_struct_0(sK2))
      | r1_yellow_0(sK2,X1) ) ),
    inference(subsumption_resolution,[],[f261,f35])).

fof(f261,plain,(
    ! [X1] :
      ( r1_yellow_0(sK2,X1)
      | m1_subset_1(sK4(sK2,sK3,X1),u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f258,f36])).

fof(f258,plain,(
    ! [X1] :
      ( r1_yellow_0(sK2,X1)
      | m1_subset_1(sK4(sK2,sK3,X1),u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f251,f45])).

fof(f312,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_lattice3(sK2,sK3,sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    inference(subsumption_resolution,[],[f311,f35])).

fof(f311,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_lattice3(sK2,sK3,sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f310,f36])).

fof(f310,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_lattice3(sK2,sK3,sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f307,f251])).

fof(f307,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r1_yellow_0(sK2,sK3)
    | ~ r2_lattice3(sK2,sK3,sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,
    ( r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r1_yellow_0(sK2,sK3)
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_lattice3(sK2,sK3,sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f294,f47])).

fof(f294,plain,
    ( r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2))))
    | r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    inference(factoring,[],[f286])).

fof(f286,plain,(
    ! [X1] :
      ( r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,X1))
      | r2_lattice3(sK2,X1,sK4(sK2,sK3,X1))
      | r1_yellow_0(sK2,X1) ) ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,(
    ! [X1] :
      ( r1_yellow_0(sK2,X1)
      | r2_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK4(sK2,sK3,X1))
      | r2_lattice3(sK2,X1,sK4(sK2,sK3,X1))
      | r1_yellow_0(sK2,X1) ) ),
    inference(resolution,[],[f277,f260])).

fof(f277,plain,(
    ! [X6,X7] :
      ( ~ r2_lattice3(sK2,X7,sK4(sK2,sK3,X6))
      | r1_yellow_0(sK2,X6)
      | r2_lattice3(sK2,k3_xboole_0(X7,u1_struct_0(sK2)),sK4(sK2,sK3,X6)) ) ),
    inference(subsumption_resolution,[],[f276,f35])).

fof(f276,plain,(
    ! [X6,X7] :
      ( r1_yellow_0(sK2,X6)
      | ~ r2_lattice3(sK2,X7,sK4(sK2,sK3,X6))
      | r2_lattice3(sK2,k3_xboole_0(X7,u1_struct_0(sK2)),sK4(sK2,sK3,X6))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f269,f36])).

fof(f269,plain,(
    ! [X6,X7] :
      ( r1_yellow_0(sK2,X6)
      | ~ r2_lattice3(sK2,X7,sK4(sK2,sK3,X6))
      | r2_lattice3(sK2,k3_xboole_0(X7,u1_struct_0(sK2)),sK4(sK2,sK3,X6))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f262,f41])).

fof(f265,plain,
    ( ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r2_yellow_0(sK2,sK3)
    | sP0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f40,f256])).

fof(f256,plain,(
    ~ sP1(sK3,sK2) ),
    inference(unit_resulting_resolution,[],[f251,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ sP1(X0,X1)
      | ~ r1_yellow_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f430,plain,(
    r2_yellow_0(sK2,sK3) ),
    inference(global_subsumption,[],[f321,f414,f417])).

fof(f417,plain,
    ( ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    inference(subsumption_resolution,[],[f416,f337])).

fof(f416,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    inference(subsumption_resolution,[],[f415,f35])).

fof(f415,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | v2_struct_0(sK2) ),
    inference(subsumption_resolution,[],[f413,f36])).

fof(f413,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(duplicate_literal_removal,[],[f412])).

fof(f412,plain,
    ( r2_yellow_0(sK2,sK3)
    | ~ r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r2_yellow_0(sK2,sK3)
    | ~ r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | ~ l1_orders_2(sK2)
    | v2_struct_0(sK2) ),
    inference(resolution,[],[f406,f50])).

fof(f406,plain,
    ( r1_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | r2_yellow_0(sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f405])).

fof(f405,plain,
    ( r1_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3))
    | r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3) ),
    inference(factoring,[],[f370])).

fof(f370,plain,(
    ! [X0] :
      ( r1_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r2_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f367])).

fof(f367,plain,(
    ! [X0] :
      ( r2_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,sK3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r2_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0) ) ),
    inference(resolution,[],[f344,f334])).

fof(f334,plain,(
    ! [X0] :
      ( r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r2_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0) ) ),
    inference(subsumption_resolution,[],[f333,f35])).

fof(f333,plain,(
    ! [X0] :
      ( r2_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f331,f36])).

fof(f331,plain,(
    ! [X0] :
      ( r2_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X0,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f321,f49])).

fof(f344,plain,(
    ! [X0,X1] :
      ( ~ r1_lattice3(sK2,k3_xboole_0(X1,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r2_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X0)
      | r1_lattice3(sK2,X1,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0)) ) ),
    inference(subsumption_resolution,[],[f343,f35])).

fof(f343,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,sK3)
      | ~ r1_lattice3(sK2,k3_xboole_0(X1,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_lattice3(sK2,X1,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f339,f36])).

fof(f339,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(sK2,X0)
      | r2_yellow_0(sK2,sK3)
      | ~ r1_lattice3(sK2,k3_xboole_0(X1,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | r1_lattice3(sK2,X1,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X0))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f336,f44])).

fof(f336,plain,(
    ! [X1] :
      ( m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2))
      | r2_yellow_0(sK2,X1)
      | r2_yellow_0(sK2,sK3) ) ),
    inference(subsumption_resolution,[],[f335,f35])).

fof(f335,plain,(
    ! [X1] :
      ( r2_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X1)
      | m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f332,f36])).

fof(f332,plain,(
    ! [X1] :
      ( r2_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X1)
      | m1_subset_1(sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X1),u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f321,f48])).

fof(f414,plain,
    ( r2_yellow_0(sK2,sK3)
    | r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    inference(duplicate_literal_removal,[],[f411])).

fof(f411,plain,
    ( r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,sK3)
    | r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK3)) ),
    inference(resolution,[],[f406,f346])).

fof(f346,plain,(
    ! [X2,X3] :
      ( ~ r1_lattice3(sK2,X3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X2))
      | r2_yellow_0(sK2,sK3)
      | r2_yellow_0(sK2,X2)
      | r1_lattice3(sK2,k3_xboole_0(X3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X2)) ) ),
    inference(subsumption_resolution,[],[f345,f35])).

fof(f345,plain,(
    ! [X2,X3] :
      ( r2_yellow_0(sK2,X2)
      | r2_yellow_0(sK2,sK3)
      | ~ r1_lattice3(sK2,X3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X2))
      | r1_lattice3(sK2,k3_xboole_0(X3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X2))
      | v2_struct_0(sK2) ) ),
    inference(subsumption_resolution,[],[f340,f36])).

fof(f340,plain,(
    ! [X2,X3] :
      ( r2_yellow_0(sK2,X2)
      | r2_yellow_0(sK2,sK3)
      | ~ r1_lattice3(sK2,X3,sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X2))
      | r1_lattice3(sK2,k3_xboole_0(X3,u1_struct_0(sK2)),sK5(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),X2))
      | ~ l1_orders_2(sK2)
      | v2_struct_0(sK2) ) ),
    inference(resolution,[],[f336,f43])).

fof(f321,plain,
    ( r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r2_yellow_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f263,f320])).

fof(f263,plain,
    ( ~ r1_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r2_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2))) ),
    inference(resolution,[],[f255,f34])).

fof(f255,plain,
    ( sP0(sK2,sK3)
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | r2_yellow_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f51,f251])).

fof(f51,plain,
    ( ~ r1_yellow_0(sK2,sK3)
    | r2_yellow_0(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)))
    | sP0(sK2,sK3)
    | r2_yellow_0(sK2,sK3) ),
    inference(resolution,[],[f37,f32])).

fof(f36,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f35,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f482,plain,(
    r1_lattice3(sK2,k3_xboole_0(sK3,u1_struct_0(sK2)),sK5(sK2,sK3,k3_xboole_0(sK3,u1_struct_0(sK2)))) ),
    inference(unit_resulting_resolution,[],[f35,f36,f441,f479,f43])).

%------------------------------------------------------------------------------
