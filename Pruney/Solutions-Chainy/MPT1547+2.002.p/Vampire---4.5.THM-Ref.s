%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:16:01 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 876 expanded)
%              Number of leaves         :   11 ( 270 expanded)
%              Depth                    :   51
%              Number of atoms          :  718 (7788 expanded)
%              Number of equality atoms :   66 (1435 expanded)
%              Maximal formula depth    :   22 (   8 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f250,plain,(
    $false ),
    inference(subsumption_resolution,[],[f249,f69])).

fof(f69,plain,(
    ~ v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f68,f38])).

fof(f38,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ r3_orders_2(sK0,sK1,sK2)
      | sK1 != k12_lattice3(sK0,sK1,sK2) )
    & ( r3_orders_2(sK0,sK1,sK2)
      | sK1 = k12_lattice3(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v2_lattice3(sK0)
    & v5_orders_2(sK0)
    & v3_orders_2(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).

fof(f25,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r3_orders_2(X0,X1,X2)
                  | k12_lattice3(X0,X1,X2) != X1 )
                & ( r3_orders_2(X0,X1,X2)
                  | k12_lattice3(X0,X1,X2) = X1 )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_orders_2(sK0,X1,X2)
                | k12_lattice3(sK0,X1,X2) != X1 )
              & ( r3_orders_2(sK0,X1,X2)
                | k12_lattice3(sK0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v2_lattice3(sK0)
      & v5_orders_2(sK0)
      & v3_orders_2(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r3_orders_2(sK0,X1,X2)
              | k12_lattice3(sK0,X1,X2) != X1 )
            & ( r3_orders_2(sK0,X1,X2)
              | k12_lattice3(sK0,X1,X2) = X1 )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ( ~ r3_orders_2(sK0,sK1,X2)
            | sK1 != k12_lattice3(sK0,sK1,X2) )
          & ( r3_orders_2(sK0,sK1,X2)
            | sK1 = k12_lattice3(sK0,sK1,X2) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X2] :
        ( ( ~ r3_orders_2(sK0,sK1,X2)
          | sK1 != k12_lattice3(sK0,sK1,X2) )
        & ( r3_orders_2(sK0,sK1,X2)
          | sK1 = k12_lattice3(sK0,sK1,X2) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ( ~ r3_orders_2(sK0,sK1,sK2)
        | sK1 != k12_lattice3(sK0,sK1,sK2) )
      & ( r3_orders_2(sK0,sK1,sK2)
        | sK1 = k12_lattice3(sK0,sK1,sK2) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_orders_2(X0,X1,X2)
                | k12_lattice3(X0,X1,X2) != X1 )
              & ( r3_orders_2(X0,X1,X2)
                | k12_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r3_orders_2(X0,X1,X2)
                | k12_lattice3(X0,X1,X2) != X1 )
              & ( r3_orders_2(X0,X1,X2)
                | k12_lattice3(X0,X1,X2) = X1 )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <~> r3_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k12_lattice3(X0,X1,X2) = X1
              <~> r3_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v2_lattice3(X0)
      & v5_orders_2(X0)
      & v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v2_lattice3(X0)
          & v5_orders_2(X0)
          & v3_orders_2(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k12_lattice3(X0,X1,X2) = X1
                <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k12_lattice3(X0,X1,X2) = X1
              <=> r3_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).

fof(f68,plain,
    ( ~ v2_struct_0(sK0)
    | ~ l1_orders_2(sK0) ),
    inference(resolution,[],[f43,f37])).

fof(f37,plain,(
    v2_lattice3(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v2_lattice3(X0)
      | ~ v2_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ~ v2_struct_0(X0)
      | ~ v2_lattice3(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ( v2_lattice3(X0)
       => ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).

fof(f249,plain,(
    v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f248,f35])).

fof(f35,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f248,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f247,f38])).

fof(f247,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f246,f39])).

fof(f39,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f246,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f245,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r3_orders_2(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(condensation,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f245,plain,(
    ~ r3_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f244,f69])).

fof(f244,plain,
    ( ~ r3_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f243,f35])).

fof(f243,plain,
    ( ~ r3_orders_2(sK0,sK1,sK1)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f242,f38])).

fof(f242,plain,
    ( ~ r3_orders_2(sK0,sK1,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f241,f39])).

fof(f241,plain,
    ( ~ r3_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,
    ( ~ r3_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f232,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,X1,X2)
      | ~ r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f232,plain,(
    ~ r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f231,f69])).

fof(f231,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f230,f35])).

fof(f230,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f229,f38])).

fof(f229,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f228,f39])).

fof(f228,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f227,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f227,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f226,f120])).

fof(f120,plain,(
    r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f119,f69])).

fof(f119,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f118,f35])).

fof(f118,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f117,f38])).

fof(f117,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f116,f39])).

fof(f116,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f115,f40])).

fof(f115,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,
    ( r3_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f99,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f99,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f98,f36])).

fof(f36,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f98,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f97,f37])).

fof(f97,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f96,f38])).

fof(f96,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f95,f40])).

fof(f95,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f90,f39])).

fof(f90,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(duplicate_literal_removal,[],[f89])).

fof(f89,plain,
    ( r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(superposition,[],[f65,f79])).

fof(f79,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f78,f36])).

fof(f78,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f77,f37])).

fof(f77,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK2)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f76,f38])).

fof(f76,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f75,f39])).

fof(f75,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f72,f40])).

fof(f72,plain,
    ( sK1 = k11_lattice3(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(superposition,[],[f55,f41])).

fof(f41,plain,
    ( sK1 = k12_lattice3(sK0,sK1,sK2)
    | r3_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f57,f43])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2)
      | ~ m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,X3,X2)
      | k11_lattice3(X0,X1,X2) != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
                      | ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
                        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
                        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) )
                      | ~ r1_orders_2(X0,X3,X2)
                      | ~ r1_orders_2(X0,X3,X1) )
                    & ( ( ! [X5] :
                            ( r1_orders_2(X0,X5,X3)
                            | ~ r1_orders_2(X0,X5,X2)
                            | ~ r1_orders_2(X0,X5,X1)
                            | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                        & r1_orders_2(X0,X3,X2)
                        & r1_orders_2(X0,X3,X1) )
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r1_orders_2(X0,X4,X3)
          & r1_orders_2(X0,X4,X2)
          & r1_orders_2(X0,X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
        & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1)
        & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
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
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
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
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k11_lattice3(X0,X1,X2) = X3
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
                      | k11_lattice3(X0,X1,X2) != X3 ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k11_lattice3(X0,X1,X2) = X3
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
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( k11_lattice3(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X0))
                         => ( ( r1_orders_2(X0,X4,X2)
                              & r1_orders_2(X0,X4,X1) )
                           => r1_orders_2(X0,X4,X3) ) )
                      & r1_orders_2(X0,X3,X2)
                      & r1_orders_2(X0,X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).

fof(f226,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r3_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f224,f53])).

fof(f224,plain,
    ( ~ r1_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f223,f36])).

fof(f223,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f222,f37])).

fof(f222,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f221,f38])).

fof(f221,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f220,f40])).

fof(f220,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f219,f39])).

fof(f219,plain,
    ( ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f206,f120])).

fof(f206,plain,
    ( ~ r3_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(trivial_inequality_removal,[],[f205])).

fof(f205,plain,
    ( sK1 != sK1
    | ~ r3_orders_2(sK0,sK1,sK2)
    | ~ r1_orders_2(sK0,sK1,sK1)
    | ~ r1_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(superposition,[],[f84,f165])).

fof(f165,plain,(
    ! [X4,X5,X3] :
      ( k11_lattice3(X3,X5,X4) = X5
      | ~ r1_orders_2(X3,X5,X5)
      | ~ r1_orders_2(X3,X5,X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X4,X5,X3] :
      ( k11_lattice3(X3,X5,X4) = X5
      | ~ r1_orders_2(X3,X5,X5)
      | ~ r1_orders_2(X3,X5,X4)
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v5_orders_2(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v2_lattice3(X3)
      | ~ v5_orders_2(X3) ) ),
    inference(superposition,[],[f142,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v2_lattice3(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = X2
      | ~ r1_orders_2(X0,X2,X2)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( k11_lattice3(X0,X1,X2) = X2
      | ~ r1_orders_2(X0,X2,X2)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | k11_lattice3(X0,X1,X2) = X2
      | ~ r1_orders_2(X0,X2,X2)
      | ~ r1_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(resolution,[],[f61,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
      | k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f50,f43])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,sK3(X0,X1,X2,X3),X3)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
      | k11_lattice3(X0,X1,X2) = X3
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(subsumption_resolution,[],[f49,f43])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( k11_lattice3(X0,X1,X2) = X3
      | r1_orders_2(X0,sK3(X0,X1,X2,X3),X2)
      | ~ r1_orders_2(X0,X3,X2)
      | ~ r1_orders_2(X0,X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v2_lattice3(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,
    ( sK1 != k11_lattice3(sK0,sK1,sK2)
    | ~ r3_orders_2(sK0,sK1,sK2) ),
    inference(subsumption_resolution,[],[f83,f36])).

fof(f83,plain,
    ( sK1 != k11_lattice3(sK0,sK1,sK2)
    | ~ r3_orders_2(sK0,sK1,sK2)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f82,f37])).

fof(f82,plain,
    ( sK1 != k11_lattice3(sK0,sK1,sK2)
    | ~ r3_orders_2(sK0,sK1,sK2)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f81,f38])).

fof(f81,plain,
    ( sK1 != k11_lattice3(sK0,sK1,sK2)
    | ~ r3_orders_2(sK0,sK1,sK2)
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f80,f39])).

fof(f80,plain,
    ( sK1 != k11_lattice3(sK0,sK1,sK2)
    | ~ r3_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(subsumption_resolution,[],[f73,f40])).

fof(f73,plain,
    ( sK1 != k11_lattice3(sK0,sK1,sK2)
    | ~ r3_orders_2(sK0,sK1,sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v2_lattice3(sK0)
    | ~ v5_orders_2(sK0) ),
    inference(superposition,[],[f42,f55])).

fof(f42,plain,
    ( sK1 != k12_lattice3(sK0,sK1,sK2)
    | ~ r3_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:27:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (5021)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.43  % (5023)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.44  % (5008)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.44  % (5007)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.45  % (5023)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f250,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(subsumption_resolution,[],[f249,f69])).
% 0.21/0.45  fof(f69,plain,(
% 0.21/0.45    ~v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f68,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    l1_orders_2(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    (((~r3_orders_2(sK0,sK1,sK2) | sK1 != k12_lattice3(sK0,sK1,sK2)) & (r3_orders_2(sK0,sK1,sK2) | sK1 = k12_lattice3(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 0.21/0.45  fof(f25,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : ((~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => (? [X1] : (? [X2] : ((~r3_orders_2(sK0,X1,X2) | k12_lattice3(sK0,X1,X2) != X1) & (r3_orders_2(sK0,X1,X2) | k12_lattice3(sK0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v2_lattice3(sK0) & v5_orders_2(sK0) & v3_orders_2(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ? [X1] : (? [X2] : ((~r3_orders_2(sK0,X1,X2) | k12_lattice3(sK0,X1,X2) != X1) & (r3_orders_2(sK0,X1,X2) | k12_lattice3(sK0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : ((~r3_orders_2(sK0,sK1,X2) | sK1 != k12_lattice3(sK0,sK1,X2)) & (r3_orders_2(sK0,sK1,X2) | sK1 = k12_lattice3(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ? [X2] : ((~r3_orders_2(sK0,sK1,X2) | sK1 != k12_lattice3(sK0,sK1,X2)) & (r3_orders_2(sK0,sK1,X2) | sK1 = k12_lattice3(sK0,sK1,X2)) & m1_subset_1(X2,u1_struct_0(sK0))) => ((~r3_orders_2(sK0,sK1,sK2) | sK1 != k12_lattice3(sK0,sK1,sK2)) & (r3_orders_2(sK0,sK1,sK2) | sK1 = k12_lattice3(sK0,sK1,sK2)) & m1_subset_1(sK2,u1_struct_0(sK0)))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f24,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : ((~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f23])).
% 0.21/0.45  fof(f23,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (((~r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) != X1) & (r3_orders_2(X0,X1,X2) | k12_lattice3(X0,X1,X2) = X1)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f10])).
% 0.21/0.45  fof(f10,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : ((k12_lattice3(X0,X1,X2) = X1 <~> r3_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f9])).
% 0.21/0.45  fof(f9,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : ((k12_lattice3(X0,X1,X2) = X1 <~> r3_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f8])).
% 0.21/0.45  fof(f8,negated_conjecture,(
% 0.21/0.45    ~! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 0.21/0.45    inference(negated_conjecture,[],[f7])).
% 0.21/0.45  fof(f7,conjecture,(
% 0.21/0.45    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k12_lattice3(X0,X1,X2) = X1 <=> r3_orders_2(X0,X1,X2)))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_yellow_0)).
% 0.21/0.45  fof(f68,plain,(
% 0.21/0.45    ~v2_struct_0(sK0) | ~l1_orders_2(sK0)),
% 0.21/0.45    inference(resolution,[],[f43,f37])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    v2_lattice3(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f43,plain,(
% 0.21/0.45    ( ! [X0] : (~v2_lattice3(X0) | ~v2_struct_0(X0) | ~l1_orders_2(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ! [X0] : (~v2_struct_0(X0) | ~v2_lattice3(X0) | ~l1_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f11])).
% 0.21/0.45  fof(f11,plain,(
% 0.21/0.45    ! [X0] : ((~v2_struct_0(X0) | ~v2_lattice3(X0)) | ~l1_orders_2(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f3])).
% 0.21/0.45  fof(f3,axiom,(
% 0.21/0.45    ! [X0] : (l1_orders_2(X0) => (v2_lattice3(X0) => ~v2_struct_0(X0)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_lattice3)).
% 0.21/0.45  fof(f249,plain,(
% 0.21/0.45    v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f248,f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    v3_orders_2(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f248,plain,(
% 0.21/0.45    ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f247,f38])).
% 0.21/0.45  fof(f247,plain,(
% 0.21/0.45    ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f246,f39])).
% 0.21/0.45  fof(f39,plain,(
% 0.21/0.45    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f246,plain,(
% 0.21/0.45    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(resolution,[],[f245,f59])).
% 0.21/0.45  fof(f59,plain,(
% 0.21/0.45    ( ! [X0,X1] : (r3_orders_2(X1,X0,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.45    inference(condensation,[],[f52])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f18])).
% 0.21/0.45  fof(f18,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f2])).
% 0.21/0.45  fof(f2,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 0.21/0.45  fof(f245,plain,(
% 0.21/0.45    ~r3_orders_2(sK0,sK1,sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f244,f69])).
% 0.21/0.45  fof(f244,plain,(
% 0.21/0.45    ~r3_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f243,f35])).
% 0.21/0.45  fof(f243,plain,(
% 0.21/0.45    ~r3_orders_2(sK0,sK1,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f242,f38])).
% 0.21/0.45  fof(f242,plain,(
% 0.21/0.45    ~r3_orders_2(sK0,sK1,sK1) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f241,f39])).
% 0.21/0.45  fof(f241,plain,(
% 0.21/0.45    ~r3_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f240])).
% 0.21/0.45  fof(f240,plain,(
% 0.21/0.45    ~r3_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(resolution,[],[f232,f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f34])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f20])).
% 0.21/0.45  fof(f20,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f19])).
% 0.21/0.45  fof(f19,plain,(
% 0.21/0.45    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f1])).
% 0.21/0.45  fof(f1,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.45  fof(f232,plain,(
% 0.21/0.45    ~r1_orders_2(sK0,sK1,sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f231,f69])).
% 0.21/0.45  fof(f231,plain,(
% 0.21/0.45    ~r1_orders_2(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f230,f35])).
% 0.21/0.45  fof(f230,plain,(
% 0.21/0.45    ~r1_orders_2(sK0,sK1,sK1) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f229,f38])).
% 0.21/0.45  fof(f229,plain,(
% 0.21/0.45    ~r1_orders_2(sK0,sK1,sK1) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f228,f39])).
% 0.21/0.45  fof(f228,plain,(
% 0.21/0.45    ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f227,f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f227,plain,(
% 0.21/0.45    ~r1_orders_2(sK0,sK1,sK1) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f226,f120])).
% 0.21/0.45  fof(f120,plain,(
% 0.21/0.45    r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f119,f69])).
% 0.21/0.45  fof(f119,plain,(
% 0.21/0.45    r3_orders_2(sK0,sK1,sK2) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f118,f35])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    r3_orders_2(sK0,sK1,sK2) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f117,f38])).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    r3_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f116,f39])).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    r3_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f115,f40])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    r3_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f114])).
% 0.21/0.45  fof(f114,plain,(
% 0.21/0.45    r3_orders_2(sK0,sK1,sK2) | r3_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(resolution,[],[f99,f54])).
% 0.21/0.45  fof(f54,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f34])).
% 0.21/0.45  fof(f99,plain,(
% 0.21/0.45    r1_orders_2(sK0,sK1,sK2) | r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f98,f36])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    v5_orders_2(sK0)),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f98,plain,(
% 0.21/0.45    r1_orders_2(sK0,sK1,sK2) | ~v5_orders_2(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f97,f37])).
% 0.21/0.45  fof(f97,plain,(
% 0.21/0.45    r1_orders_2(sK0,sK1,sK2) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f96,f38])).
% 0.21/0.45  fof(f96,plain,(
% 0.21/0.45    r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f95,f40])).
% 0.21/0.45  fof(f95,plain,(
% 0.21/0.45    r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f90,f39])).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f89])).
% 0.21/0.45  fof(f89,plain,(
% 0.21/0.45    r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(superposition,[],[f65,f79])).
% 0.21/0.45  fof(f79,plain,(
% 0.21/0.45    sK1 = k11_lattice3(sK0,sK1,sK2) | r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f78,f36])).
% 0.21/0.45  fof(f78,plain,(
% 0.21/0.45    sK1 = k11_lattice3(sK0,sK1,sK2) | ~v5_orders_2(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f77,f37])).
% 0.21/0.45  fof(f77,plain,(
% 0.21/0.45    sK1 = k11_lattice3(sK0,sK1,sK2) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f76,f38])).
% 0.21/0.45  fof(f76,plain,(
% 0.21/0.45    sK1 = k11_lattice3(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f75,f39])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    sK1 = k11_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f72,f40])).
% 0.21/0.45  fof(f72,plain,(
% 0.21/0.45    sK1 = k11_lattice3(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0) | r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(superposition,[],[f55,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    sK1 = k12_lattice3(sK0,sK1,sK2) | r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  fof(f55,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f22])).
% 0.21/0.45  fof(f22,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f21])).
% 0.21/0.45  fof(f21,plain,(
% 0.21/0.45    ! [X0,X1,X2] : (k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f5])).
% 0.21/0.45  fof(f5,axiom,(
% 0.21/0.45    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => k11_lattice3(X0,X1,X2) = k12_lattice3(X0,X1,X2))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k12_lattice3)).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f57,f43])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (r1_orders_2(X0,k11_lattice3(X0,X1,X2),X2) | ~m1_subset_1(k11_lattice3(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(equality_resolution,[],[f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,X3,X2) | k11_lattice3(X0,X1,X2) != X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f33])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    ! [X3,X2,X1,X0] : (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) & r1_orders_2(X0,sK3(X0,X1,X2,X3),X1) & m1_subset_1(sK3(X0,X1,X2,X3),u1_struct_0(X0))))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X5] : (r1_orders_2(X0,X5,X3) | ~r1_orders_2(X0,X5,X2) | ~r1_orders_2(X0,X5,X1) | ~m1_subset_1(X5,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(rectify,[],[f30])).
% 0.21/0.45  fof(f30,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | ? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1)) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k11_lattice3(X0,X1,X2) = X3 | (? [X4] : (~r1_orders_2(X0,X4,X3) & r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1))) & ((! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)) | k11_lattice3(X0,X1,X2) != X3)) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(nnf_transformation,[],[f14])).
% 0.21/0.45  fof(f14,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (r1_orders_2(X0,X4,X3) | ~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f13])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : ((r1_orders_2(X0,X4,X3) | (~r1_orders_2(X0,X4,X2) | ~r1_orders_2(X0,X4,X1))) | ~m1_subset_1(X4,u1_struct_0(X0))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f4])).
% 0.21/0.45  fof(f4,axiom,(
% 0.21/0.45    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k11_lattice3(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ((r1_orders_2(X0,X4,X2) & r1_orders_2(X0,X4,X1)) => r1_orders_2(X0,X4,X3))) & r1_orders_2(X0,X3,X2) & r1_orders_2(X0,X3,X1)))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l28_lattice3)).
% 0.21/0.45  fof(f226,plain,(
% 0.21/0.45    ~r1_orders_2(sK0,sK1,sK1) | ~r3_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)),
% 0.21/0.45    inference(resolution,[],[f224,f53])).
% 0.21/0.45  fof(f224,plain,(
% 0.21/0.45    ~r1_orders_2(sK0,sK1,sK2) | ~r1_orders_2(sK0,sK1,sK1)),
% 0.21/0.45    inference(subsumption_resolution,[],[f223,f36])).
% 0.21/0.45  fof(f223,plain,(
% 0.21/0.45    ~r1_orders_2(sK0,sK1,sK1) | ~r1_orders_2(sK0,sK1,sK2) | ~v5_orders_2(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f222,f37])).
% 0.21/0.45  fof(f222,plain,(
% 0.21/0.45    ~r1_orders_2(sK0,sK1,sK1) | ~r1_orders_2(sK0,sK1,sK2) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f221,f38])).
% 0.21/0.45  fof(f221,plain,(
% 0.21/0.45    ~r1_orders_2(sK0,sK1,sK1) | ~r1_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f220,f40])).
% 0.21/0.45  fof(f220,plain,(
% 0.21/0.45    ~r1_orders_2(sK0,sK1,sK1) | ~r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f219,f39])).
% 0.21/0.45  fof(f219,plain,(
% 0.21/0.45    ~r1_orders_2(sK0,sK1,sK1) | ~r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f206,f120])).
% 0.21/0.45  fof(f206,plain,(
% 0.21/0.45    ~r3_orders_2(sK0,sK1,sK2) | ~r1_orders_2(sK0,sK1,sK1) | ~r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.45    inference(trivial_inequality_removal,[],[f205])).
% 0.21/0.45  fof(f205,plain,(
% 0.21/0.45    sK1 != sK1 | ~r3_orders_2(sK0,sK1,sK2) | ~r1_orders_2(sK0,sK1,sK1) | ~r1_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.45    inference(superposition,[],[f84,f165])).
% 0.21/0.45  fof(f165,plain,(
% 0.21/0.45    ( ! [X4,X5,X3] : (k11_lattice3(X3,X5,X4) = X5 | ~r1_orders_2(X3,X5,X5) | ~r1_orders_2(X3,X5,X4) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v2_lattice3(X3) | ~v5_orders_2(X3)) )),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f145])).
% 0.21/0.45  fof(f145,plain,(
% 0.21/0.45    ( ! [X4,X5,X3] : (k11_lattice3(X3,X5,X4) = X5 | ~r1_orders_2(X3,X5,X5) | ~r1_orders_2(X3,X5,X4) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v2_lattice3(X3) | ~v5_orders_2(X3) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v2_lattice3(X3) | ~v5_orders_2(X3)) )),
% 0.21/0.45    inference(superposition,[],[f142,f51])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f16])).
% 0.21/0.45  fof(f16,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0))),
% 0.21/0.45    inference(flattening,[],[f15])).
% 0.21/0.45  fof(f15,plain,(
% 0.21/0.45    ! [X0] : (! [X1] : (! [X2] : (k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)))),
% 0.21/0.45    inference(ennf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : ((l1_orders_2(X0) & v2_lattice3(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k11_lattice3(X0,X1,X2) = k11_lattice3(X0,X2,X1))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_lattice3)).
% 0.21/0.45  fof(f142,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = X2 | ~r1_orders_2(X0,X2,X2) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.45    inference(duplicate_literal_removal,[],[f139])).
% 0.21/0.45  fof(f139,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k11_lattice3(X0,X1,X2) = X2 | ~r1_orders_2(X0,X2,X2) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | k11_lattice3(X0,X1,X2) = X2 | ~r1_orders_2(X0,X2,X2) | ~r1_orders_2(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.45    inference(resolution,[],[f61,f60])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) | k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f50,f43])).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,sK3(X0,X1,X2,X3),X3) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f33])).
% 0.21/0.45  fof(f61,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) | k11_lattice3(X0,X1,X2) = X3 | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.45    inference(subsumption_resolution,[],[f49,f43])).
% 0.21/0.45  fof(f49,plain,(
% 0.21/0.45    ( ! [X2,X0,X3,X1] : (k11_lattice3(X0,X1,X2) = X3 | r1_orders_2(X0,sK3(X0,X1,X2,X3),X2) | ~r1_orders_2(X0,X3,X2) | ~r1_orders_2(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v2_lattice3(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f33])).
% 0.21/0.45  fof(f84,plain,(
% 0.21/0.45    sK1 != k11_lattice3(sK0,sK1,sK2) | ~r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(subsumption_resolution,[],[f83,f36])).
% 0.21/0.45  fof(f83,plain,(
% 0.21/0.45    sK1 != k11_lattice3(sK0,sK1,sK2) | ~r3_orders_2(sK0,sK1,sK2) | ~v5_orders_2(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f82,f37])).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    sK1 != k11_lattice3(sK0,sK1,sK2) | ~r3_orders_2(sK0,sK1,sK2) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f81,f38])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    sK1 != k11_lattice3(sK0,sK1,sK2) | ~r3_orders_2(sK0,sK1,sK2) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f80,f39])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    sK1 != k11_lattice3(sK0,sK1,sK2) | ~r3_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.45    inference(subsumption_resolution,[],[f73,f40])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    sK1 != k11_lattice3(sK0,sK1,sK2) | ~r3_orders_2(sK0,sK1,sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v2_lattice3(sK0) | ~v5_orders_2(sK0)),
% 0.21/0.45    inference(superposition,[],[f42,f55])).
% 0.21/0.45  fof(f42,plain,(
% 0.21/0.45    sK1 != k12_lattice3(sK0,sK1,sK2) | ~r3_orders_2(sK0,sK1,sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f28])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (5023)------------------------------
% 0.21/0.45  % (5023)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (5023)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (5023)Memory used [KB]: 1663
% 0.21/0.45  % (5023)Time elapsed: 0.030 s
% 0.21/0.45  % (5023)------------------------------
% 0.21/0.45  % (5023)------------------------------
% 0.21/0.45  % (5004)Success in time 0.088 s
%------------------------------------------------------------------------------
