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
% DateTime   : Thu Dec  3 13:15:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 177 expanded)
%              Number of leaves         :    9 (  63 expanded)
%              Depth                    :   19
%              Number of atoms          :  252 (1115 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f101,plain,(
    $false ),
    inference(subsumption_resolution,[],[f99,f30])).

fof(f30,plain,(
    ~ r2_lattice3(sK2,sK3,sK5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r2_lattice3(sK2,sK3,sK5)
    & r1_orders_2(sK2,sK4,sK5)
    & r2_lattice3(sK2,sK3,sK4)
    & m1_subset_1(sK5,u1_struct_0(sK2))
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v4_orders_2(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f6,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ? [X3] :
                ( ~ r2_lattice3(X0,X1,X3)
                & r1_orders_2(X0,X2,X3)
                & r2_lattice3(X0,X1,X2)
                & m1_subset_1(X3,u1_struct_0(X0)) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v4_orders_2(X0) )
   => ( ? [X2,X1] :
          ( ? [X3] :
              ( ~ r2_lattice3(sK2,X1,X3)
              & r1_orders_2(sK2,X2,X3)
              & r2_lattice3(sK2,X1,X2)
              & m1_subset_1(X3,u1_struct_0(sK2)) )
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v4_orders_2(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X2,X1] :
        ( ? [X3] :
            ( ~ r2_lattice3(sK2,X1,X3)
            & r1_orders_2(sK2,X2,X3)
            & r2_lattice3(sK2,X1,X2)
            & m1_subset_1(X3,u1_struct_0(sK2)) )
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( ? [X3] :
          ( ~ r2_lattice3(sK2,sK3,X3)
          & r1_orders_2(sK2,sK4,X3)
          & r2_lattice3(sK2,sK3,sK4)
          & m1_subset_1(X3,u1_struct_0(sK2)) )
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X3] :
        ( ~ r2_lattice3(sK2,sK3,X3)
        & r1_orders_2(sK2,sK4,X3)
        & r2_lattice3(sK2,sK3,sK4)
        & m1_subset_1(X3,u1_struct_0(sK2)) )
   => ( ~ r2_lattice3(sK2,sK3,sK5)
      & r1_orders_2(sK2,sK4,sK5)
      & r2_lattice3(sK2,sK3,sK4)
      & m1_subset_1(sK5,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r2_lattice3(X0,X1,X3)
              & r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ? [X3] :
              ( ~ r2_lattice3(X0,X1,X3)
              & r1_orders_2(X0,X2,X3)
              & r2_lattice3(X0,X1,X2)
              & m1_subset_1(X3,u1_struct_0(X0)) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v4_orders_2(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( ( r1_orders_2(X0,X2,X3)
                    & r2_lattice3(X0,X1,X2) )
                 => r2_lattice3(X0,X1,X3) ) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ( ( r1_orders_2(X0,X2,X3)
                  & r2_lattice3(X0,X1,X2) )
               => r2_lattice3(X0,X1,X3) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow_0)).

fof(f99,plain,(
    r2_lattice3(sK2,sK3,sK5) ),
    inference(resolution,[],[f98,f48])).

fof(f48,plain,(
    ! [X1] :
      ( ~ sP0(sK5,sK2,X1)
      | r2_lattice3(sK2,X1,sK5) ) ),
    inference(resolution,[],[f32,f42])).

fof(f42,plain,(
    ! [X1] : sP1(X1,sK2,sK5) ),
    inference(subsumption_resolution,[],[f40,f25])).

fof(f25,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f40,plain,(
    ! [X1] :
      ( sP1(X1,sK2,sK5)
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f37,f27])).

fof(f27,plain,(
    m1_subset_1(sK5,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP1(X1,X0,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP1(X1,X0,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(definition_folding,[],[f8,f12,f11])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( r1_orders_2(X0,X3,X2)
          | ~ r2_hidden(X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f12,plain,(
    ! [X1,X0,X2] :
      ( ( r2_lattice3(X0,X1,X2)
      <=> sP0(X2,X0,X1) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | r2_lattice3(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_lattice3(X1,X0,X2)
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_lattice3(X1,X0,X2) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f18])).

fof(f18,plain,(
    ! [X1,X0,X2] :
      ( ( ( r2_lattice3(X0,X1,X2)
          | ~ sP0(X2,X0,X1) )
        & ( sP0(X2,X0,X1)
          | ~ r2_lattice3(X0,X1,X2) ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f98,plain,(
    sP0(sK5,sK2,sK3) ),
    inference(duplicate_literal_removal,[],[f97])).

fof(f97,plain,
    ( sP0(sK5,sK2,sK3)
    | sP0(sK5,sK2,sK3) ),
    inference(resolution,[],[f92,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK6(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r1_orders_2(X1,sK6(X0,X1,X2),X0)
          & r2_hidden(sK6(X0,X1,X2),X2)
          & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_orders_2(X1,sK6(X0,X1,X2),X0)
        & r2_hidden(sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_orders_2(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_orders_2(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_orders_2(X0,X3,X2)
            & r2_hidden(X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_orders_2(X0,X3,X2)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f92,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK5,sK2,X0),sK3)
      | sP0(sK5,sK2,X0) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK6(sK5,sK2,X0),sK3)
      | sP0(sK5,sK2,X0)
      | sP0(sK5,sK2,X0) ) ),
    inference(resolution,[],[f89,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X1,sK6(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK2,sK6(X0,sK2,X1),sK5)
      | ~ r2_hidden(sK6(X0,sK2,X1),sK3)
      | sP0(X0,sK2,X1) ) ),
    inference(subsumption_resolution,[],[f88,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK2,sK6(X0,sK2,X1),sK5)
      | ~ m1_subset_1(sK6(X0,sK2,X1),u1_struct_0(sK2))
      | ~ r2_hidden(sK6(X0,sK2,X1),sK3)
      | sP0(X0,sK2,X1) ) ),
    inference(resolution,[],[f83,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_orders_2(sK2,sK6(X0,sK2,X1),sK4)
      | ~ r2_hidden(sK6(X0,sK2,X1),sK3)
      | sP0(X0,sK2,X1) ) ),
    inference(resolution,[],[f52,f34])).

fof(f52,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ r2_hidden(X0,sK3)
      | r1_orders_2(sK2,X0,sK4) ) ),
    inference(resolution,[],[f33,f46])).

fof(f46,plain,(
    sP0(sK4,sK2,sK3) ),
    inference(resolution,[],[f44,f28])).

fof(f28,plain,(
    r2_lattice3(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0] :
      ( ~ r2_lattice3(sK2,X0,sK4)
      | sP0(sK4,sK2,X0) ) ),
    inference(resolution,[],[f31,f41])).

fof(f41,plain,(
    ! [X0] : sP1(X0,sK2,sK4) ),
    inference(subsumption_resolution,[],[f39,f25])).

fof(f39,plain,(
    ! [X0] :
      ( sP1(X0,sK2,sK4)
      | ~ l1_orders_2(sK2) ) ),
    inference(resolution,[],[f37,f26])).

fof(f26,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_lattice3(X1,X0,X2)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f33,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_orders_2(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f83,plain,(
    ! [X0] :
      ( ~ r1_orders_2(sK2,X0,sK4)
      | r1_orders_2(sK2,X0,sK5)
      | ~ m1_subset_1(X0,u1_struct_0(sK2)) ) ),
    inference(subsumption_resolution,[],[f82,f24])).

fof(f24,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,(
    ! [X0] :
      ( r1_orders_2(sK2,X0,sK5)
      | ~ r1_orders_2(sK2,X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ v4_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f81,f25])).

fof(f81,plain,(
    ! [X0] :
      ( r1_orders_2(sK2,X0,sK5)
      | ~ r1_orders_2(sK2,X0,sK4)
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f80,f26])).

fof(f80,plain,(
    ! [X0] :
      ( r1_orders_2(sK2,X0,sK5)
      | ~ r1_orders_2(sK2,X0,sK4)
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2) ) ),
    inference(subsumption_resolution,[],[f78,f27])).

fof(f78,plain,(
    ! [X0] :
      ( r1_orders_2(sK2,X0,sK5)
      | ~ r1_orders_2(sK2,X0,sK4)
      | ~ m1_subset_1(sK5,u1_struct_0(sK2))
      | ~ m1_subset_1(sK4,u1_struct_0(sK2))
      | ~ m1_subset_1(X0,u1_struct_0(sK2))
      | ~ l1_orders_2(sK2)
      | ~ v4_orders_2(sK2) ) ),
    inference(resolution,[],[f38,f29])).

fof(f29,plain,(
    r1_orders_2(sK2,sK4,sK5) ),
    inference(cnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_orders_2(X0,X2,X3)
      | r1_orders_2(X0,X1,X3)
      | ~ r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( r1_orders_2(X0,X1,X3)
                  | ~ r1_orders_2(X0,X2,X3)
                  | ~ r1_orders_2(X0,X1,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( ( r1_orders_2(X0,X2,X3)
                      & r1_orders_2(X0,X1,X2) )
                   => r1_orders_2(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:35:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (28294)dis+10_128_add=large:afr=on:afp=4000:afq=1.0:amm=off:anc=none:lma=on:nm=2:nwc=1:sp=reverse_arity_3 on theBenchmark
% 0.20/0.43  % (28294)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(subsumption_resolution,[],[f99,f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ~r2_lattice3(sK2,sK3,sK5)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    ((~r2_lattice3(sK2,sK3,sK5) & r1_orders_2(sK2,sK4,sK5) & r2_lattice3(sK2,sK3,sK4) & m1_subset_1(sK5,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(sK2))) & l1_orders_2(sK2) & v4_orders_2(sK2)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f6,f16,f15,f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ? [X0] : (? [X1,X2] : (? [X3] : (~r2_lattice3(X0,X1,X3) & r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & l1_orders_2(X0) & v4_orders_2(X0)) => (? [X2,X1] : (? [X3] : (~r2_lattice3(sK2,X1,X3) & r1_orders_2(sK2,X2,X3) & r2_lattice3(sK2,X1,X2) & m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(X2,u1_struct_0(sK2))) & l1_orders_2(sK2) & v4_orders_2(sK2))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ? [X2,X1] : (? [X3] : (~r2_lattice3(sK2,X1,X3) & r1_orders_2(sK2,X2,X3) & r2_lattice3(sK2,X1,X2) & m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(X2,u1_struct_0(sK2))) => (? [X3] : (~r2_lattice3(sK2,sK3,X3) & r1_orders_2(sK2,sK4,X3) & r2_lattice3(sK2,sK3,sK4) & m1_subset_1(X3,u1_struct_0(sK2))) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ? [X3] : (~r2_lattice3(sK2,sK3,X3) & r1_orders_2(sK2,sK4,X3) & r2_lattice3(sK2,sK3,sK4) & m1_subset_1(X3,u1_struct_0(sK2))) => (~r2_lattice3(sK2,sK3,sK5) & r1_orders_2(sK2,sK4,sK5) & r2_lattice3(sK2,sK3,sK4) & m1_subset_1(sK5,u1_struct_0(sK2)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f6,plain,(
% 0.20/0.43    ? [X0] : (? [X1,X2] : (? [X3] : (~r2_lattice3(X0,X1,X3) & r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X2) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & l1_orders_2(X0) & v4_orders_2(X0))),
% 0.20/0.43    inference(flattening,[],[f5])).
% 0.20/0.43  fof(f5,plain,(
% 0.20/0.43    ? [X0] : (? [X1,X2] : (? [X3] : ((~r2_lattice3(X0,X1,X3) & (r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X2))) & m1_subset_1(X3,u1_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & (l1_orders_2(X0) & v4_orders_2(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,negated_conjecture,(
% 0.20/0.43    ~! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X2)) => r2_lattice3(X0,X1,X3)))))),
% 0.20/0.43    inference(negated_conjecture,[],[f3])).
% 0.20/0.43  fof(f3,conjecture,(
% 0.20/0.43    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_lattice3(X0,X1,X2)) => r2_lattice3(X0,X1,X3)))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_yellow_0)).
% 0.20/0.43  fof(f99,plain,(
% 0.20/0.43    r2_lattice3(sK2,sK3,sK5)),
% 0.20/0.43    inference(resolution,[],[f98,f48])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X1] : (~sP0(sK5,sK2,X1) | r2_lattice3(sK2,X1,sK5)) )),
% 0.20/0.43    inference(resolution,[],[f32,f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X1] : (sP1(X1,sK2,sK5)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f40,f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    l1_orders_2(sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X1] : (sP1(X1,sK2,sK5) | ~l1_orders_2(sK2)) )),
% 0.20/0.43    inference(resolution,[],[f37,f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    m1_subset_1(sK5,u1_struct_0(sK2))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | sP1(X1,X0,X2) | ~l1_orders_2(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    ! [X0] : (! [X1,X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.43    inference(definition_folding,[],[f8,f12,f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.20/0.43    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ! [X1,X0,X2] : ((r2_lattice3(X0,X1,X2) <=> sP0(X2,X0,X1)) | ~sP1(X1,X0,X2))),
% 0.20/0.43    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.43    inference(flattening,[],[f7])).
% 0.20/0.43  fof(f7,plain,(
% 0.20/0.43    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_lattice3)).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | r2_lattice3(X1,X0,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ! [X0,X1,X2] : (((r2_lattice3(X1,X0,X2) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_lattice3(X1,X0,X2))) | ~sP1(X0,X1,X2))),
% 0.20/0.43    inference(rectify,[],[f18])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    ! [X1,X0,X2] : (((r2_lattice3(X0,X1,X2) | ~sP0(X2,X0,X1)) & (sP0(X2,X0,X1) | ~r2_lattice3(X0,X1,X2))) | ~sP1(X1,X0,X2))),
% 0.20/0.43    inference(nnf_transformation,[],[f12])).
% 0.20/0.43  fof(f98,plain,(
% 0.20/0.43    sP0(sK5,sK2,sK3)),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f97])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    sP0(sK5,sK2,sK3) | sP0(sK5,sK2,sK3)),
% 0.20/0.43    inference(resolution,[],[f92,f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (r2_hidden(sK6(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r1_orders_2(X1,sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_orders_2(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f21,f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_orders_2(X1,sK6(X0,X1,X2),X0) & r2_hidden(sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r1_orders_2(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_orders_2(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.43    inference(rectify,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X2,X0,X1)))),
% 0.20/0.43    inference(nnf_transformation,[],[f11])).
% 0.20/0.43  fof(f92,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(sK6(sK5,sK2,X0),sK3) | sP0(sK5,sK2,X0)) )),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f90])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_hidden(sK6(sK5,sK2,X0),sK3) | sP0(sK5,sK2,X0) | sP0(sK5,sK2,X0)) )),
% 0.20/0.43    inference(resolution,[],[f89,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_orders_2(X1,sK6(X0,X1,X2),X0) | sP0(X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f23])).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_orders_2(sK2,sK6(X0,sK2,X1),sK5) | ~r2_hidden(sK6(X0,sK2,X1),sK3) | sP0(X0,sK2,X1)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f88,f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f23])).
% 0.20/0.43  fof(f88,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_orders_2(sK2,sK6(X0,sK2,X1),sK5) | ~m1_subset_1(sK6(X0,sK2,X1),u1_struct_0(sK2)) | ~r2_hidden(sK6(X0,sK2,X1),sK3) | sP0(X0,sK2,X1)) )),
% 0.20/0.43    inference(resolution,[],[f83,f55])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r1_orders_2(sK2,sK6(X0,sK2,X1),sK4) | ~r2_hidden(sK6(X0,sK2,X1),sK3) | sP0(X0,sK2,X1)) )),
% 0.20/0.43    inference(resolution,[],[f52,f34])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK2)) | ~r2_hidden(X0,sK3) | r1_orders_2(sK2,X0,sK4)) )),
% 0.20/0.43    inference(resolution,[],[f33,f46])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    sP0(sK4,sK2,sK3)),
% 0.20/0.43    inference(resolution,[],[f44,f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    r2_lattice3(sK2,sK3,sK4)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X0] : (~r2_lattice3(sK2,X0,sK4) | sP0(sK4,sK2,X0)) )),
% 0.20/0.43    inference(resolution,[],[f31,f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X0] : (sP1(X0,sK2,sK4)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f39,f25])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ( ! [X0] : (sP1(X0,sK2,sK4) | ~l1_orders_2(sK2)) )),
% 0.20/0.43    inference(resolution,[],[f37,f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    m1_subset_1(sK4,u1_struct_0(sK2))),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | ~r2_lattice3(X1,X0,X2) | sP0(X2,X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f19])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_orders_2(X1,X4,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f23])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    ( ! [X0] : (~r1_orders_2(sK2,X0,sK4) | r1_orders_2(sK2,X0,sK5) | ~m1_subset_1(X0,u1_struct_0(sK2))) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f82,f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    v4_orders_2(sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    ( ! [X0] : (r1_orders_2(sK2,X0,sK5) | ~r1_orders_2(sK2,X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~v4_orders_2(sK2)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f81,f25])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    ( ! [X0] : (r1_orders_2(sK2,X0,sK5) | ~r1_orders_2(sK2,X0,sK4) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~v4_orders_2(sK2)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f80,f26])).
% 0.20/0.43  fof(f80,plain,(
% 0.20/0.43    ( ! [X0] : (r1_orders_2(sK2,X0,sK5) | ~r1_orders_2(sK2,X0,sK4) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~v4_orders_2(sK2)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f78,f27])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    ( ! [X0] : (r1_orders_2(sK2,X0,sK5) | ~r1_orders_2(sK2,X0,sK4) | ~m1_subset_1(sK5,u1_struct_0(sK2)) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | ~m1_subset_1(X0,u1_struct_0(sK2)) | ~l1_orders_2(sK2) | ~v4_orders_2(sK2)) )),
% 0.20/0.43    inference(resolution,[],[f38,f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    r1_orders_2(sK2,sK4,sK5)),
% 0.20/0.43    inference(cnf_transformation,[],[f17])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X2,X0,X3,X1] : (~r1_orders_2(X0,X2,X3) | r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v4_orders_2(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (r1_orders_2(X0,X1,X3) | ~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v4_orders_2(X0))),
% 0.20/0.43    inference(flattening,[],[f9])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_orders_2(X0,X1,X3) | (~r1_orders_2(X0,X2,X3) | ~r1_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v4_orders_2(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0] : ((l1_orders_2(X0) & v4_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r1_orders_2(X0,X1,X2)) => r1_orders_2(X0,X1,X3))))))),
% 0.20/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_orders_2)).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (28294)------------------------------
% 0.20/0.43  % (28294)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (28294)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (28294)Memory used [KB]: 5373
% 0.20/0.43  % (28294)Time elapsed: 0.006 s
% 0.20/0.43  % (28294)------------------------------
% 0.20/0.43  % (28294)------------------------------
% 0.20/0.43  % (28286)Success in time 0.072 s
%------------------------------------------------------------------------------
