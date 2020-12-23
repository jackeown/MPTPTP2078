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
% DateTime   : Thu Dec  3 13:15:38 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  156 (5723 expanded)
%              Number of leaves         :   19 (1602 expanded)
%              Depth                    :   26
%              Number of atoms          :  715 (40045 expanded)
%              Number of equality atoms :   19 ( 306 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f592,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f107,f536,f591])).

fof(f591,plain,
    ( spl5_1
    | ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f590])).

fof(f590,plain,
    ( $false
    | spl5_1
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f579,f589])).

fof(f589,plain,
    ( ~ r1_orders_2(k3_lattice3(sK1),sK4(sK1,sK2,sK0),sK2)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f114,f116,f119,f137,f552,f574,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | r3_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f574,plain,
    ( ~ r3_orders_2(k3_lattice3(sK1),sK4(sK1,sK2,sK0),sK2)
    | spl5_1 ),
    inference(forward_demodulation,[],[f573,f545])).

fof(f545,plain,
    ( sK4(sK1,sK2,sK0) = k4_lattice3(sK1,sK4(sK1,sK2,sK0))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f60,f101,f199])).

fof(f199,plain,(
    ! [X2,X3] :
      ( r4_lattice3(sK1,X2,X3)
      | ~ m1_subset_1(X2,u1_struct_0(sK1))
      | sK4(sK1,X2,X3) = k4_lattice3(sK1,sK4(sK1,X2,X3)) ) ),
    inference(resolution,[],[f166,f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | k4_lattice3(sK1,X0) = X0 ) ),
    inference(global_subsumption,[],[f59,f57,f121])).

fof(f121,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | k4_lattice3(sK1,X0) = X0
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f84,f58])).

fof(f58,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( ~ r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
      | ~ r4_lattice3(sK1,sK2,sK0) )
    & ( r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
      | r4_lattice3(sK1,sK2,sK0) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f44,f43])).

fof(f43,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
              | ~ r4_lattice3(X1,X2,X0) )
            & ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
              | r4_lattice3(X1,X2,X0) )
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,X2))
            | ~ r4_lattice3(sK1,X2,sK0) )
          & ( r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,X2))
            | r4_lattice3(sK1,X2,sK0) )
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( ( ~ r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,X2))
          | ~ r4_lattice3(sK1,X2,sK0) )
        & ( r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,X2))
          | r4_lattice3(sK1,X2,sK0) )
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ( ~ r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
        | ~ r4_lattice3(sK1,sK2,sK0) )
      & ( r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
        | r4_lattice3(sK1,sK2,sK0) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
            | ~ r4_lattice3(X1,X2,X0) )
          & ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
            | r4_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
            | ~ r4_lattice3(X1,X2,X0) )
          & ( r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))
            | r4_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <~> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <~> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( l3_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r4_lattice3(X1,X2,X0)
            <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r4_lattice3(X1,X2,X0)
          <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_lattice3)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k4_lattice3(X0,X1) = X1
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattice3)).

fof(f57,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f59,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f166,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r4_lattice3(sK1,X0,X1) ) ),
    inference(global_subsumption,[],[f57,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK1))
      | ~ m1_subset_1(X0,u1_struct_0(sK1))
      | r4_lattice3(sK1,X0,X1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f89,f59])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r4_lattice3(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
                  & r2_hidden(sK4(X0,X1,X2),X2)
                  & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
        & r2_hidden(sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X3,X1)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X3,X1)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r4_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X3,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(f101,plain,
    ( ~ r4_lattice3(sK1,sK2,sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_1
  <=> r4_lattice3(sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f60,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f573,plain,
    ( ~ r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK4(sK1,sK2,sK0)),sK2)
    | spl5_1 ),
    inference(forward_demodulation,[],[f571,f120])).

fof(f120,plain,(
    sK2 = k4_lattice3(sK1,sK2) ),
    inference(unit_resulting_resolution,[],[f57,f58,f59,f60,f84])).

fof(f571,plain,
    ( ~ r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK4(sK1,sK2,sK0)),k4_lattice3(sK1,sK2))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f57,f58,f59,f60,f549,f564,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r3_lattices(X0,X1,X2)
                  | ~ r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
                & ( r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
                  | ~ r3_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_lattices(X0,X1,X2)
              <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_lattice3)).

fof(f564,plain,
    ( ~ r3_lattices(sK1,sK4(sK1,sK2,sK0),sK2)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f57,f110,f112,f113,f59,f60,f548,f549,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f548,plain,
    ( ~ r1_lattices(sK1,sK4(sK1,sK2,sK0),sK2)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f57,f59,f60,f101,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,sK4(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f113,plain,(
    v9_lattices(sK1) ),
    inference(unit_resulting_resolution,[],[f59,f57,f58,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f112,plain,(
    v8_lattices(sK1) ),
    inference(unit_resulting_resolution,[],[f59,f57,f58,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f110,plain,(
    v6_lattices(sK1) ),
    inference(unit_resulting_resolution,[],[f59,f57,f58,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f549,plain,
    ( m1_subset_1(sK4(sK1,sK2,sK0),u1_struct_0(sK1))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f57,f59,f60,f101,f89])).

fof(f552,plain,
    ( m1_subset_1(sK4(sK1,sK2,sK0),u1_struct_0(k3_lattice3(sK1)))
    | spl5_1 ),
    inference(backward_demodulation,[],[f546,f545])).

fof(f546,plain,
    ( m1_subset_1(k4_lattice3(sK1,sK4(sK1,sK2,sK0)),u1_struct_0(k3_lattice3(sK1)))
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f60,f101,f198])).

fof(f198,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattice3(sK1,sK4(sK1,X0,X1)),u1_struct_0(k3_lattice3(sK1)))
      | r4_lattice3(sK1,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK1)) ) ),
    inference(resolution,[],[f166,f138])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | m1_subset_1(k4_lattice3(sK1,X0),u1_struct_0(k3_lattice3(sK1))) ) ),
    inference(global_subsumption,[],[f59,f57,f136])).

fof(f136,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK1))
      | ~ l3_lattices(sK1)
      | m1_subset_1(k4_lattice3(sK1,X0),u1_struct_0(k3_lattice3(sK1)))
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f92,f58])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattice3)).

fof(f137,plain,(
    m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1))) ),
    inference(forward_demodulation,[],[f135,f120])).

fof(f135,plain,(
    m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(sK1))) ),
    inference(unit_resulting_resolution,[],[f57,f58,f59,f60,f92])).

fof(f119,plain,(
    l1_orders_2(k3_lattice3(sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f58,f59,f83])).

fof(f83,plain,(
    ! [X0] :
      ( l1_orders_2(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( l1_orders_2(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( l1_orders_2(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_orders_2(k3_lattice3(X0))
        & v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_lattice3)).

fof(f116,plain,(
    v3_orders_2(k3_lattice3(sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f58,f59,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v3_orders_2(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v5_orders_2(k3_lattice3(X0))
        & v4_orders_2(k3_lattice3(X0))
        & v3_orders_2(k3_lattice3(X0))
        & v1_orders_2(k3_lattice3(X0))
        & ~ v2_struct_0(k3_lattice3(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_lattice3)).

fof(f114,plain,(
    ~ v2_struct_0(k3_lattice3(sK1)) ),
    inference(unit_resulting_resolution,[],[f57,f58,f59,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_struct_0(k3_lattice3(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f579,plain,
    ( r1_orders_2(k3_lattice3(sK1),sK4(sK1,sK2,sK0),sK2)
    | spl5_1
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f119,f137,f542,f550,f552,f63])).

fof(f63,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ r2_hidden(X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_orders_2(X0,X4,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
                & r2_hidden(sK3(X0,X1,X2),X1)
                & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_orders_2(X0,X3,X2)
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X4] :
                  ( r1_orders_2(X0,X4,X2)
                  | ~ r2_hidden(X4,X1)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( r2_lattice3(X0,X1,X2)
              | ? [X3] :
                  ( ~ r1_orders_2(X0,X3,X2)
                  & r2_hidden(X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( r1_orders_2(X0,X3,X2)
                  | ~ r2_hidden(X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r2_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( r1_orders_2(X0,X3,X2)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1,X2] :
          ( m1_subset_1(X2,u1_struct_0(X0))
         => ( r2_lattice3(X0,X1,X2)
          <=> ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r2_hidden(X3,X1)
                 => r1_orders_2(X0,X3,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).

fof(f550,plain,
    ( r2_hidden(sK4(sK1,sK2,sK0),sK0)
    | spl5_1 ),
    inference(unit_resulting_resolution,[],[f57,f59,f60,f101,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f542,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f104,f120])).

fof(f104,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_2
  <=> r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f536,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f535])).

fof(f535,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(subsumption_resolution,[],[f524,f531])).

fof(f531,plain,
    ( ~ r3_orders_2(k3_lattice3(sK1),sK3(k3_lattice3(sK1),sK0,sK2),sK2)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f114,f116,f119,f137,f488,f489,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f489,plain,
    ( m1_subset_1(sK3(k3_lattice3(sK1),sK0,sK2),u1_struct_0(k3_lattice3(sK1)))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f119,f137,f459,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | r2_lattice3(X0,X1,X2)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f459,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),sK0,sK2)
    | spl5_2 ),
    inference(forward_demodulation,[],[f105,f120])).

fof(f105,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f488,plain,
    ( ~ r1_orders_2(k3_lattice3(sK1),sK3(k3_lattice3(sK1),sK0,sK2),sK2)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f119,f137,f459,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,sK3(X0,X1,X2),X2)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f524,plain,
    ( r3_orders_2(k3_lattice3(sK1),sK3(k3_lattice3(sK1),sK0,sK2),sK2)
    | ~ spl5_1
    | spl5_2 ),
    inference(forward_demodulation,[],[f523,f499])).

fof(f499,plain,
    ( sK3(k3_lattice3(sK1),sK0,sK2) = k4_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2))
    | spl5_2 ),
    inference(backward_demodulation,[],[f485,f483])).

fof(f483,plain,
    ( sK3(k3_lattice3(sK1),sK0,sK2) = k5_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f459,f158])).

fof(f158,plain,(
    ! [X1] :
      ( r2_lattice3(k3_lattice3(sK1),X1,sK2)
      | sK3(k3_lattice3(sK1),X1,sK2) = k5_lattice3(sK1,sK3(k3_lattice3(sK1),X1,sK2)) ) ),
    inference(global_subsumption,[],[f59,f58,f57,f156])).

fof(f156,plain,(
    ! [X1] :
      ( r2_lattice3(k3_lattice3(sK1),X1,sK2)
      | sK3(k3_lattice3(sK1),X1,sK2) = k5_lattice3(sK1,sK3(k3_lattice3(sK1),X1,sK2))
      | ~ l3_lattices(sK1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f142,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | k5_lattice3(X0,X1) = X1
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_lattice3(X0,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
         => k5_lattice3(X0,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_lattice3)).

fof(f142,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(k3_lattice3(sK1),X0,sK2),u1_struct_0(k3_lattice3(sK1)))
      | r2_lattice3(k3_lattice3(sK1),X0,sK2) ) ),
    inference(global_subsumption,[],[f119,f141])).

fof(f141,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(k3_lattice3(sK1),X0,sK2),u1_struct_0(k3_lattice3(sK1)))
      | r2_lattice3(k3_lattice3(sK1),X0,sK2)
      | ~ l1_orders_2(k3_lattice3(sK1)) ) ),
    inference(resolution,[],[f137,f64])).

fof(f485,plain,
    ( k5_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2)) = k4_lattice3(sK1,k5_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2)))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f459,f161])).

fof(f161,plain,(
    ! [X1] :
      ( r2_lattice3(k3_lattice3(sK1),X1,sK2)
      | k5_lattice3(sK1,sK3(k3_lattice3(sK1),X1,sK2)) = k4_lattice3(sK1,k5_lattice3(sK1,sK3(k3_lattice3(sK1),X1,sK2))) ) ),
    inference(resolution,[],[f155,f123])).

fof(f155,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattice3(sK1,sK3(k3_lattice3(sK1),X0,sK2)),u1_struct_0(sK1))
      | r2_lattice3(k3_lattice3(sK1),X0,sK2) ) ),
    inference(resolution,[],[f142,f150])).

fof(f150,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK1)))
      | m1_subset_1(k5_lattice3(sK1,X0),u1_struct_0(sK1)) ) ),
    inference(global_subsumption,[],[f59,f57,f148])).

fof(f148,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(k3_lattice3(sK1)))
      | ~ l3_lattices(sK1)
      | m1_subset_1(k5_lattice3(sK1,X0),u1_struct_0(sK1))
      | v2_struct_0(sK1) ) ),
    inference(resolution,[],[f93,f58])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattice3)).

fof(f523,plain,
    ( r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2)),sK2)
    | ~ spl5_1
    | spl5_2 ),
    inference(forward_demodulation,[],[f521,f120])).

fof(f521,plain,
    ( r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2)),k4_lattice3(sK1,sK2))
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f57,f58,f59,f501,f517,f60,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f517,plain,
    ( r3_lattices(sK1,sK3(k3_lattice3(sK1),sK0,sK2),sK2)
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f57,f110,f112,f113,f59,f60,f501,f509,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f509,plain,
    ( r1_lattices(sK1,sK3(k3_lattice3(sK1),sK0,sK2),sK2)
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f57,f59,f60,f100,f490,f501,f88])).

fof(f88,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattices(X0,X4,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f490,plain,
    ( r2_hidden(sK3(k3_lattice3(sK1),sK0,sK2),sK0)
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f119,f137,f459,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | r2_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f100,plain,
    ( r4_lattice3(sK1,sK2,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f501,plain,
    ( m1_subset_1(sK3(k3_lattice3(sK1),sK0,sK2),u1_struct_0(sK1))
    | spl5_2 ),
    inference(forward_demodulation,[],[f498,f483])).

fof(f498,plain,
    ( m1_subset_1(k5_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2)),u1_struct_0(sK1))
    | spl5_2 ),
    inference(backward_demodulation,[],[f493,f483])).

fof(f493,plain,
    ( m1_subset_1(k5_lattice3(sK1,k5_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2))),u1_struct_0(sK1))
    | spl5_2 ),
    inference(backward_demodulation,[],[f486,f485])).

fof(f486,plain,
    ( m1_subset_1(k5_lattice3(sK1,k4_lattice3(sK1,k5_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2)))),u1_struct_0(sK1))
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f459,f209])).

fof(f209,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattice3(sK1,k4_lattice3(sK1,k5_lattice3(sK1,sK3(k3_lattice3(sK1),X0,sK2)))),u1_struct_0(sK1))
      | r2_lattice3(k3_lattice3(sK1),X0,sK2) ) ),
    inference(resolution,[],[f160,f150])).

fof(f160,plain,(
    ! [X0] :
      ( m1_subset_1(k4_lattice3(sK1,k5_lattice3(sK1,sK3(k3_lattice3(sK1),X0,sK2))),u1_struct_0(k3_lattice3(sK1)))
      | r2_lattice3(k3_lattice3(sK1),X0,sK2) ) ),
    inference(resolution,[],[f155,f138])).

fof(f107,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f61,f103,f99])).

fof(f61,plain,
    ( r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
    | r4_lattice3(sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f106,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f62,f103,f99])).

fof(f62,plain,
    ( ~ r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))
    | ~ r4_lattice3(sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (30138)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.21/0.50  % (30128)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.21/0.50  % (30141)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.50  % (30142)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (30118)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.21/0.50  % (30123)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.50  % (30120)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (30130)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (30140)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.51  % (30124)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.51  % (30129)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.51  % (30119)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (30133)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.51  % (30129)Refutation not found, incomplete strategy% (30129)------------------------------
% 0.21/0.51  % (30129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30129)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30129)Memory used [KB]: 10618
% 0.21/0.51  % (30129)Time elapsed: 0.095 s
% 0.21/0.51  % (30129)------------------------------
% 0.21/0.51  % (30129)------------------------------
% 0.21/0.51  % (30127)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.21/0.51  % (30131)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.21/0.51  % (30121)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.51  % (30126)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (30136)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.51  % (30126)Refutation not found, incomplete strategy% (30126)------------------------------
% 0.21/0.51  % (30126)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30126)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30126)Memory used [KB]: 6140
% 0.21/0.51  % (30126)Time elapsed: 0.106 s
% 0.21/0.51  % (30126)------------------------------
% 0.21/0.51  % (30126)------------------------------
% 0.21/0.51  % (30121)Refutation not found, incomplete strategy% (30121)------------------------------
% 0.21/0.51  % (30121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (30121)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (30121)Memory used [KB]: 10618
% 0.21/0.51  % (30121)Time elapsed: 0.103 s
% 0.21/0.51  % (30121)------------------------------
% 0.21/0.51  % (30121)------------------------------
% 0.21/0.52  % (30132)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.52  % (30134)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.52  % (30142)Refutation not found, incomplete strategy% (30142)------------------------------
% 0.21/0.52  % (30142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30142)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30142)Memory used [KB]: 10746
% 0.21/0.52  % (30142)Time elapsed: 0.092 s
% 0.21/0.52  % (30142)------------------------------
% 0.21/0.52  % (30142)------------------------------
% 0.21/0.52  % (30139)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.21/0.52  % (30135)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.21/0.52  % (30135)Refutation not found, incomplete strategy% (30135)------------------------------
% 0.21/0.52  % (30135)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (30135)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (30135)Memory used [KB]: 1663
% 0.21/0.52  % (30135)Time elapsed: 0.114 s
% 0.21/0.52  % (30135)------------------------------
% 0.21/0.52  % (30135)------------------------------
% 0.21/0.53  % (30137)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.53  % (30125)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.53  % (30136)Refutation not found, incomplete strategy% (30136)------------------------------
% 0.21/0.53  % (30136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (30136)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (30136)Memory used [KB]: 1791
% 0.21/0.53  % (30136)Time elapsed: 0.109 s
% 0.21/0.53  % (30136)------------------------------
% 0.21/0.53  % (30136)------------------------------
% 0.21/0.55  % (30133)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f592,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f106,f107,f536,f591])).
% 0.21/0.56  fof(f591,plain,(
% 0.21/0.56    spl5_1 | ~spl5_2),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f590])).
% 0.21/0.56  fof(f590,plain,(
% 0.21/0.56    $false | (spl5_1 | ~spl5_2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f579,f589])).
% 0.21/0.56  fof(f589,plain,(
% 0.21/0.56    ~r1_orders_2(k3_lattice3(sK1),sK4(sK1,sK2,sK0),sK2) | spl5_1),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f114,f116,f119,f137,f552,f574,f97])).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | r3_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f56])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f40])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f1])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.21/0.56  fof(f574,plain,(
% 0.21/0.56    ~r3_orders_2(k3_lattice3(sK1),sK4(sK1,sK2,sK0),sK2) | spl5_1),
% 0.21/0.56    inference(forward_demodulation,[],[f573,f545])).
% 0.21/0.56  fof(f545,plain,(
% 0.21/0.56    sK4(sK1,sK2,sK0) = k4_lattice3(sK1,sK4(sK1,sK2,sK0)) | spl5_1),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f60,f101,f199])).
% 0.21/0.56  fof(f199,plain,(
% 0.21/0.56    ( ! [X2,X3] : (r4_lattice3(sK1,X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK1)) | sK4(sK1,X2,X3) = k4_lattice3(sK1,sK4(sK1,X2,X3))) )),
% 0.21/0.56    inference(resolution,[],[f166,f123])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | k4_lattice3(sK1,X0) = X0) )),
% 0.21/0.56    inference(global_subsumption,[],[f59,f57,f121])).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~l3_lattices(sK1) | k4_lattice3(sK1,X0) = X0 | v2_struct_0(sK1)) )),
% 0.21/0.56    inference(resolution,[],[f84,f58])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    v10_lattices(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ((~r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2)) | ~r4_lattice3(sK1,sK2,sK0)) & (r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2)) | r4_lattice3(sK1,sK2,sK0)) & m1_subset_1(sK2,u1_struct_0(sK1))) & l3_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f44,f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ? [X0,X1] : (? [X2] : ((~r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) | ~r4_lattice3(X1,X2,X0)) & (r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) | r4_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (? [X2] : ((~r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,X2)) | ~r4_lattice3(sK1,X2,sK0)) & (r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,X2)) | r4_lattice3(sK1,X2,sK0)) & m1_subset_1(X2,u1_struct_0(sK1))) & l3_lattices(sK1) & v10_lattices(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ? [X2] : ((~r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,X2)) | ~r4_lattice3(sK1,X2,sK0)) & (r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,X2)) | r4_lattice3(sK1,X2,sK0)) & m1_subset_1(X2,u1_struct_0(sK1))) => ((~r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2)) | ~r4_lattice3(sK1,sK2,sK0)) & (r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2)) | r4_lattice3(sK1,sK2,sK0)) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ? [X0,X1] : (? [X2] : ((~r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) | ~r4_lattice3(X1,X2,X0)) & (r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) | r4_lattice3(X1,X2,X0)) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 0.21/0.56    inference(flattening,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ? [X0,X1] : (? [X2] : (((~r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) | ~r4_lattice3(X1,X2,X0)) & (r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)) | r4_lattice3(X1,X2,X0))) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ? [X0,X1] : (? [X2] : ((r4_lattice3(X1,X2,X0) <~> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))) & m1_subset_1(X2,u1_struct_0(X1))) & l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1))),
% 0.21/0.56    inference(flattening,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ? [X0,X1] : (? [X2] : ((r4_lattice3(X1,X2,X0) <~> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2))) & m1_subset_1(X2,u1_struct_0(X1))) & (l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f14])).
% 0.21/0.56  fof(f14,negated_conjecture,(
% 0.21/0.56    ~! [X0,X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (r4_lattice3(X1,X2,X0) <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)))))),
% 0.21/0.56    inference(negated_conjecture,[],[f13])).
% 0.21/0.56  fof(f13,conjecture,(
% 0.21/0.56    ! [X0,X1] : ((l3_lattices(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => (r4_lattice3(X1,X2,X0) <=> r2_lattice3(k3_lattice3(X1),X0,k4_lattice3(X1,X2)))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_lattice3)).
% 0.21/0.56  fof(f84,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k4_lattice3(X0,X1) = X1 | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f25])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k4_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k4_lattice3(X0,X1) = X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattice3)).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ~v2_struct_0(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    l3_lattices(sK1)),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  fof(f166,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r4_lattice3(sK1,X0,X1)) )),
% 0.21/0.56    inference(global_subsumption,[],[f57,f165])).
% 0.21/0.56  fof(f165,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(sK4(sK1,X0,X1),u1_struct_0(sK1)) | ~m1_subset_1(X0,u1_struct_0(sK1)) | r4_lattice3(sK1,X0,X1) | v2_struct_0(sK1)) )),
% 0.21/0.56    inference(resolution,[],[f89,f59])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~l3_lattices(X0) | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r4_lattice3(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f52,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(rectify,[],[f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f32])).
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f31])).
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 0.21/0.56  fof(f101,plain,(
% 0.21/0.56    ~r4_lattice3(sK1,sK2,sK0) | spl5_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f99])).
% 0.21/0.56  fof(f99,plain,(
% 0.21/0.56    spl5_1 <=> r4_lattice3(sK1,sK2,sK0)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  fof(f573,plain,(
% 0.21/0.56    ~r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK4(sK1,sK2,sK0)),sK2) | spl5_1),
% 0.21/0.56    inference(forward_demodulation,[],[f571,f120])).
% 0.21/0.56  fof(f120,plain,(
% 0.21/0.56    sK2 = k4_lattice3(sK1,sK2)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f57,f58,f59,f60,f84])).
% 0.21/0.56  fof(f571,plain,(
% 0.21/0.56    ~r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK4(sK1,sK2,sK0)),k4_lattice3(sK1,sK2)) | spl5_1),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f57,f58,f59,f60,f549,f564,f86])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : (((r3_lattices(X0,X1,X2) | ~r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) & (r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,axiom,(
% 0.21/0.56    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2))))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_lattice3)).
% 0.21/0.56  fof(f564,plain,(
% 0.21/0.56    ~r3_lattices(sK1,sK4(sK1,sK2,sK0),sK2) | spl5_1),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f57,f110,f112,f113,f59,f60,f548,f549,f94])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f55])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f38])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.21/0.56  fof(f548,plain,(
% 0.21/0.56    ~r1_lattices(sK1,sK4(sK1,sK2,sK0),sK2) | spl5_1),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f57,f59,f60,f101,f91])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_lattices(X0,sK4(X0,X1,X2),X1) | r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f54])).
% 0.21/0.56  fof(f113,plain,(
% 0.21/0.56    v9_lattices(sK1)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f59,f57,f58,f73])).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.56    inference(flattening,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.56  fof(f112,plain,(
% 0.21/0.56    v8_lattices(sK1)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f59,f57,f58,f72])).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    v6_lattices(sK1)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f59,f57,f58,f70])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f20])).
% 0.21/0.56  fof(f549,plain,(
% 0.21/0.56    m1_subset_1(sK4(sK1,sK2,sK0),u1_struct_0(sK1)) | spl5_1),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f57,f59,f60,f101,f89])).
% 0.21/0.56  fof(f552,plain,(
% 0.21/0.56    m1_subset_1(sK4(sK1,sK2,sK0),u1_struct_0(k3_lattice3(sK1))) | spl5_1),
% 0.21/0.56    inference(backward_demodulation,[],[f546,f545])).
% 0.21/0.56  fof(f546,plain,(
% 0.21/0.56    m1_subset_1(k4_lattice3(sK1,sK4(sK1,sK2,sK0)),u1_struct_0(k3_lattice3(sK1))) | spl5_1),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f60,f101,f198])).
% 0.21/0.56  fof(f198,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(k4_lattice3(sK1,sK4(sK1,X0,X1)),u1_struct_0(k3_lattice3(sK1))) | r4_lattice3(sK1,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK1))) )),
% 0.21/0.56    inference(resolution,[],[f166,f138])).
% 0.21/0.56  fof(f138,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | m1_subset_1(k4_lattice3(sK1,X0),u1_struct_0(k3_lattice3(sK1)))) )),
% 0.21/0.56    inference(global_subsumption,[],[f59,f57,f136])).
% 0.21/0.56  fof(f136,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK1)) | ~l3_lattices(sK1) | m1_subset_1(k4_lattice3(sK1,X0),u1_struct_0(k3_lattice3(sK1))) | v2_struct_0(sK1)) )),
% 0.21/0.56    inference(resolution,[],[f92,f58])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f33])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,axiom,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattice3(X0,X1),u1_struct_0(k3_lattice3(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_lattice3)).
% 0.21/0.56  fof(f137,plain,(
% 0.21/0.56    m1_subset_1(sK2,u1_struct_0(k3_lattice3(sK1)))),
% 0.21/0.56    inference(forward_demodulation,[],[f135,f120])).
% 0.21/0.56  fof(f135,plain,(
% 0.21/0.56    m1_subset_1(k4_lattice3(sK1,sK2),u1_struct_0(k3_lattice3(sK1)))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f57,f58,f59,f60,f92])).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    l1_orders_2(k3_lattice3(sK1))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f57,f58,f59,f83])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ( ! [X0] : (l1_orders_2(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X0] : ((l1_orders_2(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f23])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0] : ((l1_orders_2(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (l1_orders_2(k3_lattice3(X0)) & v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_lattice3)).
% 0.21/0.56  fof(f116,plain,(
% 0.21/0.56    v3_orders_2(k3_lattice3(sK1))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f57,f58,f59,f76])).
% 0.21/0.56  fof(f76,plain,(
% 0.21/0.56    ( ! [X0] : (v3_orders_2(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0] : ((v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0] : ((v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f11])).
% 0.21/0.56  fof(f11,axiom,(
% 0.21/0.56    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (v5_orders_2(k3_lattice3(X0)) & v4_orders_2(k3_lattice3(X0)) & v3_orders_2(k3_lattice3(X0)) & v1_orders_2(k3_lattice3(X0)) & ~v2_struct_0(k3_lattice3(X0))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_lattice3)).
% 0.21/0.56  fof(f114,plain,(
% 0.21/0.56    ~v2_struct_0(k3_lattice3(sK1))),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f57,f58,f59,f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X0] : (~v2_struct_0(k3_lattice3(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f22])).
% 0.21/0.56  fof(f579,plain,(
% 0.21/0.56    r1_orders_2(k3_lattice3(sK1),sK4(sK1,sK2,sK0),sK2) | (spl5_1 | ~spl5_2)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f119,f137,f542,f550,f552,f63])).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X1] : (~l1_orders_2(X0) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_orders_2(X0,X4,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f49])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f47,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ! [X2,X1,X0] : (? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_orders_2(X0,sK3(X0,X1,X2),X2) & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_orders_2(X0,X4,X2) | ~r2_hidden(X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(rectify,[],[f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : (((r2_lattice3(X0,X1,X2) | ? [X3] : (~r1_orders_2(X0,X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r2_lattice3(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : (r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(flattening,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : (! [X1,X2] : ((r2_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_orders_2(X0,X3,X2) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0] : (l1_orders_2(X0) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X1) => r1_orders_2(X0,X3,X2))))))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattice3)).
% 0.21/0.56  fof(f550,plain,(
% 0.21/0.56    r2_hidden(sK4(sK1,sK2,sK0),sK0) | spl5_1),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f57,f59,f60,f101,f90])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f54])).
% 0.21/0.56  fof(f542,plain,(
% 0.21/0.56    r2_lattice3(k3_lattice3(sK1),sK0,sK2) | ~spl5_2),
% 0.21/0.56    inference(forward_demodulation,[],[f104,f120])).
% 0.21/0.56  fof(f104,plain,(
% 0.21/0.56    r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2)) | ~spl5_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f103])).
% 0.21/0.56  fof(f103,plain,(
% 0.21/0.56    spl5_2 <=> r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.56  fof(f536,plain,(
% 0.21/0.56    ~spl5_1 | spl5_2),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f535])).
% 0.21/0.56  fof(f535,plain,(
% 0.21/0.56    $false | (~spl5_1 | spl5_2)),
% 0.21/0.56    inference(subsumption_resolution,[],[f524,f531])).
% 0.21/0.56  fof(f531,plain,(
% 0.21/0.56    ~r3_orders_2(k3_lattice3(sK1),sK3(k3_lattice3(sK1),sK0,sK2),sK2) | spl5_2),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f114,f116,f119,f137,f488,f489,f96])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f56])).
% 0.21/0.56  fof(f489,plain,(
% 0.21/0.56    m1_subset_1(sK3(k3_lattice3(sK1),sK0,sK2),u1_struct_0(k3_lattice3(sK1))) | spl5_2),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f119,f137,f459,f64])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | r2_lattice3(X0,X1,X2) | ~l1_orders_2(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f49])).
% 0.21/0.56  fof(f459,plain,(
% 0.21/0.56    ~r2_lattice3(k3_lattice3(sK1),sK0,sK2) | spl5_2),
% 0.21/0.56    inference(forward_demodulation,[],[f105,f120])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    ~r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2)) | spl5_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f103])).
% 0.21/0.56  fof(f488,plain,(
% 0.21/0.56    ~r1_orders_2(k3_lattice3(sK1),sK3(k3_lattice3(sK1),sK0,sK2),sK2) | spl5_2),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f119,f137,f459,f66])).
% 0.21/0.56  fof(f66,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_orders_2(X0,sK3(X0,X1,X2),X2) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f49])).
% 0.21/0.56  fof(f524,plain,(
% 0.21/0.56    r3_orders_2(k3_lattice3(sK1),sK3(k3_lattice3(sK1),sK0,sK2),sK2) | (~spl5_1 | spl5_2)),
% 0.21/0.56    inference(forward_demodulation,[],[f523,f499])).
% 0.21/0.56  fof(f499,plain,(
% 0.21/0.56    sK3(k3_lattice3(sK1),sK0,sK2) = k4_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2)) | spl5_2),
% 0.21/0.56    inference(backward_demodulation,[],[f485,f483])).
% 0.21/0.56  fof(f483,plain,(
% 0.21/0.56    sK3(k3_lattice3(sK1),sK0,sK2) = k5_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2)) | spl5_2),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f459,f158])).
% 0.21/0.56  fof(f158,plain,(
% 0.21/0.56    ( ! [X1] : (r2_lattice3(k3_lattice3(sK1),X1,sK2) | sK3(k3_lattice3(sK1),X1,sK2) = k5_lattice3(sK1,sK3(k3_lattice3(sK1),X1,sK2))) )),
% 0.21/0.56    inference(global_subsumption,[],[f59,f58,f57,f156])).
% 0.21/0.56  fof(f156,plain,(
% 0.21/0.56    ( ! [X1] : (r2_lattice3(k3_lattice3(sK1),X1,sK2) | sK3(k3_lattice3(sK1),X1,sK2) = k5_lattice3(sK1,sK3(k3_lattice3(sK1),X1,sK2)) | ~l3_lattices(sK1) | ~v10_lattices(sK1) | v2_struct_0(sK1)) )),
% 0.21/0.56    inference(resolution,[],[f142,f87])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) | k5_lattice3(X0,X1) = X1 | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f30])).
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k5_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k5_lattice3(X0,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0)))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) => k5_lattice3(X0,X1) = X1))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_lattice3)).
% 0.21/0.56  fof(f142,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(sK3(k3_lattice3(sK1),X0,sK2),u1_struct_0(k3_lattice3(sK1))) | r2_lattice3(k3_lattice3(sK1),X0,sK2)) )),
% 0.21/0.56    inference(global_subsumption,[],[f119,f141])).
% 0.21/0.56  fof(f141,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(sK3(k3_lattice3(sK1),X0,sK2),u1_struct_0(k3_lattice3(sK1))) | r2_lattice3(k3_lattice3(sK1),X0,sK2) | ~l1_orders_2(k3_lattice3(sK1))) )),
% 0.21/0.56    inference(resolution,[],[f137,f64])).
% 0.21/0.56  fof(f485,plain,(
% 0.21/0.56    k5_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2)) = k4_lattice3(sK1,k5_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2))) | spl5_2),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f459,f161])).
% 0.21/0.56  fof(f161,plain,(
% 0.21/0.56    ( ! [X1] : (r2_lattice3(k3_lattice3(sK1),X1,sK2) | k5_lattice3(sK1,sK3(k3_lattice3(sK1),X1,sK2)) = k4_lattice3(sK1,k5_lattice3(sK1,sK3(k3_lattice3(sK1),X1,sK2)))) )),
% 0.21/0.56    inference(resolution,[],[f155,f123])).
% 0.21/0.56  fof(f155,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k5_lattice3(sK1,sK3(k3_lattice3(sK1),X0,sK2)),u1_struct_0(sK1)) | r2_lattice3(k3_lattice3(sK1),X0,sK2)) )),
% 0.21/0.56    inference(resolution,[],[f142,f150])).
% 0.21/0.56  fof(f150,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(k3_lattice3(sK1))) | m1_subset_1(k5_lattice3(sK1,X0),u1_struct_0(sK1))) )),
% 0.21/0.56    inference(global_subsumption,[],[f59,f57,f148])).
% 0.21/0.56  fof(f148,plain,(
% 0.21/0.56    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(k3_lattice3(sK1))) | ~l3_lattices(sK1) | m1_subset_1(k5_lattice3(sK1,X0),u1_struct_0(sK1)) | v2_struct_0(sK1)) )),
% 0.21/0.56    inference(resolution,[],[f93,f58])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) | ~l3_lattices(X0) | m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0,X1] : (m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)) | (~m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,axiom,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(k3_lattice3(X0))) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattice3)).
% 0.21/0.56  fof(f523,plain,(
% 0.21/0.56    r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2)),sK2) | (~spl5_1 | spl5_2)),
% 0.21/0.56    inference(forward_demodulation,[],[f521,f120])).
% 0.21/0.56  fof(f521,plain,(
% 0.21/0.56    r3_orders_2(k3_lattice3(sK1),k4_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2)),k4_lattice3(sK1,sK2)) | (~spl5_1 | spl5_2)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f57,f58,f59,f501,f517,f60,f85])).
% 0.21/0.56  fof(f85,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_orders_2(k3_lattice3(X0),k4_lattice3(X0,X1),k4_lattice3(X0,X2)) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f50])).
% 0.21/0.56  fof(f517,plain,(
% 0.21/0.56    r3_lattices(sK1,sK3(k3_lattice3(sK1),sK0,sK2),sK2) | (~spl5_1 | spl5_2)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f57,f110,f112,f113,f59,f60,f501,f509,f95])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f55])).
% 0.21/0.56  fof(f509,plain,(
% 0.21/0.56    r1_lattices(sK1,sK3(k3_lattice3(sK1),sK0,sK2),sK2) | (~spl5_1 | spl5_2)),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f57,f59,f60,f100,f490,f501,f88])).
% 0.21/0.56  fof(f88,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X1] : (~l3_lattices(X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattices(X0,X4,X1) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f54])).
% 0.21/0.56  fof(f490,plain,(
% 0.21/0.56    r2_hidden(sK3(k3_lattice3(sK1),sK0,sK2),sK0) | spl5_2),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f119,f137,f459,f65])).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | r2_lattice3(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f49])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    r4_lattice3(sK1,sK2,sK0) | ~spl5_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f99])).
% 0.21/0.56  fof(f501,plain,(
% 0.21/0.56    m1_subset_1(sK3(k3_lattice3(sK1),sK0,sK2),u1_struct_0(sK1)) | spl5_2),
% 0.21/0.56    inference(forward_demodulation,[],[f498,f483])).
% 0.21/0.56  fof(f498,plain,(
% 0.21/0.56    m1_subset_1(k5_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2)),u1_struct_0(sK1)) | spl5_2),
% 0.21/0.56    inference(backward_demodulation,[],[f493,f483])).
% 0.21/0.56  fof(f493,plain,(
% 0.21/0.56    m1_subset_1(k5_lattice3(sK1,k5_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2))),u1_struct_0(sK1)) | spl5_2),
% 0.21/0.56    inference(backward_demodulation,[],[f486,f485])).
% 0.21/0.56  fof(f486,plain,(
% 0.21/0.56    m1_subset_1(k5_lattice3(sK1,k4_lattice3(sK1,k5_lattice3(sK1,sK3(k3_lattice3(sK1),sK0,sK2)))),u1_struct_0(sK1)) | spl5_2),
% 0.21/0.56    inference(unit_resulting_resolution,[],[f459,f209])).
% 0.21/0.56  fof(f209,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k5_lattice3(sK1,k4_lattice3(sK1,k5_lattice3(sK1,sK3(k3_lattice3(sK1),X0,sK2)))),u1_struct_0(sK1)) | r2_lattice3(k3_lattice3(sK1),X0,sK2)) )),
% 0.21/0.56    inference(resolution,[],[f160,f150])).
% 0.21/0.56  fof(f160,plain,(
% 0.21/0.56    ( ! [X0] : (m1_subset_1(k4_lattice3(sK1,k5_lattice3(sK1,sK3(k3_lattice3(sK1),X0,sK2))),u1_struct_0(k3_lattice3(sK1))) | r2_lattice3(k3_lattice3(sK1),X0,sK2)) )),
% 0.21/0.56    inference(resolution,[],[f155,f138])).
% 0.21/0.56  fof(f107,plain,(
% 0.21/0.56    spl5_1 | spl5_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f61,f103,f99])).
% 0.21/0.56  fof(f61,plain,(
% 0.21/0.56    r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2)) | r4_lattice3(sK1,sK2,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  fof(f106,plain,(
% 0.21/0.56    ~spl5_1 | ~spl5_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f62,f103,f99])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ~r2_lattice3(k3_lattice3(sK1),sK0,k4_lattice3(sK1,sK2)) | ~r4_lattice3(sK1,sK2,sK0)),
% 0.21/0.56    inference(cnf_transformation,[],[f45])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (30133)------------------------------
% 0.21/0.56  % (30133)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (30133)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (30133)Memory used [KB]: 11001
% 0.21/0.56  % (30133)Time elapsed: 0.098 s
% 0.21/0.56  % (30133)------------------------------
% 0.21/0.56  % (30133)------------------------------
% 0.21/0.57  % (30115)Success in time 0.21 s
%------------------------------------------------------------------------------
