%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 375 expanded)
%              Number of leaves         :   15 ( 133 expanded)
%              Depth                    :   23
%              Number of atoms          :  591 (2675 expanded)
%              Number of equality atoms :   35 ( 322 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(global_subsumption,[],[f51,f163])).

fof(f163,plain,(
    ~ r2_hidden(sK4,sK5) ),
    inference(resolution,[],[f162,f99])).

fof(f99,plain,(
    ! [X0] :
      ( r3_lattices(sK3,sK4,k15_lattice3(sK3,X0))
      | ~ r2_hidden(sK4,X0) ) ),
    inference(resolution,[],[f98,f50])).

fof(f50,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK4 != k15_lattice3(sK3,sK5)
    & r4_lattice3(sK3,sK4,sK5)
    & r2_hidden(sK4,sK5)
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l3_lattices(sK3)
    & v4_lattice3(sK3)
    & v10_lattices(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f14,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k15_lattice3(X0,X2) != X1
                & r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k15_lattice3(sK3,X2) != X1
              & r4_lattice3(sK3,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l3_lattices(sK3)
      & v4_lattice3(sK3)
      & v10_lattices(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k15_lattice3(sK3,X2) != X1
            & r4_lattice3(sK3,X1,X2)
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK3)) )
   => ( ? [X2] :
          ( k15_lattice3(sK3,X2) != sK4
          & r4_lattice3(sK3,sK4,X2)
          & r2_hidden(sK4,X2) )
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( k15_lattice3(sK3,X2) != sK4
        & r4_lattice3(sK3,sK4,X2)
        & r2_hidden(sK4,X2) )
   => ( sK4 != k15_lattice3(sK3,sK5)
      & r4_lattice3(sK3,sK4,sK5)
      & r2_hidden(sK4,sK5) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k15_lattice3(X0,X2) != X1
              & r4_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k15_lattice3(X0,X2) != X1
              & r4_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( ( r4_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k15_lattice3(X0,X2) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k15_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).

fof(f98,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ r2_hidden(X0,X1)
      | r3_lattices(sK3,X0,k15_lattice3(sK3,X1)) ) ),
    inference(global_subsumption,[],[f49,f47,f46,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | r3_lattices(sK3,X0,k15_lattice3(sK3,X1))
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f62,f48])).

fof(f48,plain,(
    v4_lattice3(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

fof(f46,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f47,plain,(
    v10_lattices(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f49,plain,(
    l3_lattices(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f162,plain,(
    ~ r3_lattices(sK3,sK4,k15_lattice3(sK3,sK5)) ),
    inference(global_subsumption,[],[f53,f160])).

fof(f160,plain,
    ( sK4 = k15_lattice3(sK3,sK5)
    | ~ r3_lattices(sK3,sK4,k15_lattice3(sK3,sK5)) ),
    inference(resolution,[],[f157,f95])).

fof(f95,plain,(
    r1_lattices(sK3,k15_lattice3(sK3,sK5),sK4) ),
    inference(resolution,[],[f93,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ sP1(X0,sK3,sK5)
      | r1_lattices(sK3,X0,sK4) ) ),
    inference(resolution,[],[f82,f52])).

fof(f52,plain,(
    r4_lattice3(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r4_lattice3(sK3,sK4,X0)
      | r1_lattices(sK3,X1,sK4)
      | ~ sP1(X1,sK3,X0) ) ),
    inference(resolution,[],[f67,f50])).

fof(f67,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ r4_lattice3(X1,X4,X2)
      | r1_lattices(X1,X0,X4)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK6(X0,X1,X2))
          & r4_lattice3(X1,sK6(X0,X1,X2),X2)
          & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) )
        | ~ r4_lattice3(X1,X0,X2) )
      & ( ( ! [X4] :
              ( r1_lattices(X1,X0,X4)
              | ~ r4_lattice3(X1,X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r4_lattice3(X1,X0,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r4_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK6(X0,X1,X2))
        & r4_lattice3(X1,sK6(X0,X1,X2),X2)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r4_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ r4_lattice3(X1,X0,X2) )
      & ( ( ! [X4] :
              ( r1_lattices(X1,X0,X4)
              | ~ r4_lattice3(X1,X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r4_lattice3(X1,X0,X2) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_lattices(X0,X2,X3)
            & r4_lattice3(X0,X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( ! [X3] :
              ( r1_lattices(X0,X2,X3)
              | ~ r4_lattice3(X0,X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r4_lattice3(X0,X2,X1) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_lattices(X0,X2,X3)
            & r4_lattice3(X0,X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( ! [X3] :
              ( r1_lattices(X0,X2,X3)
              | ~ r4_lattice3(X0,X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          & r4_lattice3(X0,X2,X1) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
    <=> ( ! [X3] :
            ( r1_lattices(X0,X2,X3)
            | ~ r4_lattice3(X0,X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        & r4_lattice3(X0,X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f93,plain,(
    ! [X0] : sP1(k15_lattice3(sK3,X0),sK3,X0) ),
    inference(resolution,[],[f91,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ sP2(X0,X1,k15_lattice3(X1,X0))
      | sP1(k15_lattice3(X1,X0),X1,X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | k15_lattice3(X1,X0) != X2
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( k15_lattice3(X1,X0) = X2
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | k15_lattice3(X1,X0) != X2 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X1,X0,X2] :
      ( ( ( k15_lattice3(X0,X1) = X2
          | ~ sP1(X2,X0,X1) )
        & ( sP1(X2,X0,X1)
          | k15_lattice3(X0,X1) != X2 ) )
      | ~ sP2(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( ( k15_lattice3(X0,X1) = X2
      <=> sP1(X2,X0,X1) )
      | ~ sP2(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f91,plain,(
    ! [X2,X1] : sP2(X1,sK3,k15_lattice3(sK3,X2)) ),
    inference(global_subsumption,[],[f49,f46,f89])).

fof(f89,plain,(
    ! [X2,X1] :
      ( sP2(X1,sK3,k15_lattice3(sK3,X2))
      | ~ l3_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f87,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | sP2(X1,sK3,X0) ) ),
    inference(global_subsumption,[],[f49,f47,f46,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | sP2(X1,sK3,X0)
      | ~ v10_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f76,f48])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | sP2(X1,X0,X2)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP2(X1,X0,X2)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f23,f31,f30])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k15_lattice3(X0,X1) = X2
          <=> ( ! [X3] :
                  ( r1_lattices(X0,X2,X3)
                  | ~ r4_lattice3(X0,X3,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              & r4_lattice3(X0,X2,X1) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,u1_struct_0(X0))
           => ( k15_lattice3(X0,X1) = X2
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r4_lattice3(X0,X3,X1)
                     => r1_lattices(X0,X2,X3) ) )
                & r4_lattice3(X0,X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).

fof(f157,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK3,k15_lattice3(sK3,X0),sK4)
      | sK4 = k15_lattice3(sK3,X0)
      | ~ r3_lattices(sK3,sK4,k15_lattice3(sK3,X0)) ) ),
    inference(resolution,[],[f153,f124])).

fof(f124,plain,(
    ! [X0] :
      ( ~ r1_lattices(sK3,sK4,k15_lattice3(sK3,X0))
      | sK4 = k15_lattice3(sK3,X0)
      | ~ r1_lattices(sK3,k15_lattice3(sK3,X0),sK4) ) ),
    inference(resolution,[],[f122,f50])).

fof(f122,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
      | k15_lattice3(sK3,X2) = X1
      | ~ r1_lattices(sK3,X1,k15_lattice3(sK3,X2))
      | ~ r1_lattices(sK3,k15_lattice3(sK3,X2),X1) ) ),
    inference(global_subsumption,[],[f49,f46,f120])).

fof(f120,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
      | k15_lattice3(sK3,X2) = X1
      | ~ r1_lattices(sK3,X1,k15_lattice3(sK3,X2))
      | ~ r1_lattices(sK3,k15_lattice3(sK3,X2),X1)
      | ~ l3_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f118,f72])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ m1_subset_1(X0,u1_struct_0(sK3))
      | X0 = X1
      | ~ r1_lattices(sK3,X0,X1)
      | ~ r1_lattices(sK3,X1,X0) ) ),
    inference(global_subsumption,[],[f49,f46,f117])).

fof(f117,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK3))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | X0 = X1
      | ~ r1_lattices(sK3,X0,X1)
      | v2_struct_0(sK3)
      | ~ l3_lattices(sK3)
      | ~ r1_lattices(sK3,X1,X0) ) ),
    inference(resolution,[],[f116,f47])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | X1 = X2
      | ~ r1_lattices(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ r1_lattices(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | X1 = X2
      | ~ r1_lattices(X0,X2,X1)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0) ) ),
    inference(resolution,[],[f114,f80])).

fof(f80,plain,(
    ! [X3] :
      ( v4_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3) ) ),
    inference(resolution,[],[f60,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f60,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f17,f28])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X0)
      | ~ r1_lattices(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f61,f54])).

fof(f54,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l2_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ r1_lattices(X0,X2,X1)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | X1 = X2
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

fof(f153,plain,(
    ! [X0] :
      ( r1_lattices(sK3,sK4,k15_lattice3(sK3,X0))
      | ~ r3_lattices(sK3,sK4,k15_lattice3(sK3,X0)) ) ),
    inference(resolution,[],[f150,f50])).

fof(f150,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
      | r1_lattices(sK3,X1,k15_lattice3(sK3,X2))
      | ~ r3_lattices(sK3,X1,k15_lattice3(sK3,X2)) ) ),
    inference(global_subsumption,[],[f49,f46,f148])).

fof(f148,plain,(
    ! [X2,X1] :
      ( ~ r3_lattices(sK3,X1,k15_lattice3(sK3,X2))
      | r1_lattices(sK3,X1,k15_lattice3(sK3,X2))
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ l3_lattices(sK3)
      | v2_struct_0(sK3) ) ),
    inference(resolution,[],[f146,f72])).

fof(f146,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(sK3))
      | ~ r3_lattices(sK3,X0,X1)
      | r1_lattices(sK3,X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(global_subsumption,[],[f49,f46,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(sK3)
      | r1_lattices(sK3,X0,X1)
      | ~ r3_lattices(sK3,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(sK3))
      | v2_struct_0(sK3)
      | ~ m1_subset_1(X0,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f142,f47])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X0,X2)
      | ~ r3_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X0,X2)
      | ~ r3_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1) ) ),
    inference(resolution,[],[f140,f79])).

fof(f79,plain,(
    ! [X2] :
      ( v6_lattices(X2)
      | v2_struct_0(X2)
      | ~ l3_lattices(X2)
      | ~ v10_lattices(X2) ) ),
    inference(resolution,[],[f60,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X2,X0)
      | ~ r3_lattices(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ v10_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X2,X0)
      | ~ r3_lattices(X1,X2,X0)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1) ) ),
    inference(resolution,[],[f131,f78])).

fof(f78,plain,(
    ! [X1] :
      ( v8_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1) ) ),
    inference(resolution,[],[f60,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0) ) ),
    inference(resolution,[],[f73,f77])).

fof(f77,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0) ) ),
    inference(resolution,[],[f60,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f53,plain,(
    sK4 != k15_lattice3(sK3,sK5) ),
    inference(cnf_transformation,[],[f36])).

fof(f51,plain,(
    r2_hidden(sK4,sK5) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:12:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (14646)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.46  % (14654)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.47  % (14646)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(global_subsumption,[],[f51,f163])).
% 0.20/0.48  fof(f163,plain,(
% 0.20/0.48    ~r2_hidden(sK4,sK5)),
% 0.20/0.48    inference(resolution,[],[f162,f99])).
% 0.20/0.48  fof(f99,plain,(
% 0.20/0.48    ( ! [X0] : (r3_lattices(sK3,sK4,k15_lattice3(sK3,X0)) | ~r2_hidden(sK4,X0)) )),
% 0.20/0.48    inference(resolution,[],[f98,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ((sK4 != k15_lattice3(sK3,sK5) & r4_lattice3(sK3,sK4,sK5) & r2_hidden(sK4,sK5)) & m1_subset_1(sK4,u1_struct_0(sK3))) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3)),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f14,f35,f34,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (k15_lattice3(X0,X2) != X1 & r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k15_lattice3(sK3,X2) != X1 & r4_lattice3(sK3,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK3))) & l3_lattices(sK3) & v4_lattice3(sK3) & v10_lattices(sK3) & ~v2_struct_0(sK3))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ? [X1] : (? [X2] : (k15_lattice3(sK3,X2) != X1 & r4_lattice3(sK3,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK3))) => (? [X2] : (k15_lattice3(sK3,X2) != sK4 & r4_lattice3(sK3,sK4,X2) & r2_hidden(sK4,X2)) & m1_subset_1(sK4,u1_struct_0(sK3)))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ? [X2] : (k15_lattice3(sK3,X2) != sK4 & r4_lattice3(sK3,sK4,X2) & r2_hidden(sK4,X2)) => (sK4 != k15_lattice3(sK3,sK5) & r4_lattice3(sK3,sK4,sK5) & r2_hidden(sK4,sK5))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (k15_lattice3(X0,X2) != X1 & r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : (? [X2] : (k15_lattice3(X0,X2) != X1 & (r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 0.20/0.48    inference(negated_conjecture,[],[f8])).
% 0.20/0.48  fof(f8,conjecture,(
% 0.20/0.48    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~r2_hidden(X0,X1) | r3_lattices(sK3,X0,k15_lattice3(sK3,X1))) )),
% 0.20/0.48    inference(global_subsumption,[],[f49,f47,f46,f97])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK3)) | ~l3_lattices(sK3) | r3_lattices(sK3,X0,k15_lattice3(sK3,X1)) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.48    inference(resolution,[],[f62,f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    v4_lattice3(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r3_lattices(X0,X1,k15_lattice3(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ~v2_struct_0(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    v10_lattices(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    l3_lattices(sK3)),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f162,plain,(
% 0.20/0.48    ~r3_lattices(sK3,sK4,k15_lattice3(sK3,sK5))),
% 0.20/0.48    inference(global_subsumption,[],[f53,f160])).
% 0.20/0.48  fof(f160,plain,(
% 0.20/0.48    sK4 = k15_lattice3(sK3,sK5) | ~r3_lattices(sK3,sK4,k15_lattice3(sK3,sK5))),
% 0.20/0.48    inference(resolution,[],[f157,f95])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    r1_lattices(sK3,k15_lattice3(sK3,sK5),sK4)),
% 0.20/0.48    inference(resolution,[],[f93,f85])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    ( ! [X0] : (~sP1(X0,sK3,sK5) | r1_lattices(sK3,X0,sK4)) )),
% 0.20/0.48    inference(resolution,[],[f82,f52])).
% 0.20/0.48  fof(f52,plain,(
% 0.20/0.48    r4_lattice3(sK3,sK4,sK5)),
% 0.20/0.48    inference(cnf_transformation,[],[f36])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r4_lattice3(sK3,sK4,X0) | r1_lattices(sK3,X1,sK4) | ~sP1(X1,sK3,X0)) )),
% 0.20/0.48    inference(resolution,[],[f67,f50])).
% 0.20/0.48  fof(f67,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X1] : (~m1_subset_1(X4,u1_struct_0(X1)) | ~r4_lattice3(X1,X4,X2) | r1_lattices(X1,X0,X4) | ~sP1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f44])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (~r1_lattices(X1,X0,sK6(X0,X1,X2)) & r4_lattice3(X1,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))) | ~r4_lattice3(X1,X0,X2)) & ((! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & r4_lattice3(X1,X0,X2)) | ~sP1(X0,X1,X2)))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f42,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK6(X0,X1,X2)) & r4_lattice3(X1,sK6(X0,X1,X2),X2) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) | ~r4_lattice3(X1,X0,X2)) & ((! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & r4_lattice3(X1,X0,X2)) | ~sP1(X0,X1,X2)))),
% 0.20/0.48    inference(rectify,[],[f41])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | ~sP1(X2,X0,X1)))),
% 0.20/0.48    inference(flattening,[],[f40])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | ~sP1(X2,X0,X1)))),
% 0.20/0.48    inference(nnf_transformation,[],[f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ! [X2,X0,X1] : (sP1(X2,X0,X1) <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ( ! [X0] : (sP1(k15_lattice3(sK3,X0),sK3,X0)) )),
% 0.20/0.48    inference(resolution,[],[f91,f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~sP2(X0,X1,k15_lattice3(X1,X0)) | sP1(k15_lattice3(X1,X0),X1,X0)) )),
% 0.20/0.48    inference(equality_resolution,[],[f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | k15_lattice3(X1,X0) != X2 | ~sP2(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f39])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (((k15_lattice3(X1,X0) = X2 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k15_lattice3(X1,X0) != X2)) | ~sP2(X0,X1,X2))),
% 0.20/0.48    inference(rectify,[],[f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ! [X1,X0,X2] : (((k15_lattice3(X0,X1) = X2 | ~sP1(X2,X0,X1)) & (sP1(X2,X0,X1) | k15_lattice3(X0,X1) != X2)) | ~sP2(X1,X0,X2))),
% 0.20/0.48    inference(nnf_transformation,[],[f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ! [X1,X0,X2] : ((k15_lattice3(X0,X1) = X2 <=> sP1(X2,X0,X1)) | ~sP2(X1,X0,X2))),
% 0.20/0.48    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    ( ! [X2,X1] : (sP2(X1,sK3,k15_lattice3(sK3,X2))) )),
% 0.20/0.48    inference(global_subsumption,[],[f49,f46,f89])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ( ! [X2,X1] : (sP2(X1,sK3,k15_lattice3(sK3,X2)) | ~l3_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.48    inference(resolution,[],[f87,f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | sP2(X1,sK3,X0)) )),
% 0.20/0.48    inference(global_subsumption,[],[f49,f47,f46,f86])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~l3_lattices(sK3) | sP2(X1,sK3,X0) | ~v10_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.48    inference(resolution,[],[f76,f48])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | sP2(X1,X0,X2) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f71])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ! [X0] : (! [X1,X2] : (sP2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(definition_folding,[],[f23,f31,f30])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 0.20/0.48  fof(f157,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_lattices(sK3,k15_lattice3(sK3,X0),sK4) | sK4 = k15_lattice3(sK3,X0) | ~r3_lattices(sK3,sK4,k15_lattice3(sK3,X0))) )),
% 0.20/0.48    inference(resolution,[],[f153,f124])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    ( ! [X0] : (~r1_lattices(sK3,sK4,k15_lattice3(sK3,X0)) | sK4 = k15_lattice3(sK3,X0) | ~r1_lattices(sK3,k15_lattice3(sK3,X0),sK4)) )),
% 0.20/0.48    inference(resolution,[],[f122,f50])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | k15_lattice3(sK3,X2) = X1 | ~r1_lattices(sK3,X1,k15_lattice3(sK3,X2)) | ~r1_lattices(sK3,k15_lattice3(sK3,X2),X1)) )),
% 0.20/0.48    inference(global_subsumption,[],[f49,f46,f120])).
% 0.20/0.48  fof(f120,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | k15_lattice3(sK3,X2) = X1 | ~r1_lattices(sK3,X1,k15_lattice3(sK3,X2)) | ~r1_lattices(sK3,k15_lattice3(sK3,X2),X1) | ~l3_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.48    inference(resolution,[],[f118,f72])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~m1_subset_1(X0,u1_struct_0(sK3)) | X0 = X1 | ~r1_lattices(sK3,X0,X1) | ~r1_lattices(sK3,X1,X0)) )),
% 0.20/0.49    inference(global_subsumption,[],[f49,f46,f117])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | X0 = X1 | ~r1_lattices(sK3,X0,X1) | v2_struct_0(sK3) | ~l3_lattices(sK3) | ~r1_lattices(sK3,X1,X0)) )),
% 0.20/0.49    inference(resolution,[],[f116,f47])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | X1 = X2 | ~r1_lattices(X0,X2,X1) | v2_struct_0(X0) | ~l3_lattices(X0) | ~r1_lattices(X0,X1,X2)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f115])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | X1 = X2 | ~r1_lattices(X0,X2,X1) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~v10_lattices(X0)) )),
% 0.20/0.49    inference(resolution,[],[f114,f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X3] : (v4_lattices(X3) | v2_struct_0(X3) | ~l3_lattices(X3) | ~v10_lattices(X3)) )),
% 0.20/0.49    inference(resolution,[],[f60,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X0] : (~sP0(X0) | v4_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 0.20/0.49    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.49    inference(definition_folding,[],[f17,f28])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.49    inference(flattening,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v4_lattices(X0) | ~r1_lattices(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | X1 = X2 | ~r1_lattices(X0,X1,X2) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.49    inference(resolution,[],[f61,f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : (l3_lattices(X0) => l2_lattices(X0))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l2_lattices(X0) | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | X1 = X2 | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    ( ! [X0] : (r1_lattices(sK3,sK4,k15_lattice3(sK3,X0)) | ~r3_lattices(sK3,sK4,k15_lattice3(sK3,X0))) )),
% 0.20/0.49    inference(resolution,[],[f150,f50])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | r1_lattices(sK3,X1,k15_lattice3(sK3,X2)) | ~r3_lattices(sK3,X1,k15_lattice3(sK3,X2))) )),
% 0.20/0.49    inference(global_subsumption,[],[f49,f46,f148])).
% 0.20/0.49  fof(f148,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~r3_lattices(sK3,X1,k15_lattice3(sK3,X2)) | r1_lattices(sK3,X1,k15_lattice3(sK3,X2)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~l3_lattices(sK3) | v2_struct_0(sK3)) )),
% 0.20/0.49    inference(resolution,[],[f146,f72])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK3)) | ~r3_lattices(sK3,X0,X1) | r1_lattices(sK3,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK3))) )),
% 0.20/0.49    inference(global_subsumption,[],[f49,f46,f145])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l3_lattices(sK3) | r1_lattices(sK3,X0,X1) | ~r3_lattices(sK3,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK3)) | v2_struct_0(sK3) | ~m1_subset_1(X0,u1_struct_0(sK3))) )),
% 0.20/0.49    inference(resolution,[],[f142,f47])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~l3_lattices(X1) | r1_lattices(X1,X0,X2) | ~r3_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f141])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X0,X2) | ~r3_lattices(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | v2_struct_0(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1)) )),
% 0.20/0.49    inference(resolution,[],[f140,f79])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    ( ! [X2] : (v6_lattices(X2) | v2_struct_0(X2) | ~l3_lattices(X2) | ~v10_lattices(X2)) )),
% 0.20/0.49    inference(resolution,[],[f60,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0] : (~sP0(X0) | v6_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v6_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X2,X0) | ~r3_lattices(X1,X2,X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | ~v10_lattices(X1)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f139])).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X2,X0) | ~r3_lattices(X1,X2,X0) | ~v6_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1)) )),
% 0.20/0.49    inference(resolution,[],[f131,f78])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    ( ! [X1] : (v8_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1)) )),
% 0.20/0.49    inference(resolution,[],[f60,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X0] : (~sP0(X0) | v8_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v8_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f130])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~v10_lattices(X0)) )),
% 0.20/0.49    inference(resolution,[],[f73,f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X0] : (v9_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~v10_lattices(X0)) )),
% 0.20/0.49    inference(resolution,[],[f60,f59])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ( ! [X0] : (~sP0(X0) | v9_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f37])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    sK4 != k15_lattice3(sK3,sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    r2_hidden(sK4,sK5)),
% 0.20/0.49    inference(cnf_transformation,[],[f36])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (14646)------------------------------
% 0.20/0.49  % (14646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (14646)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (14646)Memory used [KB]: 6396
% 0.20/0.49  % (14646)Time elapsed: 0.054 s
% 0.20/0.49  % (14646)------------------------------
% 0.20/0.49  % (14646)------------------------------
% 0.20/0.49  % (14633)Success in time 0.127 s
%------------------------------------------------------------------------------
