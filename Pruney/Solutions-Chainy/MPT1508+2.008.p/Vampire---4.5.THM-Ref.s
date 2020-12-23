%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:43 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  210 ( 550 expanded)
%              Number of leaves         :   31 ( 188 expanded)
%              Depth                    :   39
%              Number of atoms          : 1047 (3478 expanded)
%              Number of equality atoms :   77 ( 399 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f807,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f750,f754,f758,f800])).

fof(f800,plain,(
    ~ spl20_1 ),
    inference(avatar_contradiction_clause,[],[f799])).

fof(f799,plain,
    ( $false
    | ~ spl20_1 ),
    inference(subsumption_resolution,[],[f798,f85])).

fof(f85,plain,(
    r2_hidden(sK13,sK14) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,
    ( sK13 != k16_lattice3(sK12,sK14)
    & r3_lattice3(sK12,sK13,sK14)
    & r2_hidden(sK13,sK14)
    & m1_subset_1(sK13,u1_struct_0(sK12))
    & l3_lattices(sK12)
    & v4_lattice3(sK12)
    & v10_lattices(sK12)
    & ~ v2_struct_0(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f11,f45,f44,f43])).

fof(f43,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k16_lattice3(X0,X2) != X1
                & r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(sK12,X2) != X1
              & r3_lattice3(sK12,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK12)) )
      & l3_lattices(sK12)
      & v4_lattice3(sK12)
      & v10_lattices(sK12)
      & ~ v2_struct_0(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k16_lattice3(sK12,X2) != X1
            & r3_lattice3(sK12,X1,X2)
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK12)) )
   => ( ? [X2] :
          ( k16_lattice3(sK12,X2) != sK13
          & r3_lattice3(sK12,sK13,X2)
          & r2_hidden(sK13,X2) )
      & m1_subset_1(sK13,u1_struct_0(sK12)) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X2] :
        ( k16_lattice3(sK12,X2) != sK13
        & r3_lattice3(sK12,sK13,X2)
        & r2_hidden(sK13,X2) )
   => ( sK13 != k16_lattice3(sK12,sK14)
      & r3_lattice3(sK12,sK13,sK14)
      & r2_hidden(sK13,sK14) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) != X1
              & r3_lattice3(X0,X1,X2)
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
                ( ( r3_lattice3(X0,X1,X2)
                  & r2_hidden(X1,X2) )
               => k16_lattice3(X0,X2) = X1 ) ) ) ),
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
              ( ( r3_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k16_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).

fof(f798,plain,
    ( ~ r2_hidden(sK13,sK14)
    | ~ spl20_1 ),
    inference(subsumption_resolution,[],[f796,f84])).

fof(f84,plain,(
    m1_subset_1(sK13,u1_struct_0(sK12)) ),
    inference(cnf_transformation,[],[f46])).

fof(f796,plain,
    ( ~ m1_subset_1(sK13,u1_struct_0(sK12))
    | ~ r2_hidden(sK13,sK14)
    | ~ spl20_1 ),
    inference(trivial_inequality_removal,[],[f793])).

fof(f793,plain,
    ( ~ m1_subset_1(sK13,u1_struct_0(sK12))
    | sK13 != sK13
    | ~ r2_hidden(sK13,sK14)
    | ~ spl20_1 ),
    inference(resolution,[],[f739,f732])).

fof(f732,plain,
    ( r2_hidden(sK13,a_2_1_lattice3(sK12,sK14))
    | ~ spl20_1 ),
    inference(avatar_component_clause,[],[f731])).

fof(f731,plain,
    ( spl20_1
  <=> r2_hidden(sK13,a_2_1_lattice3(sK12,sK14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_1])])).

fof(f739,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,a_2_1_lattice3(sK12,sK14))
      | ~ m1_subset_1(X1,u1_struct_0(sK12))
      | sK13 != X1
      | ~ r2_hidden(X1,sK14) ) ),
    inference(subsumption_resolution,[],[f738,f80])).

fof(f80,plain,(
    ~ v2_struct_0(sK12) ),
    inference(cnf_transformation,[],[f46])).

fof(f738,plain,(
    ! [X1] :
      ( sK13 != X1
      | ~ m1_subset_1(X1,u1_struct_0(sK12))
      | ~ r2_hidden(X1,a_2_1_lattice3(sK12,sK14))
      | ~ r2_hidden(X1,sK14)
      | v2_struct_0(sK12) ) ),
    inference(subsumption_resolution,[],[f727,f83])).

fof(f83,plain,(
    l3_lattices(sK12) ),
    inference(cnf_transformation,[],[f46])).

fof(f727,plain,(
    ! [X1] :
      ( sK13 != X1
      | ~ m1_subset_1(X1,u1_struct_0(sK12))
      | ~ r2_hidden(X1,a_2_1_lattice3(sK12,sK14))
      | ~ r2_hidden(X1,sK14)
      | ~ l3_lattices(sK12)
      | v2_struct_0(sK12) ) ),
    inference(duplicate_literal_removal,[],[f726])).

fof(f726,plain,(
    ! [X1] :
      ( sK13 != X1
      | ~ m1_subset_1(X1,u1_struct_0(sK12))
      | ~ r2_hidden(X1,a_2_1_lattice3(sK12,sK14))
      | ~ r2_hidden(X1,sK14)
      | ~ l3_lattices(sK12)
      | v2_struct_0(sK12)
      | ~ m1_subset_1(X1,u1_struct_0(sK12)) ) ),
    inference(resolution,[],[f723,f352])).

fof(f352,plain,(
    ! [X6,X4,X5] :
      ( r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | ~ m1_subset_1(X4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f351,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP7(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP7(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f35,f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( sP6(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP6(X1,X0,X2) )
      | ~ sP7(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

fof(f351,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6))
      | ~ sP7(X5,X4) ) ),
    inference(resolution,[],[f349,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP7(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP6(X1,X0,X2) )
          & ( sP6(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP7(X0,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f349,plain,(
    ! [X2,X0,X1] :
      ( sP6(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f348,f153])).

fof(f153,plain,(
    ! [X10,X8,X9] :
      ( sP9(X8,sK17(X9,X8,X10))
      | ~ l3_lattices(X8)
      | v2_struct_0(X8)
      | sP6(X9,X8,X10) ) ),
    inference(resolution,[],[f123,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))
      | sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( sP6(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK17(X0,X1,X2),X0)
          & r2_hidden(sK17(X0,X1,X2),X2)
          & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP6(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK17(X0,X1,X2),X0)
        & r2_hidden(sK17(X0,X1,X2),X2)
        & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( sP6(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP6(X0,X1,X2) ) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X1,X0,X2] :
      ( ( sP6(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X3,X1)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X3,X1)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP6(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP9(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP9(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f38,f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( sP8(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP8(X1,X0,X2) )
      | ~ sP9(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( r1_lattices(X0,X1,X3)
                  | ~ r2_hidden(X3,X2)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r3_lattice3(X0,X1,X2)
            <=> ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X3,X2)
                   => r1_lattices(X0,X1,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

fof(f348,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ sP9(X2,sK17(X0,X2,a_2_1_lattice3(X2,X1)))
      | sP6(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f347])).

fof(f347,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ sP9(X2,sK17(X0,X2,a_2_1_lattice3(X2,X1)))
      | sP6(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP6(X0,X2,a_2_1_lattice3(X2,X1)) ) ),
    inference(resolution,[],[f246,f295])).

fof(f295,plain,(
    ! [X14,X12,X15,X13] :
      ( r3_lattice3(X14,sK17(X12,X13,a_2_1_lattice3(X14,X15)),X15)
      | ~ l3_lattices(X14)
      | v2_struct_0(X14)
      | sP6(X12,X13,a_2_1_lattice3(X14,X15)) ) ),
    inference(resolution,[],[f291,f163])).

fof(f163,plain,(
    ! [X2,X0,X1] :
      ( ~ sP10(X0,X1,X2)
      | r3_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,X2,X0)
      | ~ sP10(X0,X1,X2)
      | ~ sP10(X0,X1,X2) ) ),
    inference(superposition,[],[f129,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( sK19(X0,X1,X2) = X2
      | ~ sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( ( sP10(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r3_lattice3(X1,sK19(X0,X1,X2),X0)
          & sK19(X0,X1,X2) = X2
          & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP10(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f77,f78])).

fof(f78,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK19(X0,X1,X2),X0)
        & sK19(X0,X1,X2) = X2
        & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( sP10(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattice3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP10(X0,X1,X2) ) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X2,X1,X0] :
      ( ( sP10(X2,X1,X0)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP10(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( sP10(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK19(X0,X1,X2),X0)
      | ~ sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f291,plain,(
    ! [X2,X0,X3,X1] :
      ( sP10(X0,X1,sK17(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP6(X2,X3,a_2_1_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f191,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( sP11(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( sP11(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f25,f41,f40])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> sP10(X2,X1,X0) )
      | ~ sP11(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

fof(f191,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP11(sK17(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0)
      | sP10(X0,X1,sK17(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP6(X2,X3,a_2_1_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f125,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK17(X0,X1,X2),X2)
      | sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | sP10(X2,X1,X0)
      | ~ sP11(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ~ sP10(X2,X1,X0) )
        & ( sP10(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ sP11(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f246,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r3_lattice3(X9,sK17(X8,X9,X11),X10)
      | ~ r2_hidden(X8,X10)
      | ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ sP9(X9,sK17(X8,X9,X11))
      | sP6(X8,X9,X11) ) ),
    inference(resolution,[],[f215,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK17(X0,X1,X2),X0)
      | sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f215,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X2,X3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ r3_lattice3(X2,X3,X1)
      | ~ sP9(X2,X3) ) ),
    inference(resolution,[],[f119,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( sP8(X1,X0,X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP9(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP8(X1,X0,X2) )
          & ( sP8(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP9(X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f119,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP8(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( sP8(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK18(X0,X1,X2))
          & r2_hidden(sK18(X0,X1,X2),X2)
          & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP8(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f72,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK18(X0,X1,X2))
        & r2_hidden(sK18(X0,X1,X2),X2)
        & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( sP8(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP8(X0,X1,X2) ) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X1,X0,X2] :
      ( ( sP8(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X1,X3)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP8(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f723,plain,(
    ! [X0] :
      ( ~ r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14))
      | sK13 != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK12))
      | ~ r2_hidden(X0,a_2_1_lattice3(sK12,sK14)) ) ),
    inference(subsumption_resolution,[],[f722,f80])).

fof(f722,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK12))
      | sK13 != X0
      | ~ r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14))
      | ~ r2_hidden(X0,a_2_1_lattice3(sK12,sK14))
      | v2_struct_0(sK12) ) ),
    inference(subsumption_resolution,[],[f721,f83])).

fof(f721,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK12))
      | sK13 != X0
      | ~ r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14))
      | ~ r2_hidden(X0,a_2_1_lattice3(sK12,sK14))
      | ~ l3_lattices(sK12)
      | v2_struct_0(sK12) ) ),
    inference(duplicate_literal_removal,[],[f720])).

fof(f720,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK12))
      | sK13 != X0
      | ~ r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14))
      | ~ m1_subset_1(X0,u1_struct_0(sK12))
      | ~ r2_hidden(X0,a_2_1_lattice3(sK12,sK14))
      | ~ l3_lattices(sK12)
      | v2_struct_0(sK12) ) ),
    inference(resolution,[],[f711,f337])).

fof(f337,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f336])).

fof(f336,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | sP3(X0,X2,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP3(X0,X2,X1) ) ),
    inference(resolution,[],[f332,f141])).

fof(f141,plain,(
    ! [X6,X7,X5] :
      ( sP7(X5,sK16(X6,X5,X7))
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | sP3(X6,X5,X7) ) ),
    inference(resolution,[],[f116,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK16(X0,X1,X2))
          & r4_lattice3(X1,sK16(X0,X1,X2),X2)
          & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f62,f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r4_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK16(X0,X1,X2))
        & r4_lattice3(X1,sK16(X0,X1,X2),X2)
        & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r4_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ( sP3(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_lattices(X0,X2,X3)
            & r4_lattice3(X0,X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X2,X3)
            | ~ r4_lattice3(X0,X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP3(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
    <=> ! [X3] :
          ( r1_lattices(X0,X2,X3)
          | ~ r4_lattice3(X0,X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f332,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X1,sK16(X0,X1,X2))
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | sP3(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f330])).

fof(f330,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ sP7(X1,sK16(X0,X1,X2))
      | sP3(X0,X1,X2)
      | sP3(X0,X1,X2) ) ),
    inference(resolution,[],[f241,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK16(X0,X1,X2))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f241,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X1,X0,sK16(X2,X1,X3))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X3)
      | ~ sP7(X1,sK16(X2,X1,X3))
      | sP3(X2,X1,X3) ) ),
    inference(resolution,[],[f208,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK16(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f208,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_lattice3(X2,X3,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | r1_lattices(X2,X0,X3)
      | ~ r2_hidden(X0,X1)
      | ~ sP7(X2,X3) ) ),
    inference(resolution,[],[f112,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( sP6(X1,X0,X2)
      | ~ r4_lattice3(X0,X1,X2)
      | ~ sP7(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f112,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP6(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f711,plain,(
    ! [X0] :
      ( ~ sP3(X0,sK12,a_2_1_lattice3(sK12,sK14))
      | ~ m1_subset_1(X0,u1_struct_0(sK12))
      | sK13 != X0
      | ~ r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14)) ) ),
    inference(subsumption_resolution,[],[f710,f80])).

fof(f710,plain,(
    ! [X0] :
      ( sK13 != X0
      | v2_struct_0(sK12)
      | ~ m1_subset_1(X0,u1_struct_0(sK12))
      | ~ sP3(X0,sK12,a_2_1_lattice3(sK12,sK14))
      | ~ r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14)) ) ),
    inference(subsumption_resolution,[],[f709,f81])).

fof(f81,plain,(
    v10_lattices(sK12) ),
    inference(cnf_transformation,[],[f46])).

fof(f709,plain,(
    ! [X0] :
      ( sK13 != X0
      | ~ v10_lattices(sK12)
      | v2_struct_0(sK12)
      | ~ m1_subset_1(X0,u1_struct_0(sK12))
      | ~ sP3(X0,sK12,a_2_1_lattice3(sK12,sK14))
      | ~ r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14)) ) ),
    inference(subsumption_resolution,[],[f708,f82])).

fof(f82,plain,(
    v4_lattice3(sK12) ),
    inference(cnf_transformation,[],[f46])).

fof(f708,plain,(
    ! [X0] :
      ( sK13 != X0
      | ~ v4_lattice3(sK12)
      | ~ v10_lattices(sK12)
      | v2_struct_0(sK12)
      | ~ m1_subset_1(X0,u1_struct_0(sK12))
      | ~ sP3(X0,sK12,a_2_1_lattice3(sK12,sK14))
      | ~ r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14)) ) ),
    inference(subsumption_resolution,[],[f705,f83])).

fof(f705,plain,(
    ! [X0] :
      ( sK13 != X0
      | ~ l3_lattices(sK12)
      | ~ v4_lattice3(sK12)
      | ~ v10_lattices(sK12)
      | v2_struct_0(sK12)
      | ~ m1_subset_1(X0,u1_struct_0(sK12))
      | ~ sP3(X0,sK12,a_2_1_lattice3(sK12,sK14))
      | ~ r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14)) ) ),
    inference(superposition,[],[f700,f593])).

fof(f593,plain,(
    ! [X6,X4,X5] :
      ( k15_lattice3(X4,X5) = X6
      | ~ l3_lattices(X4)
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ sP3(X6,X4,X5)
      | ~ r4_lattice3(X4,X6,X5) ) ),
    inference(subsumption_resolution,[],[f592,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f592,plain,(
    ! [X6,X4,X5] :
      ( k15_lattice3(X4,X5) = X6
      | ~ m1_subset_1(k15_lattice3(X4,X5),u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ sP3(X6,X4,X5)
      | ~ r4_lattice3(X4,X6,X5) ) ),
    inference(duplicate_literal_removal,[],[f591])).

fof(f591,plain,(
    ! [X6,X4,X5] :
      ( k15_lattice3(X4,X5) = X6
      | ~ m1_subset_1(k15_lattice3(X4,X5),u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ sP3(X6,X4,X5)
      | ~ r4_lattice3(X4,X6,X5)
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | v2_struct_0(X4)
      | ~ l3_lattices(X4) ) ),
    inference(resolution,[],[f457,f222])).

fof(f222,plain,(
    ! [X0,X1] :
      ( sP4(X1,X0,k15_lattice3(X0,X1))
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f217,f124])).

fof(f217,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP4(X1,X0,k15_lattice3(X0,X1)) ) ),
    inference(resolution,[],[f135,f133])).

fof(f133,plain,(
    ! [X2,X1] :
      ( ~ sP5(k15_lattice3(X1,X2),X1,X2)
      | sP4(X2,X1,k15_lattice3(X1,X2)) ) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X1,X0)
      | k15_lattice3(X1,X2) != X0
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( k15_lattice3(X1,X2) = X0
          | ~ sP4(X2,X1,X0) )
        & ( sP4(X2,X1,X0)
          | k15_lattice3(X1,X2) != X0 ) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ( ( k15_lattice3(X0,X1) = X2
          | ~ sP4(X1,X0,X2) )
        & ( sP4(X1,X0,X2)
          | k15_lattice3(X0,X1) != X2 ) )
      | ~ sP5(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ( k15_lattice3(X0,X1) = X2
      <=> sP4(X1,X0,X2) )
      | ~ sP5(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP5(X2,X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f32,f31,f30])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( sP4(X1,X0,X2)
    <=> ( sP3(X2,X0,X1)
        & r4_lattice3(X0,X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f457,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X2,X3,X0)
      | X0 = X1
      | ~ m1_subset_1(X0,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X1,u1_struct_0(X3))
      | ~ sP3(X1,X3,X2)
      | ~ r4_lattice3(X3,X1,X2) ) ),
    inference(resolution,[],[f389,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | ~ sP3(X2,X1,X0)
      | ~ r4_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ~ sP3(X2,X1,X0)
        | ~ r4_lattice3(X1,X2,X0) )
      & ( ( sP3(X2,X1,X0)
          & r4_lattice3(X1,X2,X0) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X1,X0,X2] :
      ( ( sP4(X1,X0,X2)
        | ~ sP3(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP3(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP4(X1,X0,X2) ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X1,X0,X2] :
      ( ( sP4(X1,X0,X2)
        | ~ sP3(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP3(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP4(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f389,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X2,X3,X1)
      | X0 = X1
      | ~ sP4(X2,X3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X1,u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f388])).

fof(f388,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X1
      | ~ sP4(X2,X3,X1)
      | ~ sP4(X2,X3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X1,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f250,f135])).

fof(f250,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | X2 = X3
      | ~ sP4(X0,X1,X3)
      | ~ sP4(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f185,f135])).

fof(f185,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X0,X1)
      | ~ sP4(X1,X0,X3)
      | X2 = X3
      | ~ sP4(X1,X0,X2)
      | ~ sP5(X2,X0,X1) ) ),
    inference(superposition,[],[f101,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X1,X2) = X0
      | ~ sP4(X2,X1,X0)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f700,plain,(
    sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)) ),
    inference(subsumption_resolution,[],[f699,f206])).

fof(f206,plain,(
    sP2(sK13,sK12) ),
    inference(subsumption_resolution,[],[f205,f80])).

fof(f205,plain,
    ( sP2(sK13,sK12)
    | v2_struct_0(sK12) ),
    inference(subsumption_resolution,[],[f204,f81])).

fof(f204,plain,
    ( sP2(sK13,sK12)
    | ~ v10_lattices(sK12)
    | v2_struct_0(sK12) ),
    inference(subsumption_resolution,[],[f203,f82])).

fof(f203,plain,
    ( sP2(sK13,sK12)
    | ~ v4_lattice3(sK12)
    | ~ v10_lattices(sK12)
    | v2_struct_0(sK12) ),
    inference(subsumption_resolution,[],[f196,f83])).

fof(f196,plain,
    ( sP2(sK13,sK12)
    | ~ l3_lattices(sK12)
    | ~ v4_lattice3(sK12)
    | ~ v10_lattices(sK12)
    | v2_struct_0(sK12) ),
    inference(resolution,[],[f99,f84])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP2(X1,X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f28,f27,f26])).

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r3_lattices(X0,X3,X1)
          | ~ r3_lattice3(X0,X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
    <=> ( sP0(X1,X0,X2)
        & r3_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f28,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( k16_lattice3(X0,X2) = X1
        <=> sP1(X2,X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(f699,plain,
    ( sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14))
    | ~ sP2(sK13,sK12) ),
    inference(subsumption_resolution,[],[f698,f86])).

fof(f86,plain,(
    r3_lattice3(sK12,sK13,sK14) ),
    inference(cnf_transformation,[],[f46])).

fof(f698,plain,
    ( ~ r3_lattice3(sK12,sK13,sK14)
    | sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14))
    | ~ sP2(sK13,sK12) ),
    inference(inner_rewriting,[],[f697])).

fof(f697,plain,
    ( ~ r3_lattice3(sK12,k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK14)
    | sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14))
    | ~ sP2(k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK12) ),
    inference(subsumption_resolution,[],[f696,f81])).

fof(f696,plain,
    ( ~ v10_lattices(sK12)
    | ~ r3_lattice3(sK12,k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK14)
    | sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14))
    | ~ sP2(k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK12) ),
    inference(subsumption_resolution,[],[f695,f83])).

fof(f695,plain,
    ( ~ l3_lattices(sK12)
    | ~ v10_lattices(sK12)
    | ~ r3_lattice3(sK12,k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK14)
    | sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14))
    | ~ sP2(k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK12) ),
    inference(subsumption_resolution,[],[f694,f82])).

fof(f694,plain,
    ( ~ v4_lattice3(sK12)
    | ~ l3_lattices(sK12)
    | ~ v10_lattices(sK12)
    | ~ r3_lattice3(sK12,k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK14)
    | sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14))
    | ~ sP2(k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK12) ),
    inference(subsumption_resolution,[],[f684,f80])).

fof(f684,plain,
    ( v2_struct_0(sK12)
    | ~ v4_lattice3(sK12)
    | ~ l3_lattices(sK12)
    | ~ v10_lattices(sK12)
    | ~ r3_lattice3(sK12,k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK14)
    | sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14))
    | ~ sP2(k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK12) ),
    inference(resolution,[],[f683,f178])).

fof(f178,plain,(
    ! [X6] :
      ( ~ sP0(X6,sK12,sK14)
      | ~ r3_lattice3(sK12,X6,sK14)
      | sK13 != X6
      | ~ sP2(X6,sK12) ) ),
    inference(resolution,[],[f94,f167])).

fof(f167,plain,(
    ! [X0] :
      ( ~ sP1(sK14,sK12,X0)
      | sK13 != X0
      | ~ sP2(X0,sK12) ) ),
    inference(superposition,[],[f87,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X1,X2) = X0
      | ~ sP1(X2,X1,X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k16_lattice3(X1,X2) = X0
            | ~ sP1(X2,X1,X0) )
          & ( sP1(X2,X1,X0)
            | k16_lattice3(X1,X2) != X0 ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( ( k16_lattice3(X0,X2) = X1
            | ~ sP1(X2,X0,X1) )
          & ( sP1(X2,X0,X1)
            | k16_lattice3(X0,X2) != X1 ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f87,plain,(
    sK13 != k16_lattice3(sK12,sK14) ),
    inference(cnf_transformation,[],[f46])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | ~ r3_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ~ sP0(X2,X1,X0)
        | ~ r3_lattice3(X1,X2,X0) )
      & ( ( sP0(X2,X1,X0)
          & r3_lattice3(X1,X2,X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ~ sP0(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP0(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ~ sP0(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP0(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f683,plain,(
    ! [X0,X1] :
      ( sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1)
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f682,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r3_lattices(X1,sK15(X0,X1,X2),X0)
          & r3_lattice3(X1,sK15(X0,X1,X2),X2)
          & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r3_lattices(X1,X4,X0)
            | ~ r3_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X1,X3,X0)
          & r3_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r3_lattices(X1,sK15(X0,X1,X2),X0)
        & r3_lattice3(X1,sK15(X0,X1,X2),X2)
        & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r3_lattices(X1,X3,X0)
            & r3_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r3_lattices(X1,X4,X0)
            | ~ r3_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
        | ? [X3] :
            ( ~ r3_lattices(X0,X3,X1)
            & r3_lattice3(X0,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r3_lattices(X0,X3,X1)
            | ~ r3_lattice3(X0,X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f682,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | ~ m1_subset_1(sK15(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f676])).

fof(f676,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ m1_subset_1(sK15(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1),u1_struct_0(X0))
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1) ) ),
    inference(resolution,[],[f536,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK15(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f536,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X1,sK15(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3),X2)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X0)
      | ~ m1_subset_1(sK15(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3),u1_struct_0(X1)) ) ),
    inference(resolution,[],[f436,f134])).

fof(f134,plain,(
    ! [X0,X3,X1] :
      ( sP10(X0,X1,X3)
      | ~ r3_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X2,X0,X3,X1] :
      ( sP10(X0,X1,X2)
      | ~ r3_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f436,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP10(X2,X1,sK15(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3)
      | ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f269,f131])).

fof(f269,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP11(sK15(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3),X1,X2)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3)
      | ~ sP10(X2,X1,sK15(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3))
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f230,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ sP10(X2,X1,X0)
      | ~ sP11(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f230,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK15(k15_lattice3(X0,X1),X0,X2),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,X1),X0,X2) ) ),
    inference(subsumption_resolution,[],[f228,f96])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK15(k15_lattice3(X0,X1),X0,X2),X1)
      | ~ m1_subset_1(sK15(k15_lattice3(X0,X1),X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP0(k15_lattice3(X0,X1),X0,X2) ) ),
    inference(resolution,[],[f88,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X1,sK15(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f758,plain,(
    spl20_4 ),
    inference(avatar_contradiction_clause,[],[f757])).

fof(f757,plain,
    ( $false
    | spl20_4 ),
    inference(subsumption_resolution,[],[f756,f84])).

fof(f756,plain,
    ( ~ m1_subset_1(sK13,u1_struct_0(sK12))
    | spl20_4 ),
    inference(subsumption_resolution,[],[f755,f86])).

fof(f755,plain,
    ( ~ r3_lattice3(sK12,sK13,sK14)
    | ~ m1_subset_1(sK13,u1_struct_0(sK12))
    | spl20_4 ),
    inference(resolution,[],[f749,f134])).

fof(f749,plain,
    ( ~ sP10(sK14,sK12,sK13)
    | spl20_4 ),
    inference(avatar_component_clause,[],[f747])).

fof(f747,plain,
    ( spl20_4
  <=> sP10(sK14,sK12,sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_4])])).

fof(f754,plain,(
    spl20_3 ),
    inference(avatar_contradiction_clause,[],[f753])).

fof(f753,plain,
    ( $false
    | spl20_3 ),
    inference(subsumption_resolution,[],[f752,f80])).

fof(f752,plain,
    ( v2_struct_0(sK12)
    | spl20_3 ),
    inference(subsumption_resolution,[],[f751,f83])).

fof(f751,plain,
    ( ~ l3_lattices(sK12)
    | v2_struct_0(sK12)
    | spl20_3 ),
    inference(resolution,[],[f745,f131])).

fof(f745,plain,
    ( ~ sP11(sK13,sK12,sK14)
    | spl20_3 ),
    inference(avatar_component_clause,[],[f743])).

fof(f743,plain,
    ( spl20_3
  <=> sP11(sK13,sK12,sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl20_3])])).

fof(f750,plain,
    ( ~ spl20_3
    | ~ spl20_4
    | spl20_1 ),
    inference(avatar_split_clause,[],[f741,f731,f747,f743])).

fof(f741,plain,
    ( ~ sP10(sK14,sK12,sK13)
    | ~ sP11(sK13,sK12,sK14)
    | spl20_1 ),
    inference(resolution,[],[f733,f126])).

fof(f733,plain,
    ( ~ r2_hidden(sK13,a_2_1_lattice3(sK12,sK14))
    | spl20_1 ),
    inference(avatar_component_clause,[],[f731])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:14:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (3768)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (3762)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (3782)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (3758)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (3763)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (3773)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (3761)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (3760)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (3764)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (3763)Refutation not found, incomplete strategy% (3763)------------------------------
% 0.21/0.51  % (3763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (3779)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.22/0.51  % (3769)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.22/0.51  % (3780)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.22/0.51  % (3770)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.22/0.51  % (3769)Refutation not found, incomplete strategy% (3769)------------------------------
% 1.22/0.51  % (3769)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.51  % (3769)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.51  
% 1.22/0.51  % (3769)Memory used [KB]: 10490
% 1.22/0.51  % (3769)Time elapsed: 0.107 s
% 1.22/0.51  % (3769)------------------------------
% 1.22/0.51  % (3769)------------------------------
% 1.22/0.52  % (3764)Refutation not found, incomplete strategy% (3764)------------------------------
% 1.22/0.52  % (3764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.52  % (3757)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.52  % (3784)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.22/0.52  % (3764)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (3764)Memory used [KB]: 1663
% 1.22/0.52  % (3764)Time elapsed: 0.071 s
% 1.22/0.52  % (3764)------------------------------
% 1.22/0.52  % (3764)------------------------------
% 1.22/0.52  % (3763)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.52  
% 1.22/0.52  % (3763)Memory used [KB]: 10746
% 1.22/0.52  % (3763)Time elapsed: 0.099 s
% 1.22/0.52  % (3763)------------------------------
% 1.22/0.52  % (3763)------------------------------
% 1.22/0.52  % (3783)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.22/0.52  % (3776)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.22/0.52  % (3778)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.22/0.53  % (3756)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.22/0.53  % (3756)Refutation not found, incomplete strategy% (3756)------------------------------
% 1.22/0.53  % (3756)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (3756)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (3756)Memory used [KB]: 10490
% 1.22/0.53  % (3756)Time elapsed: 0.114 s
% 1.22/0.53  % (3756)------------------------------
% 1.22/0.53  % (3756)------------------------------
% 1.22/0.53  % (3777)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.38/0.53  % (3771)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.38/0.53  % (3772)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.38/0.53  % (3771)Refutation not found, incomplete strategy% (3771)------------------------------
% 1.38/0.53  % (3771)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.53  % (3771)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.53  
% 1.38/0.53  % (3771)Memory used [KB]: 6140
% 1.38/0.53  % (3771)Time elapsed: 0.127 s
% 1.38/0.53  % (3771)------------------------------
% 1.38/0.53  % (3771)------------------------------
% 1.38/0.53  % (3765)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.38/0.53  % (3767)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.38/0.54  % (3775)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.38/0.54  % (3774)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.38/0.57  % (3761)Refutation found. Thanks to Tanya!
% 1.38/0.57  % SZS status Theorem for theBenchmark
% 1.38/0.58  % SZS output start Proof for theBenchmark
% 1.38/0.58  fof(f807,plain,(
% 1.38/0.58    $false),
% 1.38/0.58    inference(avatar_sat_refutation,[],[f750,f754,f758,f800])).
% 1.38/0.58  fof(f800,plain,(
% 1.38/0.58    ~spl20_1),
% 1.38/0.58    inference(avatar_contradiction_clause,[],[f799])).
% 1.38/0.58  fof(f799,plain,(
% 1.38/0.58    $false | ~spl20_1),
% 1.38/0.58    inference(subsumption_resolution,[],[f798,f85])).
% 1.38/0.58  fof(f85,plain,(
% 1.38/0.58    r2_hidden(sK13,sK14)),
% 1.38/0.58    inference(cnf_transformation,[],[f46])).
% 1.38/0.58  fof(f46,plain,(
% 1.38/0.58    ((sK13 != k16_lattice3(sK12,sK14) & r3_lattice3(sK12,sK13,sK14) & r2_hidden(sK13,sK14)) & m1_subset_1(sK13,u1_struct_0(sK12))) & l3_lattices(sK12) & v4_lattice3(sK12) & v10_lattices(sK12) & ~v2_struct_0(sK12)),
% 1.38/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f11,f45,f44,f43])).
% 1.38/0.58  fof(f43,plain,(
% 1.38/0.58    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK12,X2) != X1 & r3_lattice3(sK12,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK12))) & l3_lattices(sK12) & v4_lattice3(sK12) & v10_lattices(sK12) & ~v2_struct_0(sK12))),
% 1.38/0.58    introduced(choice_axiom,[])).
% 1.38/0.58  fof(f44,plain,(
% 1.38/0.58    ? [X1] : (? [X2] : (k16_lattice3(sK12,X2) != X1 & r3_lattice3(sK12,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK12))) => (? [X2] : (k16_lattice3(sK12,X2) != sK13 & r3_lattice3(sK12,sK13,X2) & r2_hidden(sK13,X2)) & m1_subset_1(sK13,u1_struct_0(sK12)))),
% 1.38/0.58    introduced(choice_axiom,[])).
% 1.38/0.58  fof(f45,plain,(
% 1.38/0.58    ? [X2] : (k16_lattice3(sK12,X2) != sK13 & r3_lattice3(sK12,sK13,X2) & r2_hidden(sK13,X2)) => (sK13 != k16_lattice3(sK12,sK14) & r3_lattice3(sK12,sK13,sK14) & r2_hidden(sK13,sK14))),
% 1.38/0.58    introduced(choice_axiom,[])).
% 1.38/0.58  fof(f11,plain,(
% 1.38/0.58    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.38/0.58    inference(flattening,[],[f10])).
% 1.38/0.58  fof(f10,plain,(
% 1.38/0.58    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.38/0.58    inference(ennf_transformation,[],[f9])).
% 1.38/0.58  fof(f9,negated_conjecture,(
% 1.38/0.58    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 1.38/0.58    inference(negated_conjecture,[],[f8])).
% 1.38/0.58  fof(f8,conjecture,(
% 1.38/0.58    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).
% 1.38/0.58  fof(f798,plain,(
% 1.38/0.58    ~r2_hidden(sK13,sK14) | ~spl20_1),
% 1.38/0.58    inference(subsumption_resolution,[],[f796,f84])).
% 1.38/0.58  fof(f84,plain,(
% 1.38/0.58    m1_subset_1(sK13,u1_struct_0(sK12))),
% 1.38/0.58    inference(cnf_transformation,[],[f46])).
% 1.38/0.58  fof(f796,plain,(
% 1.38/0.58    ~m1_subset_1(sK13,u1_struct_0(sK12)) | ~r2_hidden(sK13,sK14) | ~spl20_1),
% 1.38/0.58    inference(trivial_inequality_removal,[],[f793])).
% 1.38/0.58  fof(f793,plain,(
% 1.38/0.58    ~m1_subset_1(sK13,u1_struct_0(sK12)) | sK13 != sK13 | ~r2_hidden(sK13,sK14) | ~spl20_1),
% 1.38/0.58    inference(resolution,[],[f739,f732])).
% 1.38/0.58  fof(f732,plain,(
% 1.38/0.58    r2_hidden(sK13,a_2_1_lattice3(sK12,sK14)) | ~spl20_1),
% 1.38/0.58    inference(avatar_component_clause,[],[f731])).
% 1.38/0.58  fof(f731,plain,(
% 1.38/0.58    spl20_1 <=> r2_hidden(sK13,a_2_1_lattice3(sK12,sK14))),
% 1.38/0.58    introduced(avatar_definition,[new_symbols(naming,[spl20_1])])).
% 1.38/0.58  fof(f739,plain,(
% 1.38/0.58    ( ! [X1] : (~r2_hidden(X1,a_2_1_lattice3(sK12,sK14)) | ~m1_subset_1(X1,u1_struct_0(sK12)) | sK13 != X1 | ~r2_hidden(X1,sK14)) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f738,f80])).
% 1.38/0.58  fof(f80,plain,(
% 1.38/0.58    ~v2_struct_0(sK12)),
% 1.38/0.58    inference(cnf_transformation,[],[f46])).
% 1.38/0.58  fof(f738,plain,(
% 1.38/0.58    ( ! [X1] : (sK13 != X1 | ~m1_subset_1(X1,u1_struct_0(sK12)) | ~r2_hidden(X1,a_2_1_lattice3(sK12,sK14)) | ~r2_hidden(X1,sK14) | v2_struct_0(sK12)) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f727,f83])).
% 1.38/0.58  fof(f83,plain,(
% 1.38/0.58    l3_lattices(sK12)),
% 1.38/0.58    inference(cnf_transformation,[],[f46])).
% 1.38/0.58  fof(f727,plain,(
% 1.38/0.58    ( ! [X1] : (sK13 != X1 | ~m1_subset_1(X1,u1_struct_0(sK12)) | ~r2_hidden(X1,a_2_1_lattice3(sK12,sK14)) | ~r2_hidden(X1,sK14) | ~l3_lattices(sK12) | v2_struct_0(sK12)) )),
% 1.38/0.58    inference(duplicate_literal_removal,[],[f726])).
% 1.38/0.58  fof(f726,plain,(
% 1.38/0.58    ( ! [X1] : (sK13 != X1 | ~m1_subset_1(X1,u1_struct_0(sK12)) | ~r2_hidden(X1,a_2_1_lattice3(sK12,sK14)) | ~r2_hidden(X1,sK14) | ~l3_lattices(sK12) | v2_struct_0(sK12) | ~m1_subset_1(X1,u1_struct_0(sK12))) )),
% 1.38/0.58    inference(resolution,[],[f723,f352])).
% 1.38/0.58  fof(f352,plain,(
% 1.38/0.58    ( ! [X6,X4,X5] : (r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | v2_struct_0(X5) | ~m1_subset_1(X4,u1_struct_0(X5))) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f351,f116])).
% 1.38/0.58  fof(f116,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP7(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f36])).
% 1.38/0.58  fof(f36,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (sP7(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.38/0.58    inference(definition_folding,[],[f19,f35,f34])).
% 1.38/0.58  fof(f34,plain,(
% 1.38/0.58    ! [X1,X0,X2] : (sP6(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.38/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 1.38/0.58  fof(f35,plain,(
% 1.38/0.58    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP6(X1,X0,X2)) | ~sP7(X0,X1))),
% 1.38/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 1.38/0.58  fof(f19,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.38/0.58    inference(flattening,[],[f18])).
% 1.38/0.58  fof(f18,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.38/0.58    inference(ennf_transformation,[],[f2])).
% 1.38/0.58  fof(f2,axiom,(
% 1.38/0.58    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 1.38/0.58  fof(f351,plain,(
% 1.38/0.58    ( ! [X6,X4,X5] : (~m1_subset_1(X4,u1_struct_0(X5)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | v2_struct_0(X5) | r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6)) | ~sP7(X5,X4)) )),
% 1.38/0.58    inference(resolution,[],[f349,f111])).
% 1.38/0.58  fof(f111,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (~sP6(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP7(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f65])).
% 1.38/0.58  fof(f65,plain,(
% 1.38/0.58    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP6(X1,X0,X2)) & (sP6(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP7(X0,X1))),
% 1.38/0.58    inference(nnf_transformation,[],[f35])).
% 1.38/0.58  fof(f349,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (sP6(X0,X2,a_2_1_lattice3(X2,X1)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f348,f153])).
% 1.38/0.58  fof(f153,plain,(
% 1.38/0.58    ( ! [X10,X8,X9] : (sP9(X8,sK17(X9,X8,X10)) | ~l3_lattices(X8) | v2_struct_0(X8) | sP6(X9,X8,X10)) )),
% 1.38/0.58    inference(resolution,[],[f123,f113])).
% 1.38/0.58  fof(f113,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) | sP6(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f69])).
% 1.38/0.58  fof(f69,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((sP6(X0,X1,X2) | (~r1_lattices(X1,sK17(X0,X1,X2),X0) & r2_hidden(sK17(X0,X1,X2),X2) & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP6(X0,X1,X2)))),
% 1.38/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f67,f68])).
% 1.38/0.58  fof(f68,plain,(
% 1.38/0.58    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK17(X0,X1,X2),X0) & r2_hidden(sK17(X0,X1,X2),X2) & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))))),
% 1.38/0.58    introduced(choice_axiom,[])).
% 1.38/0.58  fof(f67,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((sP6(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP6(X0,X1,X2)))),
% 1.38/0.58    inference(rectify,[],[f66])).
% 1.38/0.58  fof(f66,plain,(
% 1.38/0.58    ! [X1,X0,X2] : ((sP6(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP6(X1,X0,X2)))),
% 1.38/0.58    inference(nnf_transformation,[],[f34])).
% 1.38/0.58  fof(f123,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP9(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f39])).
% 1.38/0.58  fof(f39,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (sP9(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.38/0.58    inference(definition_folding,[],[f21,f38,f37])).
% 1.38/0.58  fof(f37,plain,(
% 1.38/0.58    ! [X1,X0,X2] : (sP8(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.38/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 1.38/0.58  fof(f38,plain,(
% 1.38/0.58    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP8(X1,X0,X2)) | ~sP9(X0,X1))),
% 1.38/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 1.38/0.58  fof(f21,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.38/0.58    inference(flattening,[],[f20])).
% 1.38/0.58  fof(f20,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.38/0.58    inference(ennf_transformation,[],[f1])).
% 1.38/0.58  fof(f1,axiom,(
% 1.38/0.58    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 1.38/0.58  fof(f348,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~sP9(X2,sK17(X0,X2,a_2_1_lattice3(X2,X1))) | sP6(X0,X2,a_2_1_lattice3(X2,X1)) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 1.38/0.58    inference(duplicate_literal_removal,[],[f347])).
% 1.38/0.58  fof(f347,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~sP9(X2,sK17(X0,X2,a_2_1_lattice3(X2,X1))) | sP6(X0,X2,a_2_1_lattice3(X2,X1)) | ~l3_lattices(X2) | v2_struct_0(X2) | sP6(X0,X2,a_2_1_lattice3(X2,X1))) )),
% 1.38/0.58    inference(resolution,[],[f246,f295])).
% 1.38/0.58  fof(f295,plain,(
% 1.38/0.58    ( ! [X14,X12,X15,X13] : (r3_lattice3(X14,sK17(X12,X13,a_2_1_lattice3(X14,X15)),X15) | ~l3_lattices(X14) | v2_struct_0(X14) | sP6(X12,X13,a_2_1_lattice3(X14,X15))) )),
% 1.38/0.58    inference(resolution,[],[f291,f163])).
% 1.38/0.58  fof(f163,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (~sP10(X0,X1,X2) | r3_lattice3(X1,X2,X0)) )),
% 1.38/0.58    inference(duplicate_literal_removal,[],[f162])).
% 1.38/0.58  fof(f162,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (r3_lattice3(X1,X2,X0) | ~sP10(X0,X1,X2) | ~sP10(X0,X1,X2)) )),
% 1.38/0.58    inference(superposition,[],[f129,f128])).
% 1.38/0.58  fof(f128,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (sK19(X0,X1,X2) = X2 | ~sP10(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f79])).
% 1.38/0.58  fof(f79,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((sP10(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK19(X0,X1,X2),X0) & sK19(X0,X1,X2) = X2 & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1))) | ~sP10(X0,X1,X2)))),
% 1.38/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f77,f78])).
% 1.38/0.58  fof(f78,plain,(
% 1.38/0.58    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK19(X0,X1,X2),X0) & sK19(X0,X1,X2) = X2 & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1))))),
% 1.38/0.58    introduced(choice_axiom,[])).
% 1.38/0.58  fof(f77,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((sP10(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP10(X0,X1,X2)))),
% 1.38/0.58    inference(rectify,[],[f76])).
% 1.38/0.58  fof(f76,plain,(
% 1.38/0.58    ! [X2,X1,X0] : ((sP10(X2,X1,X0) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP10(X2,X1,X0)))),
% 1.38/0.58    inference(nnf_transformation,[],[f40])).
% 1.38/0.58  fof(f40,plain,(
% 1.38/0.58    ! [X2,X1,X0] : (sP10(X2,X1,X0) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 1.38/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).
% 1.38/0.58  fof(f129,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK19(X0,X1,X2),X0) | ~sP10(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f79])).
% 1.38/0.58  fof(f291,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (sP10(X0,X1,sK17(X2,X3,a_2_1_lattice3(X1,X0))) | sP6(X2,X3,a_2_1_lattice3(X1,X0)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 1.38/0.58    inference(resolution,[],[f191,f131])).
% 1.38/0.58  fof(f131,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (sP11(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f42])).
% 1.38/0.58  fof(f42,plain,(
% 1.38/0.58    ! [X0,X1,X2] : (sP11(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 1.38/0.58    inference(definition_folding,[],[f25,f41,f40])).
% 1.38/0.58  fof(f41,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> sP10(X2,X1,X0)) | ~sP11(X0,X1,X2))),
% 1.38/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).
% 1.38/0.58  fof(f25,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 1.38/0.58    inference(flattening,[],[f24])).
% 1.38/0.58  fof(f24,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 1.38/0.58    inference(ennf_transformation,[],[f5])).
% 1.38/0.58  fof(f5,axiom,(
% 1.38/0.58    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).
% 1.38/0.58  fof(f191,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (~sP11(sK17(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0) | sP10(X0,X1,sK17(X2,X3,a_2_1_lattice3(X1,X0))) | sP6(X2,X3,a_2_1_lattice3(X1,X0))) )),
% 1.38/0.58    inference(resolution,[],[f125,f114])).
% 1.38/0.58  fof(f114,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (r2_hidden(sK17(X0,X1,X2),X2) | sP6(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f69])).
% 1.38/0.58  fof(f125,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | sP10(X2,X1,X0) | ~sP11(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f75])).
% 1.38/0.58  fof(f75,plain,(
% 1.38/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP10(X2,X1,X0)) & (sP10(X2,X1,X0) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~sP11(X0,X1,X2))),
% 1.38/0.58    inference(nnf_transformation,[],[f41])).
% 1.38/0.58  fof(f246,plain,(
% 1.38/0.58    ( ! [X10,X8,X11,X9] : (~r3_lattice3(X9,sK17(X8,X9,X11),X10) | ~r2_hidden(X8,X10) | ~m1_subset_1(X8,u1_struct_0(X9)) | ~sP9(X9,sK17(X8,X9,X11)) | sP6(X8,X9,X11)) )),
% 1.38/0.58    inference(resolution,[],[f215,f115])).
% 1.38/0.58  fof(f115,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK17(X0,X1,X2),X0) | sP6(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f69])).
% 1.38/0.58  fof(f215,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (r1_lattices(X2,X3,X0) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~r3_lattice3(X2,X3,X1) | ~sP9(X2,X3)) )),
% 1.38/0.58    inference(resolution,[],[f119,f117])).
% 1.38/0.58  fof(f117,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (sP8(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | ~sP9(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f70])).
% 1.38/0.58  fof(f70,plain,(
% 1.38/0.58    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP8(X1,X0,X2)) & (sP8(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP9(X0,X1))),
% 1.38/0.58    inference(nnf_transformation,[],[f38])).
% 1.38/0.58  fof(f119,plain,(
% 1.38/0.58    ( ! [X4,X2,X0,X1] : (~sP8(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f74])).
% 1.38/0.58  fof(f74,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((sP8(X0,X1,X2) | (~r1_lattices(X1,X0,sK18(X0,X1,X2)) & r2_hidden(sK18(X0,X1,X2),X2) & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP8(X0,X1,X2)))),
% 1.38/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f72,f73])).
% 1.38/0.58  fof(f73,plain,(
% 1.38/0.58    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK18(X0,X1,X2)) & r2_hidden(sK18(X0,X1,X2),X2) & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1))))),
% 1.38/0.58    introduced(choice_axiom,[])).
% 1.38/0.58  fof(f72,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((sP8(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP8(X0,X1,X2)))),
% 1.38/0.58    inference(rectify,[],[f71])).
% 1.38/0.58  fof(f71,plain,(
% 1.38/0.58    ! [X1,X0,X2] : ((sP8(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP8(X1,X0,X2)))),
% 1.38/0.58    inference(nnf_transformation,[],[f37])).
% 1.38/0.58  fof(f723,plain,(
% 1.38/0.58    ( ! [X0] : (~r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14)) | sK13 != X0 | ~m1_subset_1(X0,u1_struct_0(sK12)) | ~r2_hidden(X0,a_2_1_lattice3(sK12,sK14))) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f722,f80])).
% 1.38/0.58  fof(f722,plain,(
% 1.38/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK12)) | sK13 != X0 | ~r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14)) | ~r2_hidden(X0,a_2_1_lattice3(sK12,sK14)) | v2_struct_0(sK12)) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f721,f83])).
% 1.38/0.58  fof(f721,plain,(
% 1.38/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK12)) | sK13 != X0 | ~r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14)) | ~r2_hidden(X0,a_2_1_lattice3(sK12,sK14)) | ~l3_lattices(sK12) | v2_struct_0(sK12)) )),
% 1.38/0.58    inference(duplicate_literal_removal,[],[f720])).
% 1.38/0.58  fof(f720,plain,(
% 1.38/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK12)) | sK13 != X0 | ~r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14)) | ~m1_subset_1(X0,u1_struct_0(sK12)) | ~r2_hidden(X0,a_2_1_lattice3(sK12,sK14)) | ~l3_lattices(sK12) | v2_struct_0(sK12)) )),
% 1.38/0.58    inference(resolution,[],[f711,f337])).
% 1.38/0.58  fof(f337,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (sP3(X0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 1.38/0.58    inference(duplicate_literal_removal,[],[f336])).
% 1.38/0.58  fof(f336,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | sP3(X0,X2,X1) | ~l3_lattices(X2) | v2_struct_0(X2) | sP3(X0,X2,X1)) )),
% 1.38/0.58    inference(resolution,[],[f332,f141])).
% 1.38/0.58  fof(f141,plain,(
% 1.38/0.58    ( ! [X6,X7,X5] : (sP7(X5,sK16(X6,X5,X7)) | ~l3_lattices(X5) | v2_struct_0(X5) | sP3(X6,X5,X7)) )),
% 1.38/0.58    inference(resolution,[],[f116,f106])).
% 1.38/0.58  fof(f106,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) | sP3(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f64])).
% 1.38/0.58  fof(f64,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (~r1_lattices(X1,X0,sK16(X0,X1,X2)) & r4_lattice3(X1,sK16(X0,X1,X2),X2) & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 1.38/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f62,f63])).
% 1.38/0.58  fof(f63,plain,(
% 1.38/0.58    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK16(X0,X1,X2)) & r4_lattice3(X1,sK16(X0,X1,X2),X2) & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))))),
% 1.38/0.58    introduced(choice_axiom,[])).
% 1.38/0.58  fof(f62,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 1.38/0.58    inference(rectify,[],[f61])).
% 1.38/0.58  fof(f61,plain,(
% 1.38/0.58    ! [X2,X0,X1] : ((sP3(X2,X0,X1) | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP3(X2,X0,X1)))),
% 1.38/0.58    inference(nnf_transformation,[],[f30])).
% 1.38/0.58  fof(f30,plain,(
% 1.38/0.58    ! [X2,X0,X1] : (sP3(X2,X0,X1) <=> ! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.38/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.38/0.58  fof(f332,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (~sP7(X1,sK16(X0,X1,X2)) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | sP3(X0,X1,X2)) )),
% 1.38/0.58    inference(duplicate_literal_removal,[],[f330])).
% 1.38/0.58  fof(f330,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~sP7(X1,sK16(X0,X1,X2)) | sP3(X0,X1,X2) | sP3(X0,X1,X2)) )),
% 1.38/0.58    inference(resolution,[],[f241,f108])).
% 1.38/0.58  fof(f108,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK16(X0,X1,X2)) | sP3(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f64])).
% 1.38/0.58  fof(f241,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (r1_lattices(X1,X0,sK16(X2,X1,X3)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X3) | ~sP7(X1,sK16(X2,X1,X3)) | sP3(X2,X1,X3)) )),
% 1.38/0.58    inference(resolution,[],[f208,f107])).
% 1.38/0.58  fof(f107,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK16(X0,X1,X2),X2) | sP3(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f64])).
% 1.38/0.58  fof(f208,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (~r4_lattice3(X2,X3,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | r1_lattices(X2,X0,X3) | ~r2_hidden(X0,X1) | ~sP7(X2,X3)) )),
% 1.38/0.58    inference(resolution,[],[f112,f110])).
% 1.38/0.58  fof(f110,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (sP6(X1,X0,X2) | ~r4_lattice3(X0,X1,X2) | ~sP7(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f65])).
% 1.38/0.58  fof(f112,plain,(
% 1.38/0.58    ( ! [X4,X2,X0,X1] : (~sP6(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X4,X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f69])).
% 1.38/0.58  fof(f711,plain,(
% 1.38/0.58    ( ! [X0] : (~sP3(X0,sK12,a_2_1_lattice3(sK12,sK14)) | ~m1_subset_1(X0,u1_struct_0(sK12)) | sK13 != X0 | ~r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14))) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f710,f80])).
% 1.38/0.58  fof(f710,plain,(
% 1.38/0.58    ( ! [X0] : (sK13 != X0 | v2_struct_0(sK12) | ~m1_subset_1(X0,u1_struct_0(sK12)) | ~sP3(X0,sK12,a_2_1_lattice3(sK12,sK14)) | ~r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14))) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f709,f81])).
% 1.38/0.58  fof(f81,plain,(
% 1.38/0.58    v10_lattices(sK12)),
% 1.38/0.58    inference(cnf_transformation,[],[f46])).
% 1.38/0.58  fof(f709,plain,(
% 1.38/0.58    ( ! [X0] : (sK13 != X0 | ~v10_lattices(sK12) | v2_struct_0(sK12) | ~m1_subset_1(X0,u1_struct_0(sK12)) | ~sP3(X0,sK12,a_2_1_lattice3(sK12,sK14)) | ~r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14))) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f708,f82])).
% 1.38/0.58  fof(f82,plain,(
% 1.38/0.58    v4_lattice3(sK12)),
% 1.38/0.58    inference(cnf_transformation,[],[f46])).
% 1.38/0.58  fof(f708,plain,(
% 1.38/0.58    ( ! [X0] : (sK13 != X0 | ~v4_lattice3(sK12) | ~v10_lattices(sK12) | v2_struct_0(sK12) | ~m1_subset_1(X0,u1_struct_0(sK12)) | ~sP3(X0,sK12,a_2_1_lattice3(sK12,sK14)) | ~r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14))) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f705,f83])).
% 1.38/0.58  fof(f705,plain,(
% 1.38/0.58    ( ! [X0] : (sK13 != X0 | ~l3_lattices(sK12) | ~v4_lattice3(sK12) | ~v10_lattices(sK12) | v2_struct_0(sK12) | ~m1_subset_1(X0,u1_struct_0(sK12)) | ~sP3(X0,sK12,a_2_1_lattice3(sK12,sK14)) | ~r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14))) )),
% 1.38/0.58    inference(superposition,[],[f700,f593])).
% 1.38/0.58  fof(f593,plain,(
% 1.38/0.58    ( ! [X6,X4,X5] : (k15_lattice3(X4,X5) = X6 | ~l3_lattices(X4) | ~v4_lattice3(X4) | ~v10_lattices(X4) | v2_struct_0(X4) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~sP3(X6,X4,X5) | ~r4_lattice3(X4,X6,X5)) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f592,f124])).
% 1.38/0.58  fof(f124,plain,(
% 1.38/0.58    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f23])).
% 1.38/0.58  fof(f23,plain,(
% 1.38/0.58    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.38/0.58    inference(flattening,[],[f22])).
% 1.38/0.58  fof(f22,plain,(
% 1.38/0.58    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.38/0.58    inference(ennf_transformation,[],[f4])).
% 1.38/0.58  fof(f4,axiom,(
% 1.38/0.58    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 1.38/0.58  fof(f592,plain,(
% 1.38/0.58    ( ! [X6,X4,X5] : (k15_lattice3(X4,X5) = X6 | ~m1_subset_1(k15_lattice3(X4,X5),u1_struct_0(X4)) | ~l3_lattices(X4) | ~v4_lattice3(X4) | ~v10_lattices(X4) | v2_struct_0(X4) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~sP3(X6,X4,X5) | ~r4_lattice3(X4,X6,X5)) )),
% 1.38/0.58    inference(duplicate_literal_removal,[],[f591])).
% 1.38/0.58  fof(f591,plain,(
% 1.38/0.58    ( ! [X6,X4,X5] : (k15_lattice3(X4,X5) = X6 | ~m1_subset_1(k15_lattice3(X4,X5),u1_struct_0(X4)) | ~l3_lattices(X4) | ~v4_lattice3(X4) | ~v10_lattices(X4) | v2_struct_0(X4) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~sP3(X6,X4,X5) | ~r4_lattice3(X4,X6,X5) | ~v4_lattice3(X4) | ~v10_lattices(X4) | v2_struct_0(X4) | ~l3_lattices(X4)) )),
% 1.38/0.58    inference(resolution,[],[f457,f222])).
% 1.38/0.58  fof(f222,plain,(
% 1.38/0.58    ( ! [X0,X1] : (sP4(X1,X0,k15_lattice3(X0,X1)) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f217,f124])).
% 1.38/0.58  fof(f217,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP4(X1,X0,k15_lattice3(X0,X1))) )),
% 1.38/0.58    inference(resolution,[],[f135,f133])).
% 1.38/0.58  fof(f133,plain,(
% 1.38/0.58    ( ! [X2,X1] : (~sP5(k15_lattice3(X1,X2),X1,X2) | sP4(X2,X1,k15_lattice3(X1,X2))) )),
% 1.38/0.58    inference(equality_resolution,[],[f100])).
% 1.38/0.58  fof(f100,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (sP4(X2,X1,X0) | k15_lattice3(X1,X2) != X0 | ~sP5(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f57])).
% 1.38/0.58  fof(f57,plain,(
% 1.38/0.58    ! [X0,X1,X2] : (((k15_lattice3(X1,X2) = X0 | ~sP4(X2,X1,X0)) & (sP4(X2,X1,X0) | k15_lattice3(X1,X2) != X0)) | ~sP5(X0,X1,X2))),
% 1.38/0.58    inference(rectify,[],[f56])).
% 1.38/0.58  fof(f56,plain,(
% 1.38/0.58    ! [X2,X0,X1] : (((k15_lattice3(X0,X1) = X2 | ~sP4(X1,X0,X2)) & (sP4(X1,X0,X2) | k15_lattice3(X0,X1) != X2)) | ~sP5(X2,X0,X1))),
% 1.38/0.58    inference(nnf_transformation,[],[f32])).
% 1.38/0.58  fof(f32,plain,(
% 1.38/0.58    ! [X2,X0,X1] : ((k15_lattice3(X0,X1) = X2 <=> sP4(X1,X0,X2)) | ~sP5(X2,X0,X1))),
% 1.38/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 1.38/0.58  fof(f135,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (sP5(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.38/0.58    inference(duplicate_literal_removal,[],[f109])).
% 1.38/0.58  fof(f109,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (sP5(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f33])).
% 1.38/0.58  fof(f33,plain,(
% 1.38/0.58    ! [X0] : (! [X1,X2] : (sP5(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.38/0.58    inference(definition_folding,[],[f17,f32,f31,f30])).
% 1.38/0.58  fof(f31,plain,(
% 1.38/0.58    ! [X1,X0,X2] : (sP4(X1,X0,X2) <=> (sP3(X2,X0,X1) & r4_lattice3(X0,X2,X1)))),
% 1.38/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.38/0.58  fof(f17,plain,(
% 1.38/0.58    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.38/0.58    inference(flattening,[],[f16])).
% 1.38/0.58  fof(f16,plain,(
% 1.38/0.58    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.38/0.58    inference(ennf_transformation,[],[f3])).
% 1.38/0.58  fof(f3,axiom,(
% 1.38/0.58    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 1.38/0.58  fof(f457,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (~sP4(X2,X3,X0) | X0 = X1 | ~m1_subset_1(X0,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v4_lattice3(X3) | ~v10_lattices(X3) | v2_struct_0(X3) | ~m1_subset_1(X1,u1_struct_0(X3)) | ~sP3(X1,X3,X2) | ~r4_lattice3(X3,X1,X2)) )),
% 1.38/0.58    inference(resolution,[],[f389,f104])).
% 1.38/0.58  fof(f104,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (sP4(X0,X1,X2) | ~sP3(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f60])).
% 1.38/0.58  fof(f60,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ~sP3(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) & ((sP3(X2,X1,X0) & r4_lattice3(X1,X2,X0)) | ~sP4(X0,X1,X2)))),
% 1.38/0.58    inference(rectify,[],[f59])).
% 1.38/0.58  fof(f59,plain,(
% 1.38/0.58    ! [X1,X0,X2] : ((sP4(X1,X0,X2) | ~sP3(X2,X0,X1) | ~r4_lattice3(X0,X2,X1)) & ((sP3(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP4(X1,X0,X2)))),
% 1.38/0.58    inference(flattening,[],[f58])).
% 1.38/0.58  fof(f58,plain,(
% 1.38/0.58    ! [X1,X0,X2] : ((sP4(X1,X0,X2) | (~sP3(X2,X0,X1) | ~r4_lattice3(X0,X2,X1))) & ((sP3(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP4(X1,X0,X2)))),
% 1.38/0.58    inference(nnf_transformation,[],[f31])).
% 1.38/0.58  fof(f389,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (~sP4(X2,X3,X1) | X0 = X1 | ~sP4(X2,X3,X0) | ~m1_subset_1(X0,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v4_lattice3(X3) | ~v10_lattices(X3) | v2_struct_0(X3) | ~m1_subset_1(X1,u1_struct_0(X3))) )),
% 1.38/0.58    inference(duplicate_literal_removal,[],[f388])).
% 1.38/0.58  fof(f388,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (X0 = X1 | ~sP4(X2,X3,X1) | ~sP4(X2,X3,X0) | ~m1_subset_1(X0,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v4_lattice3(X3) | ~v10_lattices(X3) | v2_struct_0(X3) | ~m1_subset_1(X1,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v4_lattice3(X3) | ~v10_lattices(X3) | v2_struct_0(X3)) )),
% 1.38/0.58    inference(resolution,[],[f250,f135])).
% 1.38/0.58  fof(f250,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (~sP5(X3,X1,X0) | X2 = X3 | ~sP4(X0,X1,X3) | ~sP4(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.38/0.58    inference(resolution,[],[f185,f135])).
% 1.38/0.58  fof(f185,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (~sP5(X3,X0,X1) | ~sP4(X1,X0,X3) | X2 = X3 | ~sP4(X1,X0,X2) | ~sP5(X2,X0,X1)) )),
% 1.38/0.58    inference(superposition,[],[f101,f101])).
% 1.38/0.58  fof(f101,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (k15_lattice3(X1,X2) = X0 | ~sP4(X2,X1,X0) | ~sP5(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f57])).
% 1.38/0.58  fof(f700,plain,(
% 1.38/0.58    sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14))),
% 1.38/0.58    inference(subsumption_resolution,[],[f699,f206])).
% 1.38/0.58  fof(f206,plain,(
% 1.38/0.58    sP2(sK13,sK12)),
% 1.38/0.58    inference(subsumption_resolution,[],[f205,f80])).
% 1.38/0.58  fof(f205,plain,(
% 1.38/0.58    sP2(sK13,sK12) | v2_struct_0(sK12)),
% 1.38/0.58    inference(subsumption_resolution,[],[f204,f81])).
% 1.38/0.58  fof(f204,plain,(
% 1.38/0.58    sP2(sK13,sK12) | ~v10_lattices(sK12) | v2_struct_0(sK12)),
% 1.38/0.58    inference(subsumption_resolution,[],[f203,f82])).
% 1.38/0.58  fof(f203,plain,(
% 1.38/0.58    sP2(sK13,sK12) | ~v4_lattice3(sK12) | ~v10_lattices(sK12) | v2_struct_0(sK12)),
% 1.38/0.58    inference(subsumption_resolution,[],[f196,f83])).
% 1.38/0.58  fof(f196,plain,(
% 1.38/0.58    sP2(sK13,sK12) | ~l3_lattices(sK12) | ~v4_lattice3(sK12) | ~v10_lattices(sK12) | v2_struct_0(sK12)),
% 1.38/0.58    inference(resolution,[],[f99,f84])).
% 1.38/0.58  fof(f99,plain,(
% 1.38/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP2(X1,X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f29])).
% 1.38/0.58  fof(f29,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.38/0.58    inference(definition_folding,[],[f15,f28,f27,f26])).
% 1.38/0.58  fof(f26,plain,(
% 1.38/0.58    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.38/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.38/0.58  fof(f27,plain,(
% 1.38/0.58    ! [X2,X0,X1] : (sP1(X2,X0,X1) <=> (sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)))),
% 1.38/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.38/0.58  fof(f28,plain,(
% 1.38/0.58    ! [X1,X0] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> sP1(X2,X0,X1)) | ~sP2(X1,X0))),
% 1.38/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.38/0.58  fof(f15,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.38/0.58    inference(flattening,[],[f14])).
% 1.38/0.58  fof(f14,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.38/0.58    inference(ennf_transformation,[],[f6])).
% 1.38/0.58  fof(f6,axiom,(
% 1.38/0.58    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 1.38/0.58  fof(f699,plain,(
% 1.38/0.58    sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)) | ~sP2(sK13,sK12)),
% 1.38/0.58    inference(subsumption_resolution,[],[f698,f86])).
% 1.38/0.58  fof(f86,plain,(
% 1.38/0.58    r3_lattice3(sK12,sK13,sK14)),
% 1.38/0.58    inference(cnf_transformation,[],[f46])).
% 1.38/0.58  fof(f698,plain,(
% 1.38/0.58    ~r3_lattice3(sK12,sK13,sK14) | sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)) | ~sP2(sK13,sK12)),
% 1.38/0.58    inference(inner_rewriting,[],[f697])).
% 1.38/0.58  fof(f697,plain,(
% 1.38/0.58    ~r3_lattice3(sK12,k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK14) | sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)) | ~sP2(k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK12)),
% 1.38/0.58    inference(subsumption_resolution,[],[f696,f81])).
% 1.38/0.58  fof(f696,plain,(
% 1.38/0.58    ~v10_lattices(sK12) | ~r3_lattice3(sK12,k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK14) | sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)) | ~sP2(k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK12)),
% 1.38/0.58    inference(subsumption_resolution,[],[f695,f83])).
% 1.38/0.58  fof(f695,plain,(
% 1.38/0.58    ~l3_lattices(sK12) | ~v10_lattices(sK12) | ~r3_lattice3(sK12,k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK14) | sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)) | ~sP2(k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK12)),
% 1.38/0.58    inference(subsumption_resolution,[],[f694,f82])).
% 1.38/0.58  fof(f694,plain,(
% 1.38/0.58    ~v4_lattice3(sK12) | ~l3_lattices(sK12) | ~v10_lattices(sK12) | ~r3_lattice3(sK12,k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK14) | sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)) | ~sP2(k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK12)),
% 1.38/0.58    inference(subsumption_resolution,[],[f684,f80])).
% 1.38/0.58  fof(f684,plain,(
% 1.38/0.58    v2_struct_0(sK12) | ~v4_lattice3(sK12) | ~l3_lattices(sK12) | ~v10_lattices(sK12) | ~r3_lattice3(sK12,k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK14) | sK13 != k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)) | ~sP2(k15_lattice3(sK12,a_2_1_lattice3(sK12,sK14)),sK12)),
% 1.38/0.58    inference(resolution,[],[f683,f178])).
% 1.38/0.58  fof(f178,plain,(
% 1.38/0.58    ( ! [X6] : (~sP0(X6,sK12,sK14) | ~r3_lattice3(sK12,X6,sK14) | sK13 != X6 | ~sP2(X6,sK12)) )),
% 1.38/0.58    inference(resolution,[],[f94,f167])).
% 1.38/0.58  fof(f167,plain,(
% 1.38/0.58    ( ! [X0] : (~sP1(sK14,sK12,X0) | sK13 != X0 | ~sP2(X0,sK12)) )),
% 1.38/0.58    inference(superposition,[],[f87,f91])).
% 1.38/0.58  fof(f91,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (k16_lattice3(X1,X2) = X0 | ~sP1(X2,X1,X0) | ~sP2(X0,X1)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f48])).
% 1.38/0.58  fof(f48,plain,(
% 1.38/0.58    ! [X0,X1] : (! [X2] : ((k16_lattice3(X1,X2) = X0 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k16_lattice3(X1,X2) != X0)) | ~sP2(X0,X1))),
% 1.38/0.58    inference(rectify,[],[f47])).
% 1.38/0.58  fof(f47,plain,(
% 1.38/0.58    ! [X1,X0] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ~sP1(X2,X0,X1)) & (sP1(X2,X0,X1) | k16_lattice3(X0,X2) != X1)) | ~sP2(X1,X0))),
% 1.38/0.58    inference(nnf_transformation,[],[f28])).
% 1.38/0.58  fof(f87,plain,(
% 1.38/0.58    sK13 != k16_lattice3(sK12,sK14)),
% 1.38/0.58    inference(cnf_transformation,[],[f46])).
% 1.38/0.58  fof(f94,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f51])).
% 1.38/0.58  fof(f51,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) & ((sP0(X2,X1,X0) & r3_lattice3(X1,X2,X0)) | ~sP1(X0,X1,X2)))),
% 1.38/0.58    inference(rectify,[],[f50])).
% 1.38/0.58  fof(f50,plain,(
% 1.38/0.58    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | ~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2)) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP1(X2,X0,X1)))),
% 1.38/0.58    inference(flattening,[],[f49])).
% 1.38/0.58  fof(f49,plain,(
% 1.38/0.58    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | (~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP1(X2,X0,X1)))),
% 1.38/0.58    inference(nnf_transformation,[],[f27])).
% 1.38/0.58  fof(f683,plain,(
% 1.38/0.58    ( ! [X0,X1] : (sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1) | v2_struct_0(X0) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~v10_lattices(X0)) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f682,f96])).
% 1.38/0.58  fof(f96,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f55])).
% 1.38/0.58  fof(f55,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r3_lattices(X1,sK15(X0,X1,X2),X0) & r3_lattice3(X1,sK15(X0,X1,X2),X2) & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 1.38/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f53,f54])).
% 1.38/0.58  fof(f54,plain,(
% 1.38/0.58    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r3_lattices(X1,sK15(X0,X1,X2),X0) & r3_lattice3(X1,sK15(X0,X1,X2),X2) & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))))),
% 1.38/0.58    introduced(choice_axiom,[])).
% 1.38/0.58  fof(f53,plain,(
% 1.38/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 1.38/0.58    inference(rectify,[],[f52])).
% 1.38/0.58  fof(f52,plain,(
% 1.38/0.58    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 1.38/0.58    inference(nnf_transformation,[],[f26])).
% 1.38/0.58  fof(f682,plain,(
% 1.38/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~v10_lattices(X0) | ~m1_subset_1(sK15(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1),u1_struct_0(X0))) )),
% 1.38/0.58    inference(duplicate_literal_removal,[],[f676])).
% 1.38/0.58  fof(f676,plain,(
% 1.38/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~m1_subset_1(sK15(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1),u1_struct_0(X0)) | sP0(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1)) )),
% 1.38/0.58    inference(resolution,[],[f536,f97])).
% 1.38/0.58  fof(f97,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK15(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f55])).
% 1.38/0.58  fof(f536,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X1,sK15(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3),X2) | v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~l3_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X0) | ~m1_subset_1(sK15(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3),u1_struct_0(X1))) )),
% 1.38/0.58    inference(resolution,[],[f436,f134])).
% 1.38/0.58  fof(f134,plain,(
% 1.38/0.58    ( ! [X0,X3,X1] : (sP10(X0,X1,X3) | ~r3_lattice3(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 1.38/0.58    inference(equality_resolution,[],[f130])).
% 1.38/0.58  fof(f130,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (sP10(X0,X1,X2) | ~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 1.38/0.58    inference(cnf_transformation,[],[f79])).
% 1.38/0.58  fof(f436,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (~sP10(X2,X1,sK15(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3)) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3) | ~v4_lattice3(X0) | ~l3_lattices(X0) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 1.38/0.58    inference(resolution,[],[f269,f131])).
% 1.38/0.58  fof(f269,plain,(
% 1.38/0.58    ( ! [X2,X0,X3,X1] : (~sP11(sK15(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3),X1,X2) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3) | ~sP10(X2,X1,sK15(k15_lattice3(X0,a_2_1_lattice3(X1,X2)),X0,X3)) | ~l3_lattices(X0)) )),
% 1.38/0.58    inference(resolution,[],[f230,f126])).
% 1.38/0.58  fof(f126,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP10(X2,X1,X0) | ~sP11(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f75])).
% 1.38/0.58  fof(f230,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK15(k15_lattice3(X0,X1),X0,X2),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,X1),X0,X2)) )),
% 1.38/0.58    inference(subsumption_resolution,[],[f228,f96])).
% 1.38/0.58  fof(f228,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK15(k15_lattice3(X0,X1),X0,X2),X1) | ~m1_subset_1(sK15(k15_lattice3(X0,X1),X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP0(k15_lattice3(X0,X1),X0,X2)) )),
% 1.38/0.58    inference(resolution,[],[f88,f98])).
% 1.38/0.58  fof(f98,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (~r3_lattices(X1,sK15(X0,X1,X2),X0) | sP0(X0,X1,X2)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f55])).
% 1.38/0.58  fof(f88,plain,(
% 1.38/0.58    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k15_lattice3(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.38/0.58    inference(cnf_transformation,[],[f13])).
% 1.38/0.58  fof(f13,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.38/0.58    inference(flattening,[],[f12])).
% 1.38/0.58  fof(f12,plain,(
% 1.38/0.58    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.38/0.58    inference(ennf_transformation,[],[f7])).
% 1.38/0.58  fof(f7,axiom,(
% 1.38/0.58    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 1.38/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
% 1.38/0.58  fof(f758,plain,(
% 1.38/0.58    spl20_4),
% 1.38/0.58    inference(avatar_contradiction_clause,[],[f757])).
% 1.38/0.58  fof(f757,plain,(
% 1.38/0.58    $false | spl20_4),
% 1.38/0.58    inference(subsumption_resolution,[],[f756,f84])).
% 1.38/0.58  fof(f756,plain,(
% 1.38/0.58    ~m1_subset_1(sK13,u1_struct_0(sK12)) | spl20_4),
% 1.38/0.58    inference(subsumption_resolution,[],[f755,f86])).
% 1.38/0.58  fof(f755,plain,(
% 1.38/0.58    ~r3_lattice3(sK12,sK13,sK14) | ~m1_subset_1(sK13,u1_struct_0(sK12)) | spl20_4),
% 1.38/0.58    inference(resolution,[],[f749,f134])).
% 1.38/0.58  fof(f749,plain,(
% 1.38/0.58    ~sP10(sK14,sK12,sK13) | spl20_4),
% 1.38/0.58    inference(avatar_component_clause,[],[f747])).
% 1.38/0.58  fof(f747,plain,(
% 1.38/0.58    spl20_4 <=> sP10(sK14,sK12,sK13)),
% 1.38/0.58    introduced(avatar_definition,[new_symbols(naming,[spl20_4])])).
% 1.38/0.58  fof(f754,plain,(
% 1.38/0.58    spl20_3),
% 1.38/0.58    inference(avatar_contradiction_clause,[],[f753])).
% 1.38/0.58  fof(f753,plain,(
% 1.38/0.58    $false | spl20_3),
% 1.38/0.58    inference(subsumption_resolution,[],[f752,f80])).
% 1.38/0.58  fof(f752,plain,(
% 1.38/0.58    v2_struct_0(sK12) | spl20_3),
% 1.38/0.58    inference(subsumption_resolution,[],[f751,f83])).
% 1.38/0.58  fof(f751,plain,(
% 1.38/0.58    ~l3_lattices(sK12) | v2_struct_0(sK12) | spl20_3),
% 1.38/0.58    inference(resolution,[],[f745,f131])).
% 1.38/0.58  fof(f745,plain,(
% 1.38/0.58    ~sP11(sK13,sK12,sK14) | spl20_3),
% 1.38/0.58    inference(avatar_component_clause,[],[f743])).
% 1.38/0.58  fof(f743,plain,(
% 1.38/0.58    spl20_3 <=> sP11(sK13,sK12,sK14)),
% 1.38/0.58    introduced(avatar_definition,[new_symbols(naming,[spl20_3])])).
% 1.38/0.58  fof(f750,plain,(
% 1.38/0.58    ~spl20_3 | ~spl20_4 | spl20_1),
% 1.38/0.58    inference(avatar_split_clause,[],[f741,f731,f747,f743])).
% 1.38/0.58  fof(f741,plain,(
% 1.38/0.58    ~sP10(sK14,sK12,sK13) | ~sP11(sK13,sK12,sK14) | spl20_1),
% 1.38/0.58    inference(resolution,[],[f733,f126])).
% 1.38/0.58  fof(f733,plain,(
% 1.38/0.58    ~r2_hidden(sK13,a_2_1_lattice3(sK12,sK14)) | spl20_1),
% 1.38/0.58    inference(avatar_component_clause,[],[f731])).
% 1.38/0.58  % SZS output end Proof for theBenchmark
% 1.38/0.58  % (3761)------------------------------
% 1.38/0.58  % (3761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.58  % (3761)Termination reason: Refutation
% 1.38/0.58  
% 1.38/0.58  % (3761)Memory used [KB]: 6524
% 1.38/0.58  % (3761)Time elapsed: 0.174 s
% 1.38/0.58  % (3761)------------------------------
% 1.38/0.58  % (3761)------------------------------
% 1.38/0.59  % (3752)Success in time 0.226 s
%------------------------------------------------------------------------------
