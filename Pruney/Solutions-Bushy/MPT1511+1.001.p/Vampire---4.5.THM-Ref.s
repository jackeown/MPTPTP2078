%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1511+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:59 EST 2020

% Result     : Theorem 1.59s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  236 ( 740 expanded)
%              Number of leaves         :   34 ( 235 expanded)
%              Depth                    :   28
%              Number of atoms          : 1216 (4656 expanded)
%              Number of equality atoms :   74 ( 917 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f493,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f313,f320,f346,f359,f364,f369,f481,f488,f492])).

fof(f492,plain,
    ( ~ spl15_4
    | spl15_10 ),
    inference(avatar_contradiction_clause,[],[f491])).

fof(f491,plain,
    ( $false
    | ~ spl15_4
    | spl15_10 ),
    inference(subsumption_resolution,[],[f490,f75])).

fof(f75,plain,(
    m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( ( sK10 != k16_lattice3(sK9,a_2_4_lattice3(sK9,sK10))
      | sK10 != k15_lattice3(sK9,a_2_3_lattice3(sK9,sK10)) )
    & m1_subset_1(sK10,u1_struct_0(sK9))
    & l3_lattices(sK9)
    & v4_lattice3(sK9)
    & v10_lattices(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10])],[f13,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) != X1
              | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) != X1 )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k16_lattice3(sK9,a_2_4_lattice3(sK9,X1)) != X1
            | k15_lattice3(sK9,a_2_3_lattice3(sK9,X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(sK9)) )
      & l3_lattices(sK9)
      & v4_lattice3(sK9)
      & v10_lattices(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] :
        ( ( k16_lattice3(sK9,a_2_4_lattice3(sK9,X1)) != X1
          | k15_lattice3(sK9,a_2_3_lattice3(sK9,X1)) != X1 )
        & m1_subset_1(X1,u1_struct_0(sK9)) )
   => ( ( sK10 != k16_lattice3(sK9,a_2_4_lattice3(sK9,sK10))
        | sK10 != k15_lattice3(sK9,a_2_3_lattice3(sK9,sK10)) )
      & m1_subset_1(sK10,u1_struct_0(sK9)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) != X1
            | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) != X1
            | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
              & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).

fof(f490,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ spl15_4
    | spl15_10 ),
    inference(subsumption_resolution,[],[f489,f383])).

fof(f383,plain,
    ( r3_lattices(sK9,sK10,sK10)
    | ~ spl15_4 ),
    inference(resolution,[],[f311,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | r3_lattices(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X1,X2,X0)
      | ~ sP5(X0,X1,X2)
      | ~ sP5(X0,X1,X2) ) ),
    inference(superposition,[],[f108,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( sK13(X0,X1,X2) = X2
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattices(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r3_lattices(X1,sK13(X0,X1,X2),X0)
          & sK13(X0,X1,X2) = X2
          & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f63,f64])).

fof(f64,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattices(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,sK13(X0,X1,X2),X0)
        & sK13(X0,X1,X2) = X2
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattices(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattices(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ( sP5(X2,X1,X0)
        | ! [X3] :
            ( ~ r3_lattices(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r3_lattices(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP5(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( sP5(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattices(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X1,sK13(X0,X1,X2),X0)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f311,plain,
    ( sP5(sK10,sK9,sK10)
    | ~ spl15_4 ),
    inference(avatar_component_clause,[],[f310])).

fof(f310,plain,
    ( spl15_4
  <=> sP5(sK10,sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_4])])).

fof(f489,plain,
    ( ~ r3_lattices(sK9,sK10,sK10)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | spl15_10 ),
    inference(resolution,[],[f480,f119])).

fof(f119,plain,(
    ! [X0,X3,X1] :
      ( sP7(X0,X1,X3)
      | ~ r3_lattices(X1,X0,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f116])).

fof(f116,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X0,X1,X2)
      | ~ r3_lattices(X1,X0,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattices(X1,X0,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r3_lattices(X1,X0,sK14(X0,X1,X2))
          & sK14(X0,X1,X2) = X2
          & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f68,f69])).

fof(f69,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattices(X1,X0,X4)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X0,sK14(X0,X1,X2))
        & sK14(X0,X1,X2) = X2
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattices(X1,X0,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattices(X1,X0,X4)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ( sP7(X2,X1,X0)
        | ! [X3] :
            ( ~ r3_lattices(X1,X2,X3)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP7(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( sP7(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattices(X1,X2,X3)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f480,plain,
    ( ~ sP7(sK10,sK9,sK10)
    | spl15_10 ),
    inference(avatar_component_clause,[],[f478])).

fof(f478,plain,
    ( spl15_10
  <=> sP7(sK10,sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_10])])).

fof(f488,plain,(
    spl15_9 ),
    inference(avatar_contradiction_clause,[],[f487])).

fof(f487,plain,
    ( $false
    | spl15_9 ),
    inference(subsumption_resolution,[],[f486,f71])).

fof(f71,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f48])).

fof(f486,plain,
    ( v2_struct_0(sK9)
    | spl15_9 ),
    inference(subsumption_resolution,[],[f485,f72])).

fof(f72,plain,(
    v10_lattices(sK9) ),
    inference(cnf_transformation,[],[f48])).

fof(f485,plain,
    ( ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | spl15_9 ),
    inference(subsumption_resolution,[],[f484,f73])).

fof(f73,plain,(
    v4_lattice3(sK9) ),
    inference(cnf_transformation,[],[f48])).

fof(f484,plain,
    ( ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | spl15_9 ),
    inference(subsumption_resolution,[],[f483,f74])).

fof(f74,plain,(
    l3_lattices(sK9) ),
    inference(cnf_transformation,[],[f48])).

fof(f483,plain,
    ( ~ l3_lattices(sK9)
    | ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | spl15_9 ),
    inference(subsumption_resolution,[],[f482,f75])).

fof(f482,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | spl15_9 ),
    inference(resolution,[],[f476,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( sP8(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( sP8(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f31,f44,f43])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> sP7(X2,X1,X0) )
      | ~ sP8(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_4_lattice3)).

fof(f476,plain,
    ( ~ sP8(sK10,sK9,sK10)
    | spl15_9 ),
    inference(avatar_component_clause,[],[f474])).

fof(f474,plain,
    ( spl15_9
  <=> sP8(sK10,sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_9])])).

fof(f481,plain,
    ( ~ spl15_9
    | ~ spl15_10
    | spl15_2 ),
    inference(avatar_split_clause,[],[f472,f126,f478,f474])).

fof(f126,plain,
    ( spl15_2
  <=> sK10 = k16_lattice3(sK9,a_2_4_lattice3(sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_2])])).

fof(f472,plain,
    ( ~ sP7(sK10,sK9,sK10)
    | ~ sP8(sK10,sK9,sK10)
    | spl15_2 ),
    inference(resolution,[],[f464,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ sP7(X2,X1,X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ~ sP7(X2,X1,X0) )
        & ( sP7(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ sP8(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f464,plain,
    ( ~ r2_hidden(sK10,a_2_4_lattice3(sK9,sK10))
    | spl15_2 ),
    inference(subsumption_resolution,[],[f463,f74])).

fof(f463,plain,
    ( ~ l3_lattices(sK9)
    | ~ r2_hidden(sK10,a_2_4_lattice3(sK9,sK10))
    | spl15_2 ),
    inference(subsumption_resolution,[],[f462,f75])).

fof(f462,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | ~ r2_hidden(sK10,a_2_4_lattice3(sK9,sK10))
    | spl15_2 ),
    inference(subsumption_resolution,[],[f461,f71])).

fof(f461,plain,
    ( v2_struct_0(sK9)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | ~ r2_hidden(sK10,a_2_4_lattice3(sK9,sK10))
    | spl15_2 ),
    inference(subsumption_resolution,[],[f460,f72])).

fof(f460,plain,
    ( ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | ~ r2_hidden(sK10,a_2_4_lattice3(sK9,sK10))
    | spl15_2 ),
    inference(subsumption_resolution,[],[f456,f73])).

fof(f456,plain,
    ( ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | ~ r2_hidden(sK10,a_2_4_lattice3(sK9,sK10))
    | spl15_2 ),
    inference(trivial_inequality_removal,[],[f455])).

fof(f455,plain,
    ( ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | sK10 != sK10
    | ~ r2_hidden(sK10,a_2_4_lattice3(sK9,sK10))
    | spl15_2 ),
    inference(duplicate_literal_removal,[],[f454])).

fof(f454,plain,
    ( ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | sK10 != sK10
    | ~ r2_hidden(sK10,a_2_4_lattice3(sK9,sK10))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | spl15_2 ),
    inference(resolution,[],[f451,f391])).

fof(f391,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK9,X0,a_2_4_lattice3(sK9,sK10))
        | sK10 != X0
        | ~ r2_hidden(X0,a_2_4_lattice3(sK9,sK10))
        | ~ m1_subset_1(X0,u1_struct_0(sK9)) )
    | spl15_2 ),
    inference(subsumption_resolution,[],[f390,f71])).

fof(f390,plain,
    ( ! [X0] :
        ( sK10 != X0
        | ~ r3_lattice3(sK9,X0,a_2_4_lattice3(sK9,sK10))
        | ~ r2_hidden(X0,a_2_4_lattice3(sK9,sK10))
        | ~ m1_subset_1(X0,u1_struct_0(sK9))
        | v2_struct_0(sK9) )
    | spl15_2 ),
    inference(subsumption_resolution,[],[f389,f72])).

fof(f389,plain,
    ( ! [X0] :
        ( sK10 != X0
        | ~ r3_lattice3(sK9,X0,a_2_4_lattice3(sK9,sK10))
        | ~ r2_hidden(X0,a_2_4_lattice3(sK9,sK10))
        | ~ m1_subset_1(X0,u1_struct_0(sK9))
        | ~ v10_lattices(sK9)
        | v2_struct_0(sK9) )
    | spl15_2 ),
    inference(subsumption_resolution,[],[f388,f73])).

fof(f388,plain,
    ( ! [X0] :
        ( sK10 != X0
        | ~ r3_lattice3(sK9,X0,a_2_4_lattice3(sK9,sK10))
        | ~ r2_hidden(X0,a_2_4_lattice3(sK9,sK10))
        | ~ m1_subset_1(X0,u1_struct_0(sK9))
        | ~ v4_lattice3(sK9)
        | ~ v10_lattices(sK9)
        | v2_struct_0(sK9) )
    | spl15_2 ),
    inference(subsumption_resolution,[],[f387,f74])).

fof(f387,plain,
    ( ! [X0] :
        ( sK10 != X0
        | ~ r3_lattice3(sK9,X0,a_2_4_lattice3(sK9,sK10))
        | ~ r2_hidden(X0,a_2_4_lattice3(sK9,sK10))
        | ~ m1_subset_1(X0,u1_struct_0(sK9))
        | ~ l3_lattices(sK9)
        | ~ v4_lattice3(sK9)
        | ~ v10_lattices(sK9)
        | v2_struct_0(sK9) )
    | spl15_2 ),
    inference(superposition,[],[f128,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | ~ r3_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
              | ~ r3_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k16_lattice3(X0,X2) = X1
              | ~ r3_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).

fof(f128,plain,
    ( sK10 != k16_lattice3(sK9,a_2_4_lattice3(sK9,sK10))
    | spl15_2 ),
    inference(avatar_component_clause,[],[f126])).

fof(f451,plain,(
    ! [X4,X3] :
      ( r3_lattice3(X3,X4,a_2_4_lattice3(X3,X4))
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l3_lattices(X3) ) ),
    inference(subsumption_resolution,[],[f450,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP2(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f35,f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP1(X1,X0,X2) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(f450,plain,(
    ! [X4,X3] :
      ( ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | r3_lattice3(X3,X4,a_2_4_lattice3(X3,X4))
      | ~ sP2(X3,X4) ) ),
    inference(resolution,[],[f448,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X1,X0,X2)
      | r3_lattice3(X0,X1,X2)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP1(X1,X0,X2) )
          & ( sP1(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f448,plain,(
    ! [X0,X1] :
      ( sP1(X0,X1,a_2_4_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f447])).

fof(f447,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | sP1(X0,X1,a_2_4_lattice3(X1,X0))
      | sP1(X0,X1,a_2_4_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f255,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK11(X0,X1,X2))
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK11(X0,X1,X2))
          & r2_hidden(sK11(X0,X1,X2),X2)
          & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK11(X0,X1,X2))
        & r2_hidden(sK11(X0,X1,X2),X2)
        & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X1,X3)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f255,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X2,X3,sK11(X0,X1,a_2_4_lattice3(X2,X3)))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | sP1(X0,X1,a_2_4_lattice3(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f254,f133])).

fof(f133,plain,(
    ! [X3] :
      ( v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3) ) ),
    inference(resolution,[],[f84,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f84,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f15,f32])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f1])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f254,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,a_2_4_lattice3(X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ v6_lattices(X2)
      | r1_lattices(X2,X3,sK11(X0,X1,a_2_4_lattice3(X2,X3))) ) ),
    inference(subsumption_resolution,[],[f253,f135])).

fof(f135,plain,(
    ! [X5] :
      ( v8_lattices(X5)
      | v2_struct_0(X5)
      | ~ l3_lattices(X5)
      | ~ v10_lattices(X5) ) ),
    inference(resolution,[],[f84,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f253,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,a_2_4_lattice3(X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ v8_lattices(X2)
      | ~ v6_lattices(X2)
      | r1_lattices(X2,X3,sK11(X0,X1,a_2_4_lattice3(X2,X3))) ) ),
    inference(subsumption_resolution,[],[f252,f136])).

fof(f136,plain,(
    ! [X6] :
      ( v9_lattices(X6)
      | v2_struct_0(X6)
      | ~ l3_lattices(X6)
      | ~ v10_lattices(X6) ) ),
    inference(resolution,[],[f84,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f252,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,a_2_4_lattice3(X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ v9_lattices(X2)
      | ~ v8_lattices(X2)
      | ~ v6_lattices(X2)
      | r1_lattices(X2,X3,sK11(X0,X1,a_2_4_lattice3(X2,X3))) ) ),
    inference(duplicate_literal_removal,[],[f245])).

fof(f245,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,a_2_4_lattice3(X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v9_lattices(X2)
      | ~ v8_lattices(X2)
      | ~ v6_lattices(X2)
      | v2_struct_0(X2)
      | r1_lattices(X2,X3,sK11(X0,X1,a_2_4_lattice3(X2,X3))) ) ),
    inference(resolution,[],[f207,f219])).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | r1_lattices(X1,X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X1,X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP7(X0,X1,X2)
      | ~ sP7(X0,X1,X2) ) ),
    inference(superposition,[],[f214,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( sK14(X0,X1,X2) = X2
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f214,plain,(
    ! [X4,X5,X3] :
      ( r1_lattices(X3,X4,sK14(X4,X3,X5))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ v8_lattices(X3)
      | ~ v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ sP7(X4,X3,X5) ) ),
    inference(subsumption_resolution,[],[f210,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1))
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f210,plain,(
    ! [X4,X5,X3] :
      ( r1_lattices(X3,X4,sK14(X4,X3,X5))
      | ~ m1_subset_1(sK14(X4,X3,X5),u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ v8_lattices(X3)
      | ~ v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ sP7(X4,X3,X5) ) ),
    inference(resolution,[],[f102,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X1,X0,sK14(X0,X1,X2))
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f102,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f207,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X0,X1,sK11(X2,X3,a_2_4_lattice3(X1,X0)))
      | sP1(X2,X3,a_2_4_lattice3(X1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f171,f117])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP8(sK11(X2,X3,a_2_4_lattice3(X1,X0)),X1,X0)
      | sP7(X0,X1,sK11(X2,X3,a_2_4_lattice3(X1,X0)))
      | sP1(X2,X3,a_2_4_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f111,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK11(X0,X1,X2),X2)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | sP7(X2,X1,X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f369,plain,(
    spl15_7 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | spl15_7 ),
    inference(subsumption_resolution,[],[f367,f72])).

fof(f367,plain,
    ( ~ v10_lattices(sK9)
    | spl15_7 ),
    inference(subsumption_resolution,[],[f366,f74])).

fof(f366,plain,
    ( ~ l3_lattices(sK9)
    | ~ v10_lattices(sK9)
    | spl15_7 ),
    inference(subsumption_resolution,[],[f365,f71])).

fof(f365,plain,
    ( v2_struct_0(sK9)
    | ~ l3_lattices(sK9)
    | ~ v10_lattices(sK9)
    | spl15_7 ),
    inference(resolution,[],[f345,f136])).

fof(f345,plain,
    ( ~ v9_lattices(sK9)
    | spl15_7 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl15_7
  <=> v9_lattices(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_7])])).

fof(f364,plain,(
    spl15_6 ),
    inference(avatar_contradiction_clause,[],[f363])).

fof(f363,plain,
    ( $false
    | spl15_6 ),
    inference(subsumption_resolution,[],[f362,f72])).

fof(f362,plain,
    ( ~ v10_lattices(sK9)
    | spl15_6 ),
    inference(subsumption_resolution,[],[f361,f74])).

fof(f361,plain,
    ( ~ l3_lattices(sK9)
    | ~ v10_lattices(sK9)
    | spl15_6 ),
    inference(subsumption_resolution,[],[f360,f71])).

fof(f360,plain,
    ( v2_struct_0(sK9)
    | ~ l3_lattices(sK9)
    | ~ v10_lattices(sK9)
    | spl15_6 ),
    inference(resolution,[],[f341,f135])).

fof(f341,plain,
    ( ~ v8_lattices(sK9)
    | spl15_6 ),
    inference(avatar_component_clause,[],[f339])).

fof(f339,plain,
    ( spl15_6
  <=> v8_lattices(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_6])])).

fof(f359,plain,(
    spl15_5 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | spl15_5 ),
    inference(subsumption_resolution,[],[f357,f72])).

fof(f357,plain,
    ( ~ v10_lattices(sK9)
    | spl15_5 ),
    inference(subsumption_resolution,[],[f356,f74])).

fof(f356,plain,
    ( ~ l3_lattices(sK9)
    | ~ v10_lattices(sK9)
    | spl15_5 ),
    inference(subsumption_resolution,[],[f355,f71])).

fof(f355,plain,
    ( v2_struct_0(sK9)
    | ~ l3_lattices(sK9)
    | ~ v10_lattices(sK9)
    | spl15_5 ),
    inference(resolution,[],[f337,f133])).

fof(f337,plain,
    ( ~ v6_lattices(sK9)
    | spl15_5 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl15_5
  <=> v6_lattices(sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_5])])).

fof(f346,plain,
    ( ~ spl15_5
    | ~ spl15_6
    | ~ spl15_7
    | spl15_4 ),
    inference(avatar_split_clause,[],[f333,f310,f343,f339,f335])).

fof(f333,plain,
    ( ~ v9_lattices(sK9)
    | ~ v8_lattices(sK9)
    | ~ v6_lattices(sK9)
    | spl15_4 ),
    inference(subsumption_resolution,[],[f332,f71])).

fof(f332,plain,
    ( ~ v9_lattices(sK9)
    | ~ v8_lattices(sK9)
    | ~ v6_lattices(sK9)
    | v2_struct_0(sK9)
    | spl15_4 ),
    inference(subsumption_resolution,[],[f331,f74])).

fof(f331,plain,
    ( ~ l3_lattices(sK9)
    | ~ v9_lattices(sK9)
    | ~ v8_lattices(sK9)
    | ~ v6_lattices(sK9)
    | v2_struct_0(sK9)
    | spl15_4 ),
    inference(subsumption_resolution,[],[f328,f75])).

fof(f328,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | ~ v9_lattices(sK9)
    | ~ v8_lattices(sK9)
    | ~ v6_lattices(sK9)
    | v2_struct_0(sK9)
    | spl15_4 ),
    inference(resolution,[],[f322,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( r3_lattices(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(condensation,[],[f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r3_lattices(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r3_lattices)).

fof(f322,plain,
    ( ~ r3_lattices(sK9,sK10,sK10)
    | spl15_4 ),
    inference(subsumption_resolution,[],[f321,f75])).

fof(f321,plain,
    ( ~ r3_lattices(sK9,sK10,sK10)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | spl15_4 ),
    inference(resolution,[],[f312,f118])).

fof(f118,plain,(
    ! [X0,X3,X1] :
      ( sP5(X0,X1,X3)
      | ~ r3_lattices(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X0,X1,X2)
      | ~ r3_lattices(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f312,plain,
    ( ~ sP5(sK10,sK9,sK10)
    | spl15_4 ),
    inference(avatar_component_clause,[],[f310])).

fof(f320,plain,(
    spl15_3 ),
    inference(avatar_contradiction_clause,[],[f319])).

fof(f319,plain,
    ( $false
    | spl15_3 ),
    inference(subsumption_resolution,[],[f318,f71])).

fof(f318,plain,
    ( v2_struct_0(sK9)
    | spl15_3 ),
    inference(subsumption_resolution,[],[f317,f72])).

fof(f317,plain,
    ( ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | spl15_3 ),
    inference(subsumption_resolution,[],[f316,f73])).

fof(f316,plain,
    ( ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | spl15_3 ),
    inference(subsumption_resolution,[],[f315,f74])).

fof(f315,plain,
    ( ~ l3_lattices(sK9)
    | ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | spl15_3 ),
    inference(subsumption_resolution,[],[f314,f75])).

fof(f314,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | spl15_3 ),
    inference(resolution,[],[f308,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( sP6(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( sP6(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f29,f41,f40])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
      <=> sP5(X2,X1,X0) )
      | ~ sP6(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattices(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_3_lattice3)).

fof(f308,plain,
    ( ~ sP6(sK10,sK9,sK10)
    | spl15_3 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl15_3
  <=> sP6(sK10,sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_3])])).

fof(f313,plain,
    ( ~ spl15_3
    | ~ spl15_4
    | spl15_1 ),
    inference(avatar_split_clause,[],[f304,f122,f310,f306])).

fof(f122,plain,
    ( spl15_1
  <=> sK10 = k15_lattice3(sK9,a_2_3_lattice3(sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_1])])).

fof(f304,plain,
    ( ~ sP5(sK10,sK9,sK10)
    | ~ sP6(sK10,sK9,sK10)
    | spl15_1 ),
    inference(resolution,[],[f303,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
      | ~ sP5(X2,X1,X0)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_3_lattice3(X1,X2))
          | ~ sP5(X2,X1,X0) )
        & ( sP5(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_3_lattice3(X1,X2)) ) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f303,plain,
    ( ~ r2_hidden(sK10,a_2_3_lattice3(sK9,sK10))
    | spl15_1 ),
    inference(subsumption_resolution,[],[f302,f74])).

fof(f302,plain,
    ( ~ l3_lattices(sK9)
    | ~ r2_hidden(sK10,a_2_3_lattice3(sK9,sK10))
    | spl15_1 ),
    inference(subsumption_resolution,[],[f301,f75])).

fof(f301,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | ~ r2_hidden(sK10,a_2_3_lattice3(sK9,sK10))
    | spl15_1 ),
    inference(subsumption_resolution,[],[f300,f71])).

fof(f300,plain,
    ( v2_struct_0(sK9)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | ~ r2_hidden(sK10,a_2_3_lattice3(sK9,sK10))
    | spl15_1 ),
    inference(subsumption_resolution,[],[f299,f72])).

fof(f299,plain,
    ( ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | ~ r2_hidden(sK10,a_2_3_lattice3(sK9,sK10))
    | spl15_1 ),
    inference(subsumption_resolution,[],[f296,f73])).

fof(f296,plain,
    ( ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | ~ r2_hidden(sK10,a_2_3_lattice3(sK9,sK10))
    | spl15_1 ),
    inference(trivial_inequality_removal,[],[f295])).

fof(f295,plain,
    ( ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | sK10 != sK10
    | ~ r2_hidden(sK10,a_2_3_lattice3(sK9,sK10))
    | spl15_1 ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,
    ( ~ v4_lattice3(sK9)
    | ~ v10_lattices(sK9)
    | v2_struct_0(sK9)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ l3_lattices(sK9)
    | sK10 != sK10
    | ~ r2_hidden(sK10,a_2_3_lattice3(sK9,sK10))
    | ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | spl15_1 ),
    inference(resolution,[],[f291,f202])).

fof(f202,plain,
    ( ! [X0] :
        ( ~ r4_lattice3(sK9,X0,a_2_3_lattice3(sK9,sK10))
        | sK10 != X0
        | ~ r2_hidden(X0,a_2_3_lattice3(sK9,sK10))
        | ~ m1_subset_1(X0,u1_struct_0(sK9)) )
    | spl15_1 ),
    inference(subsumption_resolution,[],[f201,f71])).

fof(f201,plain,
    ( ! [X0] :
        ( sK10 != X0
        | ~ r4_lattice3(sK9,X0,a_2_3_lattice3(sK9,sK10))
        | ~ r2_hidden(X0,a_2_3_lattice3(sK9,sK10))
        | ~ m1_subset_1(X0,u1_struct_0(sK9))
        | v2_struct_0(sK9) )
    | spl15_1 ),
    inference(subsumption_resolution,[],[f200,f72])).

fof(f200,plain,
    ( ! [X0] :
        ( sK10 != X0
        | ~ r4_lattice3(sK9,X0,a_2_3_lattice3(sK9,sK10))
        | ~ r2_hidden(X0,a_2_3_lattice3(sK9,sK10))
        | ~ m1_subset_1(X0,u1_struct_0(sK9))
        | ~ v10_lattices(sK9)
        | v2_struct_0(sK9) )
    | spl15_1 ),
    inference(subsumption_resolution,[],[f199,f73])).

fof(f199,plain,
    ( ! [X0] :
        ( sK10 != X0
        | ~ r4_lattice3(sK9,X0,a_2_3_lattice3(sK9,sK10))
        | ~ r2_hidden(X0,a_2_3_lattice3(sK9,sK10))
        | ~ m1_subset_1(X0,u1_struct_0(sK9))
        | ~ v4_lattice3(sK9)
        | ~ v10_lattices(sK9)
        | v2_struct_0(sK9) )
    | spl15_1 ),
    inference(subsumption_resolution,[],[f197,f74])).

fof(f197,plain,
    ( ! [X0] :
        ( sK10 != X0
        | ~ r4_lattice3(sK9,X0,a_2_3_lattice3(sK9,sK10))
        | ~ r2_hidden(X0,a_2_3_lattice3(sK9,sK10))
        | ~ m1_subset_1(X0,u1_struct_0(sK9))
        | ~ l3_lattices(sK9)
        | ~ v4_lattice3(sK9)
        | ~ v10_lattices(sK9)
        | v2_struct_0(sK9) )
    | spl15_1 ),
    inference(superposition,[],[f124,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X2) = X1
      | ~ r4_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k15_lattice3(X0,X2) = X1
              | ~ r4_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k15_lattice3(X0,X2) = X1
              | ~ r4_lattice3(X0,X1,X2)
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_lattice3)).

fof(f124,plain,
    ( sK10 != k15_lattice3(sK9,a_2_3_lattice3(sK9,sK10))
    | spl15_1 ),
    inference(avatar_component_clause,[],[f122])).

fof(f291,plain,(
    ! [X4,X3] :
      ( r4_lattice3(X3,X4,a_2_3_lattice3(X3,X4))
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l3_lattices(X3) ) ),
    inference(subsumption_resolution,[],[f290,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP4(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP4(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f23,f38,f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP3(X1,X0,X2) )
      | ~ sP4(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f290,plain,(
    ! [X4,X3] :
      ( ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | r4_lattice3(X3,X4,a_2_3_lattice3(X3,X4))
      | ~ sP4(X3,X4) ) ),
    inference(resolution,[],[f288,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP3(X1,X0,X2) )
          & ( sP3(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP4(X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f288,plain,(
    ! [X0,X1] :
      ( sP3(X0,X1,a_2_3_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f287])).

fof(f287,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | sP3(X0,X1,a_2_3_lattice3(X1,X0))
      | sP3(X0,X1,a_2_3_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f244,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK12(X0,X1,X2),X0)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK12(X0,X1,X2),X0)
          & r2_hidden(sK12(X0,X1,X2),X2)
          & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f57,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK12(X0,X1,X2),X0)
        & r2_hidden(sK12(X0,X1,X2),X2)
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X3,X1)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X3,X1)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f244,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X2,sK12(X0,X1,a_2_3_lattice3(X2,X3)),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | sP3(X0,X1,a_2_3_lattice3(X2,X3)) ) ),
    inference(subsumption_resolution,[],[f243,f133])).

fof(f243,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,a_2_3_lattice3(X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ v6_lattices(X2)
      | r1_lattices(X2,sK12(X0,X1,a_2_3_lattice3(X2,X3)),X3) ) ),
    inference(subsumption_resolution,[],[f242,f135])).

fof(f242,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,a_2_3_lattice3(X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ v8_lattices(X2)
      | ~ v6_lattices(X2)
      | r1_lattices(X2,sK12(X0,X1,a_2_3_lattice3(X2,X3)),X3) ) ),
    inference(subsumption_resolution,[],[f241,f136])).

fof(f241,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,a_2_3_lattice3(X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ v9_lattices(X2)
      | ~ v8_lattices(X2)
      | ~ v6_lattices(X2)
      | r1_lattices(X2,sK12(X0,X1,a_2_3_lattice3(X2,X3)),X3) ) ),
    inference(duplicate_literal_removal,[],[f234])).

fof(f234,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X0,X1,a_2_3_lattice3(X2,X3))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v9_lattices(X2)
      | ~ v8_lattices(X2)
      | ~ v6_lattices(X2)
      | v2_struct_0(X2)
      | r1_lattices(X2,sK12(X0,X1,a_2_3_lattice3(X2,X3)),X3) ) ),
    inference(resolution,[],[f206,f216])).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | r1_lattices(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f215])).

fof(f215,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP5(X0,X1,X2)
      | ~ sP5(X0,X1,X2) ) ),
    inference(superposition,[],[f213,f107])).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,sK13(X1,X0,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ sP5(X1,X0,X2) ) ),
    inference(subsumption_resolution,[],[f209,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,sK13(X1,X0,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK13(X1,X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ sP5(X1,X0,X2) ) ),
    inference(resolution,[],[f102,f108])).

fof(f206,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X0,X1,sK12(X2,X3,a_2_3_lattice3(X1,X0)))
      | sP3(X2,X3,a_2_3_lattice3(X1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f168,f110])).

fof(f168,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ sP6(sK12(X6,X7,a_2_3_lattice3(X5,X4)),X5,X4)
      | sP5(X4,X5,sK12(X6,X7,a_2_3_lattice3(X5,X4)))
      | sP3(X6,X7,a_2_3_lattice3(X5,X4)) ) ),
    inference(resolution,[],[f104,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK12(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_3_lattice3(X1,X2))
      | sP5(X2,X1,X0)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f129,plain,
    ( ~ spl15_1
    | ~ spl15_2 ),
    inference(avatar_split_clause,[],[f76,f126,f122])).

fof(f76,plain,
    ( sK10 != k16_lattice3(sK9,a_2_4_lattice3(sK9,sK10))
    | sK10 != k15_lattice3(sK9,a_2_3_lattice3(sK9,sK10)) ),
    inference(cnf_transformation,[],[f48])).

%------------------------------------------------------------------------------
