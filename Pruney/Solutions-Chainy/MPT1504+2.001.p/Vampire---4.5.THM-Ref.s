%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  294 (1243 expanded)
%              Number of leaves         :   42 ( 404 expanded)
%              Depth                    :   43
%              Number of atoms          : 1452 (6593 expanded)
%              Number of equality atoms :   64 ( 889 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f855,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f447,f463,f468,f473,f536,f543,f555,f582,f591,f605,f617,f854])).

fof(f854,plain,
    ( ~ spl23_4
    | ~ spl23_5
    | ~ spl23_7
    | ~ spl23_12 ),
    inference(avatar_contradiction_clause,[],[f853])).

fof(f853,plain,
    ( $false
    | ~ spl23_4
    | ~ spl23_5
    | ~ spl23_7
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f852,f89])).

fof(f89,plain,(
    ~ v2_struct_0(sK14) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,
    ( k15_lattice3(sK14,sK15) != k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15))
    & l3_lattices(sK14)
    & v4_lattice3(sK14)
    & v10_lattices(sK14)
    & ~ v2_struct_0(sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15])],[f11,f47,f46])).

fof(f46,plain,
    ( ? [X0] :
        ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] : k15_lattice3(sK14,X1) != k16_lattice3(sK14,a_2_2_lattice3(sK14,X1))
      & l3_lattices(sK14)
      & v4_lattice3(sK14)
      & v10_lattices(sK14)
      & ~ v2_struct_0(sK14) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X1] : k15_lattice3(sK14,X1) != k16_lattice3(sK14,a_2_2_lattice3(sK14,X1))
   => k15_lattice3(sK14,sK15) != k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
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
       => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

fof(f852,plain,
    ( v2_struct_0(sK14)
    | ~ spl23_4
    | ~ spl23_5
    | ~ spl23_7
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f851,f90])).

fof(f90,plain,(
    v10_lattices(sK14) ),
    inference(cnf_transformation,[],[f48])).

fof(f851,plain,
    ( ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ spl23_4
    | ~ spl23_5
    | ~ spl23_7
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f850,f91])).

fof(f91,plain,(
    v4_lattice3(sK14) ),
    inference(cnf_transformation,[],[f48])).

fof(f850,plain,
    ( ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ spl23_4
    | ~ spl23_5
    | ~ spl23_7
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f849,f92])).

fof(f92,plain,(
    l3_lattices(sK14) ),
    inference(cnf_transformation,[],[f48])).

fof(f849,plain,
    ( ~ l3_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ spl23_4
    | ~ spl23_5
    | ~ spl23_7
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f848,f549])).

fof(f549,plain,
    ( m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ spl23_12 ),
    inference(avatar_component_clause,[],[f548])).

fof(f548,plain,
    ( spl23_12
  <=> m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_12])])).

fof(f848,plain,
    ( ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ l3_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ spl23_4
    | ~ spl23_5
    | ~ spl23_7
    | ~ spl23_12 ),
    inference(duplicate_literal_removal,[],[f847])).

fof(f847,plain,
    ( ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ l3_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ spl23_4
    | ~ spl23_5
    | ~ spl23_7
    | ~ spl23_12 ),
    inference(resolution,[],[f829,f217])).

fof(f217,plain,(
    ! [X0,X1] :
      ( sP5(X1,X0,k15_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f152,f150])).

fof(f150,plain,(
    ! [X2,X1] :
      ( ~ sP6(k15_lattice3(X1,X2),X1,X2)
      | sP5(X2,X1,k15_lattice3(X1,X2)) ) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X1,X0)
      | k15_lattice3(X1,X2) != X0
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( ( k15_lattice3(X1,X2) = X0
          | ~ sP5(X2,X1,X0) )
        & ( sP5(X2,X1,X0)
          | k15_lattice3(X1,X2) != X0 ) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ( ( k15_lattice3(X0,X1) = X2
          | ~ sP5(X1,X0,X2) )
        & ( sP5(X1,X0,X2)
          | k15_lattice3(X0,X1) != X2 ) )
      | ~ sP6(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ( k15_lattice3(X0,X1) = X2
      <=> sP5(X1,X0,X2) )
      | ~ sP6(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP6(X2,X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f34,f33,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0,X1)
    <=> ! [X3] :
          ( r1_lattices(X0,X2,X3)
          | ~ r4_lattice3(X0,X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( sP5(X1,X0,X2)
    <=> ( sP4(X2,X0,X1)
        & r4_lattice3(X0,X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

fof(f829,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14)) )
    | ~ spl23_4
    | ~ spl23_5
    | ~ spl23_7
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f828,f670])).

fof(f670,plain,
    ( ! [X0] :
        ( r2_hidden(X0,a_2_2_lattice3(sK14,sK15))
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ sP5(sK15,sK14,X0) )
    | ~ spl23_5
    | ~ spl23_12 ),
    inference(superposition,[],[f502,f600])).

fof(f600,plain,
    ( ! [X0] :
        ( k15_lattice3(sK14,sK15) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ sP5(sK15,sK14,X0) )
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f599,f89])).

fof(f599,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | v2_struct_0(sK14)
        | k15_lattice3(sK14,sK15) = X0 )
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f598,f90])).

fof(f598,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14)
        | k15_lattice3(sK14,sK15) = X0 )
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f597,f91])).

fof(f597,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ v4_lattice3(sK14)
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14)
        | k15_lattice3(sK14,sK15) = X0 )
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f593,f92])).

fof(f593,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ l3_lattices(sK14)
        | ~ v4_lattice3(sK14)
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14)
        | k15_lattice3(sK14,sK15) = X0 )
    | ~ spl23_12 ),
    inference(resolution,[],[f549,f398])).

fof(f398,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(k15_lattice3(X5,X6),u1_struct_0(X5))
      | ~ sP5(X6,X5,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ l3_lattices(X5)
      | ~ v4_lattice3(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | k15_lattice3(X5,X6) = X4 ) ),
    inference(duplicate_literal_removal,[],[f397])).

fof(f397,plain,(
    ! [X6,X4,X5] :
      ( k15_lattice3(X5,X6) = X4
      | ~ sP5(X6,X5,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ l3_lattices(X5)
      | ~ v4_lattice3(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | ~ m1_subset_1(k15_lattice3(X5,X6),u1_struct_0(X5))
      | ~ l3_lattices(X5)
      | ~ v4_lattice3(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | ~ m1_subset_1(k15_lattice3(X5,X6),u1_struct_0(X5)) ) ),
    inference(resolution,[],[f385,f217])).

fof(f385,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X2,X3,X1)
      | X0 = X1
      | ~ sP5(X2,X3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(X1,u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f384])).

fof(f384,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X1
      | ~ sP5(X2,X3,X1)
      | ~ sP5(X2,X3,X0)
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
    inference(resolution,[],[f248,f152])).

fof(f248,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | X2 = X3
      | ~ sP5(X0,X1,X3)
      | ~ sP5(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f197,f152])).

fof(f197,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X0,X1)
      | ~ sP5(X1,X0,X3)
      | X2 = X3
      | ~ sP5(X1,X0,X2)
      | ~ sP6(X2,X0,X1) ) ),
    inference(superposition,[],[f113,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X1,X2) = X0
      | ~ sP5(X2,X1,X0)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f502,plain,
    ( r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15))
    | ~ spl23_5 ),
    inference(avatar_component_clause,[],[f501])).

fof(f501,plain,
    ( spl23_5
  <=> r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_5])])).

fof(f828,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) )
    | ~ spl23_4
    | ~ spl23_7
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f827,f600])).

fof(f827,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | k15_lattice3(sK14,sK15) != X0
        | ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) )
    | ~ spl23_4
    | ~ spl23_7
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f826,f671])).

fof(f671,plain,
    ( ! [X1] :
        ( ~ sP5(sK15,sK14,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK14))
        | sP3(X1,sK14) )
    | ~ spl23_7
    | ~ spl23_12 ),
    inference(superposition,[],[f509,f600])).

fof(f509,plain,
    ( sP3(k15_lattice3(sK14,sK15),sK14)
    | ~ spl23_7 ),
    inference(avatar_component_clause,[],[f508])).

fof(f508,plain,
    ( spl23_7
  <=> sP3(k15_lattice3(sK14,sK15),sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_7])])).

fof(f826,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ sP3(X0,sK14)
        | k15_lattice3(sK14,sK15) != X0
        | ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) )
    | ~ spl23_4
    | ~ spl23_12 ),
    inference(duplicate_literal_removal,[],[f822])).

fof(f822,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ sP3(X0,sK14)
        | k15_lattice3(sK14,sK15) != X0
        | ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15))
        | ~ m1_subset_1(X0,u1_struct_0(sK14)) )
    | ~ spl23_4
    | ~ spl23_12 ),
    inference(resolution,[],[f818,f446])).

fof(f446,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK14,X0,a_2_2_lattice3(sK14,sK15))
        | ~ sP3(X0,sK14)
        | k15_lattice3(sK14,sK15) != X0
        | ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15))
        | ~ m1_subset_1(X0,u1_struct_0(sK14)) )
    | ~ spl23_4 ),
    inference(avatar_component_clause,[],[f445])).

fof(f445,plain,
    ( spl23_4
  <=> ! [X0] :
        ( ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15))
        | ~ sP3(X0,sK14)
        | k15_lattice3(sK14,sK15) != X0
        | ~ r3_lattice3(sK14,X0,a_2_2_lattice3(sK14,sK15))
        | ~ m1_subset_1(X0,u1_struct_0(sK14)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_4])])).

fof(f818,plain,
    ( ! [X2] :
        ( r3_lattice3(sK14,X2,a_2_2_lattice3(sK14,sK15))
        | ~ sP5(sK15,sK14,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK14)) )
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f817,f676])).

fof(f676,plain,
    ( ! [X6] :
        ( ~ sP5(sK15,sK14,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK14))
        | sP11(sK14,X6) )
    | ~ spl23_12 ),
    inference(superposition,[],[f607,f600])).

fof(f607,plain,
    ( sP11(sK14,k15_lattice3(sK14,sK15))
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f606,f89])).

fof(f606,plain,
    ( sP11(sK14,k15_lattice3(sK14,sK15))
    | v2_struct_0(sK14)
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f595,f92])).

fof(f595,plain,
    ( sP11(sK14,k15_lattice3(sK14,sK15))
    | ~ l3_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ spl23_12 ),
    inference(resolution,[],[f549,f139])).

fof(f139,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP11(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP11(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f41,f40])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( sP10(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP10(X1,X0,X2) )
      | ~ sP11(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).

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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f817,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK14))
        | ~ sP5(sK15,sK14,X2)
        | r3_lattice3(sK14,X2,a_2_2_lattice3(sK14,sK15))
        | ~ sP11(sK14,X2) )
    | ~ spl23_12 ),
    inference(resolution,[],[f815,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ sP10(X1,X0,X2)
      | r3_lattice3(X0,X1,X2)
      | ~ sP11(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP10(X1,X0,X2) )
          & ( sP10(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP11(X0,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f815,plain,
    ( ! [X0] :
        ( sP10(X0,sK14,a_2_2_lattice3(sK14,sK15))
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ sP5(sK15,sK14,X0) )
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f814,f89])).

fof(f814,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK14))
        | sP10(X0,sK14,a_2_2_lattice3(sK14,sK15))
        | ~ sP5(sK15,sK14,X0)
        | v2_struct_0(sK14) )
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f813,f90])).

fof(f813,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK14))
        | sP10(X0,sK14,a_2_2_lattice3(sK14,sK15))
        | ~ sP5(sK15,sK14,X0)
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14) )
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f812,f91])).

fof(f812,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK14))
        | sP10(X0,sK14,a_2_2_lattice3(sK14,sK15))
        | ~ sP5(sK15,sK14,X0)
        | ~ v4_lattice3(sK14)
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14) )
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f811,f92])).

fof(f811,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK14))
        | sP10(X0,sK14,a_2_2_lattice3(sK14,sK15))
        | ~ sP5(sK15,sK14,X0)
        | ~ l3_lattices(sK14)
        | ~ v4_lattice3(sK14)
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14) )
    | ~ spl23_12 ),
    inference(duplicate_literal_removal,[],[f810])).

fof(f810,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK14))
        | sP10(X0,sK14,a_2_2_lattice3(sK14,sK15))
        | ~ sP5(sK15,sK14,X0)
        | ~ l3_lattices(sK14)
        | ~ v4_lattice3(sK14)
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14)
        | sP10(X0,sK14,a_2_2_lattice3(sK14,sK15)) )
    | ~ spl23_12 ),
    inference(resolution,[],[f712,f290])).

fof(f290,plain,(
    ! [X10,X8,X11,X9] :
      ( r4_lattice3(X10,sK21(X8,X9,a_2_2_lattice3(X10,X11)),X11)
      | ~ l3_lattices(X10)
      | ~ v4_lattice3(X10)
      | ~ v10_lattices(X10)
      | v2_struct_0(X10)
      | sP10(X8,X9,a_2_2_lattice3(X10,X11)) ) ),
    inference(resolution,[],[f259,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ sP12(X0,X1,X2)
      | r4_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,X2,X0)
      | ~ sP12(X0,X1,X2)
      | ~ sP12(X0,X1,X2) ) ),
    inference(superposition,[],[f146,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( sK22(X0,X1,X2) = X2
      | ~ sP12(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0,X1,X2] :
      ( ( sP12(X0,X1,X2)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r4_lattice3(X1,sK22(X0,X1,X2),X0)
          & sK22(X0,X1,X2) = X2
          & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP12(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f86,f87])).

fof(f87,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK22(X0,X1,X2),X0)
        & sK22(X0,X1,X2) = X2
        & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
    ! [X0,X1,X2] :
      ( ( sP12(X0,X1,X2)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r4_lattice3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP12(X0,X1,X2) ) ) ),
    inference(rectify,[],[f85])).

fof(f85,plain,(
    ! [X2,X1,X0] :
      ( ( sP12(X2,X1,X0)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP12(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( sP12(X2,X1,X0)
    <=> ? [X3] :
          ( r4_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP12])])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK22(X0,X1,X2),X0)
      | ~ sP12(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f259,plain,(
    ! [X2,X0,X3,X1] :
      ( sP12(X0,X1,sK21(X2,X3,a_2_2_lattice3(X1,X0)))
      | sP10(X2,X3,a_2_2_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f200,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( sP13(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( sP13(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f25,f44,f43])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> sP12(X2,X1,X0) )
      | ~ sP13(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP13])])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(f200,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP13(sK21(X2,X3,a_2_2_lattice3(X1,X0)),X1,X0)
      | sP12(X0,X1,sK21(X2,X3,a_2_2_lattice3(X1,X0)))
      | sP10(X2,X3,a_2_2_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f142,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK21(X0,X1,X2),X2)
      | sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( sP10(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK21(X0,X1,X2))
          & r2_hidden(sK21(X0,X1,X2),X2)
          & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP10(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f80,f81])).

fof(f81,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK21(X0,X1,X2))
        & r2_hidden(sK21(X0,X1,X2),X2)
        & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( sP10(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP10(X0,X1,X2) ) ) ),
    inference(rectify,[],[f79])).

fof(f79,plain,(
    ! [X1,X0,X2] :
      ( ( sP10(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X1,X3)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP10(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | sP12(X2,X1,X0)
      | ~ sP13(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ~ sP12(X2,X1,X0) )
        & ( sP12(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ sP13(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f712,plain,
    ( ! [X24,X23] :
        ( ~ r4_lattice3(sK14,sK21(X23,sK14,X24),sK15)
        | ~ m1_subset_1(X23,u1_struct_0(sK14))
        | sP10(X23,sK14,X24)
        | ~ sP5(sK15,sK14,X23) )
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f711,f91])).

fof(f711,plain,
    ( ! [X24,X23] :
        ( ~ r4_lattice3(sK14,sK21(X23,sK14,X24),sK15)
        | ~ m1_subset_1(X23,u1_struct_0(sK14))
        | ~ v4_lattice3(sK14)
        | sP10(X23,sK14,X24)
        | ~ sP5(sK15,sK14,X23) )
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f710,f90])).

fof(f710,plain,
    ( ! [X24,X23] :
        ( ~ r4_lattice3(sK14,sK21(X23,sK14,X24),sK15)
        | ~ m1_subset_1(X23,u1_struct_0(sK14))
        | ~ v10_lattices(sK14)
        | ~ v4_lattice3(sK14)
        | sP10(X23,sK14,X24)
        | ~ sP5(sK15,sK14,X23) )
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f709,f92])).

fof(f709,plain,
    ( ! [X24,X23] :
        ( ~ r4_lattice3(sK14,sK21(X23,sK14,X24),sK15)
        | ~ m1_subset_1(X23,u1_struct_0(sK14))
        | ~ l3_lattices(sK14)
        | ~ v10_lattices(sK14)
        | ~ v4_lattice3(sK14)
        | sP10(X23,sK14,X24)
        | ~ sP5(sK15,sK14,X23) )
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f688,f89])).

fof(f688,plain,
    ( ! [X24,X23] :
        ( ~ r4_lattice3(sK14,sK21(X23,sK14,X24),sK15)
        | v2_struct_0(sK14)
        | ~ m1_subset_1(X23,u1_struct_0(sK14))
        | ~ l3_lattices(sK14)
        | ~ v10_lattices(sK14)
        | ~ v4_lattice3(sK14)
        | sP10(X23,sK14,X24)
        | ~ sP5(sK15,sK14,X23) )
    | ~ spl23_12 ),
    inference(duplicate_literal_removal,[],[f687])).

fof(f687,plain,
    ( ! [X24,X23] :
        ( ~ r4_lattice3(sK14,sK21(X23,sK14,X24),sK15)
        | v2_struct_0(sK14)
        | ~ m1_subset_1(X23,u1_struct_0(sK14))
        | ~ l3_lattices(sK14)
        | ~ v10_lattices(sK14)
        | ~ v4_lattice3(sK14)
        | sP10(X23,sK14,X24)
        | ~ m1_subset_1(X23,u1_struct_0(sK14))
        | ~ sP5(sK15,sK14,X23) )
    | ~ spl23_12 ),
    inference(superposition,[],[f411,f600])).

fof(f411,plain,(
    ! [X10,X11,X9] :
      ( ~ r4_lattice3(X9,sK21(k15_lattice3(X9,X10),X9,X11),X10)
      | v2_struct_0(X9)
      | ~ m1_subset_1(k15_lattice3(X9,X10),u1_struct_0(X9))
      | ~ l3_lattices(X9)
      | ~ v10_lattices(X9)
      | ~ v4_lattice3(X9)
      | sP10(k15_lattice3(X9,X10),X9,X11) ) ),
    inference(subsumption_resolution,[],[f403,f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1))
      | sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f403,plain,(
    ! [X10,X11,X9] :
      ( ~ v10_lattices(X9)
      | v2_struct_0(X9)
      | ~ m1_subset_1(k15_lattice3(X9,X10),u1_struct_0(X9))
      | ~ l3_lattices(X9)
      | ~ r4_lattice3(X9,sK21(k15_lattice3(X9,X10),X9,X11),X10)
      | ~ m1_subset_1(sK21(k15_lattice3(X9,X10),X9,X11),u1_struct_0(X9))
      | ~ v4_lattice3(X9)
      | sP10(k15_lattice3(X9,X10),X9,X11) ) ),
    inference(resolution,[],[f260,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK21(X0,X1,X2))
      | sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f260,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X2)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_lattice3(X0) ) ),
    inference(resolution,[],[f256,f117])).

fof(f117,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ r4_lattice3(X1,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK17(X0,X1,X2))
          & r4_lattice3(X1,sK17(X0,X1,X2),X2)
          & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f65,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r4_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK17(X0,X1,X2))
        & r4_lattice3(X1,sK17(X0,X1,X2),X2)
        & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r4_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ( sP4(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_lattices(X0,X2,X3)
            & r4_lattice3(X0,X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X2,X3)
            | ~ r4_lattice3(X0,X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP4(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f256,plain,(
    ! [X0,X1] :
      ( sP4(k15_lattice3(X0,X1),X0,X1)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f217,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | sP4(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ~ sP4(X2,X1,X0)
        | ~ r4_lattice3(X1,X2,X0) )
      & ( ( sP4(X2,X1,X0)
          & r4_lattice3(X1,X2,X0) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f62])).

fof(f62,plain,(
    ! [X1,X0,X2] :
      ( ( sP5(X1,X0,X2)
        | ~ sP4(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP4(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP5(X1,X0,X2) ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X1,X0,X2] :
      ( ( sP5(X1,X0,X2)
        | ~ sP4(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP4(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP5(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f617,plain,
    ( ~ spl23_12
    | spl23_13 ),
    inference(avatar_contradiction_clause,[],[f616])).

fof(f616,plain,
    ( $false
    | ~ spl23_12
    | spl23_13 ),
    inference(subsumption_resolution,[],[f615,f92])).

fof(f615,plain,
    ( ~ l3_lattices(sK14)
    | ~ spl23_12
    | spl23_13 ),
    inference(subsumption_resolution,[],[f614,f549])).

fof(f614,plain,
    ( ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ l3_lattices(sK14)
    | spl23_13 ),
    inference(subsumption_resolution,[],[f613,f89])).

fof(f613,plain,
    ( v2_struct_0(sK14)
    | ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ l3_lattices(sK14)
    | spl23_13 ),
    inference(subsumption_resolution,[],[f612,f90])).

fof(f612,plain,
    ( ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ l3_lattices(sK14)
    | spl23_13 ),
    inference(subsumption_resolution,[],[f610,f91])).

fof(f610,plain,
    ( ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ l3_lattices(sK14)
    | spl23_13 ),
    inference(resolution,[],[f554,f257])).

fof(f257,plain,(
    ! [X2,X3] :
      ( r4_lattice3(X2,k15_lattice3(X2,X3),X3)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(k15_lattice3(X2,X3),u1_struct_0(X2))
      | ~ l3_lattices(X2) ) ),
    inference(resolution,[],[f217,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | r4_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f554,plain,
    ( ~ r4_lattice3(sK14,k15_lattice3(sK14,sK15),sK15)
    | spl23_13 ),
    inference(avatar_component_clause,[],[f552])).

fof(f552,plain,
    ( spl23_13
  <=> r4_lattice3(sK14,k15_lattice3(sK14,sK15),sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_13])])).

fof(f605,plain,
    ( spl23_7
    | ~ spl23_12 ),
    inference(avatar_split_clause,[],[f604,f548,f508])).

fof(f604,plain,
    ( sP3(k15_lattice3(sK14,sK15),sK14)
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f603,f89])).

fof(f603,plain,
    ( sP3(k15_lattice3(sK14,sK15),sK14)
    | v2_struct_0(sK14)
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f602,f90])).

fof(f602,plain,
    ( sP3(k15_lattice3(sK14,sK15),sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f601,f91])).

fof(f601,plain,
    ( sP3(k15_lattice3(sK14,sK15),sK14)
    | ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ spl23_12 ),
    inference(subsumption_resolution,[],[f594,f92])).

fof(f594,plain,
    ( sP3(k15_lattice3(sK14,sK15),sK14)
    | ~ l3_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ spl23_12 ),
    inference(resolution,[],[f549,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP3(X1,X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f30,f29,f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r3_lattices(X0,X3,X1)
          | ~ r3_lattice3(X0,X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ( sP1(X1,X0,X2)
        & r3_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( k16_lattice3(X0,X2) = X1
        <=> sP2(X2,X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

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
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(f591,plain,(
    spl23_8 ),
    inference(avatar_contradiction_clause,[],[f590])).

fof(f590,plain,
    ( $false
    | spl23_8 ),
    inference(subsumption_resolution,[],[f589,f92])).

fof(f589,plain,
    ( ~ l3_lattices(sK14)
    | spl23_8 ),
    inference(subsumption_resolution,[],[f588,f91])).

fof(f588,plain,
    ( ~ v4_lattice3(sK14)
    | ~ l3_lattices(sK14)
    | spl23_8 ),
    inference(subsumption_resolution,[],[f587,f89])).

fof(f587,plain,
    ( v2_struct_0(sK14)
    | ~ v4_lattice3(sK14)
    | ~ l3_lattices(sK14)
    | spl23_8 ),
    inference(resolution,[],[f520,f154])).

fof(f154,plain,(
    ! [X1] :
      ( sP8(X1)
      | v2_struct_0(X1)
      | ~ v4_lattice3(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f132,f122])).

fof(f122,plain,(
    ! [X0] :
      ( ~ sP9(X0)
      | ~ v4_lattice3(X0)
      | sP8(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( ( v4_lattice3(X0)
          | ~ sP8(X0) )
        & ( sP8(X0)
          | ~ v4_lattice3(X0) ) )
      | ~ sP9(X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> sP8(X0) )
      | ~ sP9(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f132,plain,(
    ! [X0] :
      ( sP9(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( sP9(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f38,f37,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( sP7(X2,X0,X1)
    <=> ! [X3] :
          ( r1_lattices(X0,X2,X3)
          | ~ r4_lattice3(X0,X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f37,plain,(
    ! [X0] :
      ( sP8(X0)
    <=> ! [X1] :
        ? [X2] :
          ( sP7(X2,X0,X1)
          & r4_lattice3(X0,X2,X1)
          & m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f19,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( r1_lattices(X0,X2,X3)
                | ~ r4_lattice3(X0,X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v4_lattice3(X0)
      <=> ! [X1] :
          ? [X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ( r4_lattice3(X0,X3,X1)
                 => r1_lattices(X0,X2,X3) ) )
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattice3)).

fof(f520,plain,
    ( ~ sP8(sK14)
    | spl23_8 ),
    inference(avatar_component_clause,[],[f518])).

fof(f518,plain,
    ( spl23_8
  <=> sP8(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_8])])).

fof(f582,plain,
    ( ~ spl23_8
    | spl23_12 ),
    inference(avatar_split_clause,[],[f581,f548,f518])).

fof(f581,plain,
    ( ~ sP8(sK14)
    | spl23_12 ),
    inference(subsumption_resolution,[],[f580,f125])).

fof(f125,plain,(
    ! [X0,X3] :
      ( r4_lattice3(X0,sK19(X0,X3),X3)
      | ~ sP8(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( sP8(X0)
        | ! [X2] :
            ( ~ sP7(X2,X0,sK18(X0))
            | ~ r4_lattice3(X0,X2,sK18(X0))
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( sP7(sK19(X0,X3),X0,X3)
            & r4_lattice3(X0,sK19(X0,X3),X3)
            & m1_subset_1(sK19(X0,X3),u1_struct_0(X0)) )
        | ~ sP8(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19])],[f70,f72,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] :
        ! [X2] :
          ( ~ sP7(X2,X0,X1)
          | ~ r4_lattice3(X0,X2,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
     => ! [X2] :
          ( ~ sP7(X2,X0,sK18(X0))
          | ~ r4_lattice3(X0,X2,sK18(X0))
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X3,X0] :
      ( ? [X4] :
          ( sP7(X4,X0,X3)
          & r4_lattice3(X0,X4,X3)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( sP7(sK19(X0,X3),X0,X3)
        & r4_lattice3(X0,sK19(X0,X3),X3)
        & m1_subset_1(sK19(X0,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0] :
      ( ( sP8(X0)
        | ? [X1] :
          ! [X2] :
            ( ~ sP7(X2,X0,X1)
            | ~ r4_lattice3(X0,X2,X1)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X3] :
          ? [X4] :
            ( sP7(X4,X0,X3)
            & r4_lattice3(X0,X4,X3)
            & m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP8(X0) ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( sP8(X0)
        | ? [X1] :
          ! [X2] :
            ( ~ sP7(X2,X0,X1)
            | ~ r4_lattice3(X0,X2,X1)
            | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X1] :
          ? [X2] :
            ( sP7(X2,X0,X1)
            & r4_lattice3(X0,X2,X1)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP8(X0) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f580,plain,
    ( ~ r4_lattice3(sK14,sK19(sK14,sK15),sK15)
    | ~ sP8(sK14)
    | spl23_12 ),
    inference(subsumption_resolution,[],[f577,f124])).

fof(f124,plain,(
    ! [X0,X3] :
      ( m1_subset_1(sK19(X0,X3),u1_struct_0(X0))
      | ~ sP8(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f577,plain,
    ( ~ m1_subset_1(sK19(sK14,sK15),u1_struct_0(sK14))
    | ~ r4_lattice3(sK14,sK19(sK14,sK15),sK15)
    | ~ sP8(sK14)
    | spl23_12 ),
    inference(resolution,[],[f574,f228])).

fof(f228,plain,(
    ! [X0,X1] :
      ( sP4(sK19(X0,X1),X0,X1)
      | ~ sP8(X0) ) ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,(
    ! [X0,X1] :
      ( ~ sP8(X0)
      | sP4(sK19(X0,X1),X0,X1)
      | sP4(sK19(X0,X1),X0,X1) ) ),
    inference(resolution,[],[f221,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK17(X0,X1,X2),X2)
      | sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f221,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_lattice3(X0,sK17(sK19(X0,X1),X0,X2),X1)
      | ~ sP8(X0)
      | sP4(sK19(X0,X1),X0,X2) ) ),
    inference(subsumption_resolution,[],[f218,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))
      | sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK17(sK19(X0,X1),X0,X2),u1_struct_0(X0))
      | ~ r4_lattice3(X0,sK17(sK19(X0,X1),X0,X2),X1)
      | ~ sP8(X0)
      | sP4(sK19(X0,X1),X0,X2) ) ),
    inference(resolution,[],[f216,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK17(X0,X1,X2))
      | sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f216,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,sK19(X0,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ sP8(X0) ) ),
    inference(resolution,[],[f128,f126])).

fof(f126,plain,(
    ! [X0,X3] :
      ( sP7(sK19(X0,X3),X0,X3)
      | ~ sP8(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f128,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | ~ r4_lattice3(X1,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK20(X0,X1,X2))
          & r4_lattice3(X1,sK20(X0,X1,X2),X2)
          & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f75,f76])).

fof(f76,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r4_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK20(X0,X1,X2))
        & r4_lattice3(X1,sK20(X0,X1,X2),X2)
        & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r4_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ( sP7(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_lattices(X0,X2,X3)
            & r4_lattice3(X0,X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X2,X3)
            | ~ r4_lattice3(X0,X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP7(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f574,plain,
    ( ! [X0] :
        ( ~ sP4(X0,sK14,sK15)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ r4_lattice3(sK14,X0,sK15) )
    | spl23_12 ),
    inference(resolution,[],[f573,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( sP5(X0,X1,X2)
      | ~ sP4(X2,X1,X0)
      | ~ r4_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f573,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14)) )
    | spl23_12 ),
    inference(subsumption_resolution,[],[f572,f89])).

fof(f572,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | v2_struct_0(sK14) )
    | spl23_12 ),
    inference(subsumption_resolution,[],[f571,f90])).

fof(f571,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14) )
    | spl23_12 ),
    inference(subsumption_resolution,[],[f570,f91])).

fof(f570,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ v4_lattice3(sK14)
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14) )
    | spl23_12 ),
    inference(subsumption_resolution,[],[f569,f92])).

fof(f569,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ l3_lattices(sK14)
        | ~ v4_lattice3(sK14)
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14) )
    | spl23_12 ),
    inference(duplicate_literal_removal,[],[f568])).

fof(f568,plain,
    ( ! [X0] :
        ( ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ l3_lattices(sK14)
        | ~ v4_lattice3(sK14)
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14) )
    | spl23_12 ),
    inference(resolution,[],[f556,f152])).

fof(f556,plain,
    ( ! [X0] :
        ( ~ sP6(X0,sK14,sK15)
        | ~ sP5(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14)) )
    | spl23_12 ),
    inference(superposition,[],[f550,f113])).

fof(f550,plain,
    ( ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | spl23_12 ),
    inference(avatar_component_clause,[],[f548])).

fof(f555,plain,
    ( ~ spl23_12
    | ~ spl23_13
    | spl23_11 ),
    inference(avatar_split_clause,[],[f545,f533,f552,f548])).

fof(f533,plain,
    ( spl23_11
  <=> sP12(sK15,sK14,k15_lattice3(sK14,sK15)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_11])])).

fof(f545,plain,
    ( ~ r4_lattice3(sK14,k15_lattice3(sK14,sK15),sK15)
    | ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | spl23_11 ),
    inference(resolution,[],[f535,f151])).

fof(f151,plain,(
    ! [X0,X3,X1] :
      ( sP12(X0,X1,X3)
      | ~ r4_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f147])).

fof(f147,plain,(
    ! [X2,X0,X3,X1] :
      ( sP12(X0,X1,X2)
      | ~ r4_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f535,plain,
    ( ~ sP12(sK15,sK14,k15_lattice3(sK14,sK15))
    | spl23_11 ),
    inference(avatar_component_clause,[],[f533])).

fof(f543,plain,(
    spl23_10 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | spl23_10 ),
    inference(subsumption_resolution,[],[f541,f89])).

fof(f541,plain,
    ( v2_struct_0(sK14)
    | spl23_10 ),
    inference(subsumption_resolution,[],[f540,f90])).

fof(f540,plain,
    ( ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | spl23_10 ),
    inference(subsumption_resolution,[],[f539,f91])).

fof(f539,plain,
    ( ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | spl23_10 ),
    inference(subsumption_resolution,[],[f537,f92])).

fof(f537,plain,
    ( ~ l3_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | spl23_10 ),
    inference(resolution,[],[f531,f148])).

fof(f531,plain,
    ( ~ sP13(k15_lattice3(sK14,sK15),sK14,sK15)
    | spl23_10 ),
    inference(avatar_component_clause,[],[f529])).

fof(f529,plain,
    ( spl23_10
  <=> sP13(k15_lattice3(sK14,sK15),sK14,sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_10])])).

fof(f536,plain,
    ( ~ spl23_10
    | ~ spl23_11
    | spl23_5 ),
    inference(avatar_split_clause,[],[f526,f501,f533,f529])).

fof(f526,plain,
    ( ~ sP12(sK15,sK14,k15_lattice3(sK14,sK15))
    | ~ sP13(k15_lattice3(sK14,sK15),sK14,sK15)
    | spl23_5 ),
    inference(resolution,[],[f503,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ sP12(X2,X1,X0)
      | ~ sP13(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f503,plain,
    ( ~ r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15))
    | spl23_5 ),
    inference(avatar_component_clause,[],[f501])).

fof(f473,plain,(
    spl23_3 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | spl23_3 ),
    inference(subsumption_resolution,[],[f471,f90])).

fof(f471,plain,
    ( ~ v10_lattices(sK14)
    | spl23_3 ),
    inference(subsumption_resolution,[],[f470,f92])).

fof(f470,plain,
    ( ~ l3_lattices(sK14)
    | ~ v10_lattices(sK14)
    | spl23_3 ),
    inference(subsumption_resolution,[],[f469,f89])).

fof(f469,plain,
    ( v2_struct_0(sK14)
    | ~ l3_lattices(sK14)
    | ~ v10_lattices(sK14)
    | spl23_3 ),
    inference(resolution,[],[f443,f161])).

fof(f161,plain,(
    ! [X6] :
      ( v9_lattices(X6)
      | v2_struct_0(X6)
      | ~ l3_lattices(X6)
      | ~ v10_lattices(X6) ) ),
    inference(resolution,[],[f101,f100])).

fof(f100,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f101,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f13,f26])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f443,plain,
    ( ~ v9_lattices(sK14)
    | spl23_3 ),
    inference(avatar_component_clause,[],[f441])).

fof(f441,plain,
    ( spl23_3
  <=> v9_lattices(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_3])])).

fof(f468,plain,(
    spl23_2 ),
    inference(avatar_contradiction_clause,[],[f467])).

fof(f467,plain,
    ( $false
    | spl23_2 ),
    inference(subsumption_resolution,[],[f466,f90])).

fof(f466,plain,
    ( ~ v10_lattices(sK14)
    | spl23_2 ),
    inference(subsumption_resolution,[],[f465,f92])).

fof(f465,plain,
    ( ~ l3_lattices(sK14)
    | ~ v10_lattices(sK14)
    | spl23_2 ),
    inference(subsumption_resolution,[],[f464,f89])).

fof(f464,plain,
    ( v2_struct_0(sK14)
    | ~ l3_lattices(sK14)
    | ~ v10_lattices(sK14)
    | spl23_2 ),
    inference(resolution,[],[f439,f160])).

fof(f160,plain,(
    ! [X5] :
      ( v8_lattices(X5)
      | v2_struct_0(X5)
      | ~ l3_lattices(X5)
      | ~ v10_lattices(X5) ) ),
    inference(resolution,[],[f101,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f439,plain,
    ( ~ v8_lattices(sK14)
    | spl23_2 ),
    inference(avatar_component_clause,[],[f437])).

fof(f437,plain,
    ( spl23_2
  <=> v8_lattices(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_2])])).

fof(f463,plain,(
    spl23_1 ),
    inference(avatar_contradiction_clause,[],[f462])).

fof(f462,plain,
    ( $false
    | spl23_1 ),
    inference(subsumption_resolution,[],[f461,f90])).

fof(f461,plain,
    ( ~ v10_lattices(sK14)
    | spl23_1 ),
    inference(subsumption_resolution,[],[f460,f92])).

fof(f460,plain,
    ( ~ l3_lattices(sK14)
    | ~ v10_lattices(sK14)
    | spl23_1 ),
    inference(subsumption_resolution,[],[f459,f89])).

fof(f459,plain,
    ( v2_struct_0(sK14)
    | ~ l3_lattices(sK14)
    | ~ v10_lattices(sK14)
    | spl23_1 ),
    inference(resolution,[],[f435,f158])).

fof(f158,plain,(
    ! [X3] :
      ( v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3) ) ),
    inference(resolution,[],[f101,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f435,plain,
    ( ~ v6_lattices(sK14)
    | spl23_1 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl23_1
  <=> v6_lattices(sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl23_1])])).

fof(f447,plain,
    ( ~ spl23_1
    | ~ spl23_2
    | ~ spl23_3
    | spl23_4 ),
    inference(avatar_split_clause,[],[f431,f445,f441,f437,f433])).

fof(f431,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15))
      | ~ m1_subset_1(X0,u1_struct_0(sK14))
      | ~ v9_lattices(sK14)
      | ~ v8_lattices(sK14)
      | ~ v6_lattices(sK14)
      | ~ r3_lattice3(sK14,X0,a_2_2_lattice3(sK14,sK15))
      | k15_lattice3(sK14,sK15) != X0
      | ~ sP3(X0,sK14) ) ),
    inference(subsumption_resolution,[],[f430,f89])).

fof(f430,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15))
      | ~ m1_subset_1(X0,u1_struct_0(sK14))
      | ~ v9_lattices(sK14)
      | ~ v8_lattices(sK14)
      | ~ v6_lattices(sK14)
      | v2_struct_0(sK14)
      | ~ r3_lattice3(sK14,X0,a_2_2_lattice3(sK14,sK15))
      | k15_lattice3(sK14,sK15) != X0
      | ~ sP3(X0,sK14) ) ),
    inference(subsumption_resolution,[],[f427,f92])).

fof(f427,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15))
      | ~ m1_subset_1(X0,u1_struct_0(sK14))
      | ~ l3_lattices(sK14)
      | ~ v9_lattices(sK14)
      | ~ v8_lattices(sK14)
      | ~ v6_lattices(sK14)
      | v2_struct_0(sK14)
      | ~ r3_lattice3(sK14,X0,a_2_2_lattice3(sK14,sK15))
      | k15_lattice3(sK14,sK15) != X0
      | ~ sP3(X0,sK14) ) ),
    inference(resolution,[],[f420,f190])).

fof(f190,plain,(
    ! [X6] :
      ( ~ sP1(X6,sK14,a_2_2_lattice3(sK14,sK15))
      | ~ r3_lattice3(sK14,X6,a_2_2_lattice3(sK14,sK15))
      | k15_lattice3(sK14,sK15) != X6
      | ~ sP3(X6,sK14) ) ),
    inference(resolution,[],[f106,f179])).

fof(f179,plain,(
    ! [X0] :
      ( ~ sP2(a_2_2_lattice3(sK14,sK15),sK14,X0)
      | k15_lattice3(sK14,sK15) != X0
      | ~ sP3(X0,sK14) ) ),
    inference(superposition,[],[f93,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X1,X2) = X0
      | ~ sP2(X2,X1,X0)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k16_lattice3(X1,X2) = X0
            | ~ sP2(X2,X1,X0) )
          & ( sP2(X2,X1,X0)
            | k16_lattice3(X1,X2) != X0 ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( ( k16_lattice3(X0,X2) = X1
            | ~ sP2(X2,X0,X1) )
          & ( sP2(X2,X0,X1)
            | k16_lattice3(X0,X2) != X1 ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f93,plain,(
    k15_lattice3(sK14,sK15) != k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)) ),
    inference(cnf_transformation,[],[f48])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ sP1(X2,X1,X0)
      | ~ r3_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ sP1(X2,X1,X0)
        | ~ r3_lattice3(X1,X2,X0) )
      & ( ( sP1(X2,X1,X0)
          & r3_lattice3(X1,X2,X0) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ~ sP1(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP1(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ~ sP1(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP1(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f420,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v9_lattices(X2)
      | ~ v8_lattices(X2)
      | ~ v6_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f413])).

fof(f413,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sP1(X0,X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v9_lattices(X2)
      | ~ v8_lattices(X2)
      | ~ v6_lattices(X2)
      | v2_struct_0(X2)
      | sP1(X0,X2,X1) ) ),
    inference(resolution,[],[f345,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X1,sK16(X0,X1,X2),X0)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ r3_lattices(X1,sK16(X0,X1,X2),X0)
          & r3_lattice3(X1,sK16(X0,X1,X2),X2)
          & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r3_lattices(X1,X4,X0)
            | ~ r3_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f56,f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X1,X3,X0)
          & r3_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r3_lattices(X1,sK16(X0,X1,X2),X0)
        & r3_lattice3(X1,sK16(X0,X1,X2),X2)
        & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ r3_lattices(X1,X3,X0)
            & r3_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r3_lattices(X1,X4,X0)
            | ~ r3_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ~ r3_lattices(X0,X3,X1)
            & r3_lattice3(X0,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r3_lattices(X0,X3,X1)
            | ~ r3_lattice3(X0,X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f345,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X1,sK16(X3,X1,X2),X0)
      | ~ r2_hidden(X0,X2)
      | sP1(X3,X1,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f344,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f344,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | sP1(X3,X1,X2)
      | r3_lattices(X1,sK16(X3,X1,X2),X0)
      | ~ m1_subset_1(sK16(X3,X1,X2),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f343,f139])).

fof(f343,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ sP11(X1,sK16(X3,X1,X2))
      | sP1(X3,X1,X2)
      | r3_lattices(X1,sK16(X3,X1,X2),X0)
      | ~ m1_subset_1(sK16(X3,X1,X2),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f339])).

fof(f339,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ sP11(X1,sK16(X3,X1,X2))
      | sP1(X3,X1,X2)
      | r3_lattices(X1,sK16(X3,X1,X2),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(sK16(X3,X1,X2),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f246,f141])).

fof(f141,plain,(
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
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
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
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f246,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X1,sK16(X2,X1,X3),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X3)
      | ~ sP11(X1,sK16(X2,X1,X3))
      | sP1(X2,X1,X3) ) ),
    inference(resolution,[],[f213,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK16(X0,X1,X2),X2)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f213,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X2,X3,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | r1_lattices(X2,X3,X0)
      | ~ r2_hidden(X0,X1)
      | ~ sP11(X2,X3) ) ),
    inference(resolution,[],[f135,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( sP10(X1,X0,X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP11(X0,X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f135,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP10(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 21:00:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (10577)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (10560)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (10558)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (10557)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (10557)Refutation not found, incomplete strategy% (10557)------------------------------
% 0.21/0.54  % (10557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (10557)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (10557)Memory used [KB]: 10618
% 0.21/0.54  % (10557)Time elapsed: 0.113 s
% 0.21/0.54  % (10557)------------------------------
% 0.21/0.54  % (10557)------------------------------
% 0.21/0.54  % (10559)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.54  % (10579)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (10581)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.55  % (10571)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.55  % (10565)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (10575)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.55  % (10561)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.56  % (10567)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.56  % (10574)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.56  % (10566)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.56  % (10563)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.56  % (10556)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.56  % (10563)Refutation not found, incomplete strategy% (10563)------------------------------
% 0.21/0.56  % (10563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (10563)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (10563)Memory used [KB]: 1663
% 0.21/0.56  % (10563)Time elapsed: 0.094 s
% 0.21/0.56  % (10563)------------------------------
% 0.21/0.56  % (10563)------------------------------
% 0.21/0.56  % (10560)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f855,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f447,f463,f468,f473,f536,f543,f555,f582,f591,f605,f617,f854])).
% 0.21/0.56  fof(f854,plain,(
% 0.21/0.56    ~spl23_4 | ~spl23_5 | ~spl23_7 | ~spl23_12),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f853])).
% 0.21/0.56  fof(f853,plain,(
% 0.21/0.56    $false | (~spl23_4 | ~spl23_5 | ~spl23_7 | ~spl23_12)),
% 0.21/0.56    inference(subsumption_resolution,[],[f852,f89])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    ~v2_struct_0(sK14)),
% 0.21/0.56    inference(cnf_transformation,[],[f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    k15_lattice3(sK14,sK15) != k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)) & l3_lattices(sK14) & v4_lattice3(sK14) & v10_lattices(sK14) & ~v2_struct_0(sK14)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15])],[f11,f47,f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : k15_lattice3(sK14,X1) != k16_lattice3(sK14,a_2_2_lattice3(sK14,X1)) & l3_lattices(sK14) & v4_lattice3(sK14) & v10_lattices(sK14) & ~v2_struct_0(sK14))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ? [X1] : k15_lattice3(sK14,X1) != k16_lattice3(sK14,a_2_2_lattice3(sK14,X1)) => k15_lattice3(sK14,sK15) != k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f10])).
% 0.21/0.56  fof(f10,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f9])).
% 0.21/0.56  fof(f9,negated_conjecture,(
% 0.21/0.56    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 0.21/0.56    inference(negated_conjecture,[],[f8])).
% 0.21/0.56  fof(f8,conjecture,(
% 0.21/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).
% 0.21/0.56  fof(f852,plain,(
% 0.21/0.56    v2_struct_0(sK14) | (~spl23_4 | ~spl23_5 | ~spl23_7 | ~spl23_12)),
% 0.21/0.56    inference(subsumption_resolution,[],[f851,f90])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    v10_lattices(sK14)),
% 0.21/0.56    inference(cnf_transformation,[],[f48])).
% 0.21/0.56  fof(f851,plain,(
% 0.21/0.56    ~v10_lattices(sK14) | v2_struct_0(sK14) | (~spl23_4 | ~spl23_5 | ~spl23_7 | ~spl23_12)),
% 0.21/0.56    inference(subsumption_resolution,[],[f850,f91])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    v4_lattice3(sK14)),
% 0.21/0.56    inference(cnf_transformation,[],[f48])).
% 0.21/0.56  fof(f850,plain,(
% 0.21/0.56    ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | (~spl23_4 | ~spl23_5 | ~spl23_7 | ~spl23_12)),
% 0.21/0.56    inference(subsumption_resolution,[],[f849,f92])).
% 0.21/0.56  fof(f92,plain,(
% 0.21/0.56    l3_lattices(sK14)),
% 0.21/0.56    inference(cnf_transformation,[],[f48])).
% 0.21/0.56  fof(f849,plain,(
% 0.21/0.56    ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | (~spl23_4 | ~spl23_5 | ~spl23_7 | ~spl23_12)),
% 0.21/0.56    inference(subsumption_resolution,[],[f848,f549])).
% 0.21/0.56  fof(f549,plain,(
% 0.21/0.56    m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~spl23_12),
% 0.21/0.56    inference(avatar_component_clause,[],[f548])).
% 0.21/0.56  fof(f548,plain,(
% 0.21/0.56    spl23_12 <=> m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl23_12])])).
% 0.21/0.57  fof(f848,plain,(
% 0.21/0.57    ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | (~spl23_4 | ~spl23_5 | ~spl23_7 | ~spl23_12)),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f847])).
% 0.21/0.57  fof(f847,plain,(
% 0.21/0.57    ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | (~spl23_4 | ~spl23_5 | ~spl23_7 | ~spl23_12)),
% 0.21/0.57    inference(resolution,[],[f829,f217])).
% 0.21/0.57  fof(f217,plain,(
% 0.21/0.57    ( ! [X0,X1] : (sP5(X1,X0,k15_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))) )),
% 0.21/0.57    inference(resolution,[],[f152,f150])).
% 0.21/0.57  fof(f150,plain,(
% 0.21/0.57    ( ! [X2,X1] : (~sP6(k15_lattice3(X1,X2),X1,X2) | sP5(X2,X1,k15_lattice3(X1,X2))) )),
% 0.21/0.57    inference(equality_resolution,[],[f112])).
% 0.21/0.57  fof(f112,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP5(X2,X1,X0) | k15_lattice3(X1,X2) != X0 | ~sP6(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f60])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((k15_lattice3(X1,X2) = X0 | ~sP5(X2,X1,X0)) & (sP5(X2,X1,X0) | k15_lattice3(X1,X2) != X0)) | ~sP6(X0,X1,X2))),
% 0.21/0.57    inference(rectify,[],[f59])).
% 0.21/0.57  fof(f59,plain,(
% 0.21/0.57    ! [X2,X0,X1] : (((k15_lattice3(X0,X1) = X2 | ~sP5(X1,X0,X2)) & (sP5(X1,X0,X2) | k15_lattice3(X0,X1) != X2)) | ~sP6(X2,X0,X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f34])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    ! [X2,X0,X1] : ((k15_lattice3(X0,X1) = X2 <=> sP5(X1,X0,X2)) | ~sP6(X2,X0,X1))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.21/0.57  fof(f152,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP6(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f121])).
% 0.21/0.57  fof(f121,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP6(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f35])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    ! [X0] : (! [X1,X2] : (sP6(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(definition_folding,[],[f17,f34,f33,f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X2,X0,X1] : (sP4(X2,X0,X1) <=> ! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X1,X0,X2] : (sP5(X1,X0,X2) <=> (sP4(X2,X0,X1) & r4_lattice3(X0,X2,X1)))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 0.21/0.57  fof(f829,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14))) ) | (~spl23_4 | ~spl23_5 | ~spl23_7 | ~spl23_12)),
% 0.21/0.57    inference(subsumption_resolution,[],[f828,f670])).
% 0.21/0.57  fof(f670,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~sP5(sK15,sK14,X0)) ) | (~spl23_5 | ~spl23_12)),
% 0.21/0.57    inference(superposition,[],[f502,f600])).
% 0.21/0.57  fof(f600,plain,(
% 0.21/0.57    ( ! [X0] : (k15_lattice3(sK14,sK15) = X0 | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~sP5(sK15,sK14,X0)) ) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f599,f89])).
% 0.21/0.57  fof(f599,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | v2_struct_0(sK14) | k15_lattice3(sK14,sK15) = X0) ) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f598,f90])).
% 0.21/0.57  fof(f598,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~v10_lattices(sK14) | v2_struct_0(sK14) | k15_lattice3(sK14,sK15) = X0) ) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f597,f91])).
% 0.21/0.57  fof(f597,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | k15_lattice3(sK14,sK15) = X0) ) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f593,f92])).
% 0.21/0.57  fof(f593,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | k15_lattice3(sK14,sK15) = X0) ) | ~spl23_12),
% 0.21/0.57    inference(resolution,[],[f549,f398])).
% 0.21/0.57  fof(f398,plain,(
% 0.21/0.57    ( ! [X6,X4,X5] : (~m1_subset_1(k15_lattice3(X5,X6),u1_struct_0(X5)) | ~sP5(X6,X5,X4) | ~m1_subset_1(X4,u1_struct_0(X5)) | ~l3_lattices(X5) | ~v4_lattice3(X5) | ~v10_lattices(X5) | v2_struct_0(X5) | k15_lattice3(X5,X6) = X4) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f397])).
% 0.21/0.57  fof(f397,plain,(
% 0.21/0.57    ( ! [X6,X4,X5] : (k15_lattice3(X5,X6) = X4 | ~sP5(X6,X5,X4) | ~m1_subset_1(X4,u1_struct_0(X5)) | ~l3_lattices(X5) | ~v4_lattice3(X5) | ~v10_lattices(X5) | v2_struct_0(X5) | ~m1_subset_1(k15_lattice3(X5,X6),u1_struct_0(X5)) | ~l3_lattices(X5) | ~v4_lattice3(X5) | ~v10_lattices(X5) | v2_struct_0(X5) | ~m1_subset_1(k15_lattice3(X5,X6),u1_struct_0(X5))) )),
% 0.21/0.57    inference(resolution,[],[f385,f217])).
% 0.21/0.57  fof(f385,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~sP5(X2,X3,X1) | X0 = X1 | ~sP5(X2,X3,X0) | ~m1_subset_1(X0,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v4_lattice3(X3) | ~v10_lattices(X3) | v2_struct_0(X3) | ~m1_subset_1(X1,u1_struct_0(X3))) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f384])).
% 0.21/0.57  fof(f384,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (X0 = X1 | ~sP5(X2,X3,X1) | ~sP5(X2,X3,X0) | ~m1_subset_1(X0,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v4_lattice3(X3) | ~v10_lattices(X3) | v2_struct_0(X3) | ~m1_subset_1(X1,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v4_lattice3(X3) | ~v10_lattices(X3) | v2_struct_0(X3)) )),
% 0.21/0.57    inference(resolution,[],[f248,f152])).
% 0.21/0.57  fof(f248,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~sP6(X3,X1,X0) | X2 = X3 | ~sP5(X0,X1,X3) | ~sP5(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 0.21/0.57    inference(resolution,[],[f197,f152])).
% 0.21/0.57  fof(f197,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~sP6(X3,X0,X1) | ~sP5(X1,X0,X3) | X2 = X3 | ~sP5(X1,X0,X2) | ~sP6(X2,X0,X1)) )),
% 0.21/0.57    inference(superposition,[],[f113,f113])).
% 0.21/0.57  fof(f113,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k15_lattice3(X1,X2) = X0 | ~sP5(X2,X1,X0) | ~sP6(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f60])).
% 0.21/0.57  fof(f502,plain,(
% 0.21/0.57    r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15)) | ~spl23_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f501])).
% 0.21/0.57  fof(f501,plain,(
% 0.21/0.57    spl23_5 <=> r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl23_5])])).
% 0.21/0.57  fof(f828,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~r2_hidden(X0,a_2_2_lattice3(sK14,sK15))) ) | (~spl23_4 | ~spl23_7 | ~spl23_12)),
% 0.21/0.57    inference(subsumption_resolution,[],[f827,f600])).
% 0.21/0.57  fof(f827,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | k15_lattice3(sK14,sK15) != X0 | ~r2_hidden(X0,a_2_2_lattice3(sK14,sK15))) ) | (~spl23_4 | ~spl23_7 | ~spl23_12)),
% 0.21/0.57    inference(subsumption_resolution,[],[f826,f671])).
% 0.21/0.57  fof(f671,plain,(
% 0.21/0.57    ( ! [X1] : (~sP5(sK15,sK14,X1) | ~m1_subset_1(X1,u1_struct_0(sK14)) | sP3(X1,sK14)) ) | (~spl23_7 | ~spl23_12)),
% 0.21/0.57    inference(superposition,[],[f509,f600])).
% 0.21/0.57  fof(f509,plain,(
% 0.21/0.57    sP3(k15_lattice3(sK14,sK15),sK14) | ~spl23_7),
% 0.21/0.57    inference(avatar_component_clause,[],[f508])).
% 0.21/0.57  fof(f508,plain,(
% 0.21/0.57    spl23_7 <=> sP3(k15_lattice3(sK14,sK15),sK14)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl23_7])])).
% 0.21/0.57  fof(f826,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~sP3(X0,sK14) | k15_lattice3(sK14,sK15) != X0 | ~r2_hidden(X0,a_2_2_lattice3(sK14,sK15))) ) | (~spl23_4 | ~spl23_12)),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f822])).
% 0.21/0.57  fof(f822,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~sP3(X0,sK14) | k15_lattice3(sK14,sK15) != X0 | ~r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) | ~m1_subset_1(X0,u1_struct_0(sK14))) ) | (~spl23_4 | ~spl23_12)),
% 0.21/0.57    inference(resolution,[],[f818,f446])).
% 0.21/0.57  fof(f446,plain,(
% 0.21/0.57    ( ! [X0] : (~r3_lattice3(sK14,X0,a_2_2_lattice3(sK14,sK15)) | ~sP3(X0,sK14) | k15_lattice3(sK14,sK15) != X0 | ~r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) | ~m1_subset_1(X0,u1_struct_0(sK14))) ) | ~spl23_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f445])).
% 0.21/0.57  fof(f445,plain,(
% 0.21/0.57    spl23_4 <=> ! [X0] : (~r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) | ~sP3(X0,sK14) | k15_lattice3(sK14,sK15) != X0 | ~r3_lattice3(sK14,X0,a_2_2_lattice3(sK14,sK15)) | ~m1_subset_1(X0,u1_struct_0(sK14)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl23_4])])).
% 0.21/0.57  fof(f818,plain,(
% 0.21/0.57    ( ! [X2] : (r3_lattice3(sK14,X2,a_2_2_lattice3(sK14,sK15)) | ~sP5(sK15,sK14,X2) | ~m1_subset_1(X2,u1_struct_0(sK14))) ) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f817,f676])).
% 0.21/0.57  fof(f676,plain,(
% 0.21/0.57    ( ! [X6] : (~sP5(sK15,sK14,X6) | ~m1_subset_1(X6,u1_struct_0(sK14)) | sP11(sK14,X6)) ) | ~spl23_12),
% 0.21/0.57    inference(superposition,[],[f607,f600])).
% 0.21/0.57  fof(f607,plain,(
% 0.21/0.57    sP11(sK14,k15_lattice3(sK14,sK15)) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f606,f89])).
% 0.21/0.57  fof(f606,plain,(
% 0.21/0.57    sP11(sK14,k15_lattice3(sK14,sK15)) | v2_struct_0(sK14) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f595,f92])).
% 0.21/0.57  fof(f595,plain,(
% 0.21/0.57    sP11(sK14,k15_lattice3(sK14,sK15)) | ~l3_lattices(sK14) | v2_struct_0(sK14) | ~spl23_12),
% 0.21/0.57    inference(resolution,[],[f549,f139])).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP11(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (sP11(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(definition_folding,[],[f21,f41,f40])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ! [X1,X0,X2] : (sP10(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP10(X1,X0,X2)) | ~sP11(X0,X1))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).
% 0.21/0.57  fof(f21,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 0.21/0.57  fof(f817,plain,(
% 0.21/0.57    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK14)) | ~sP5(sK15,sK14,X2) | r3_lattice3(sK14,X2,a_2_2_lattice3(sK14,sK15)) | ~sP11(sK14,X2)) ) | ~spl23_12),
% 0.21/0.57    inference(resolution,[],[f815,f134])).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~sP10(X1,X0,X2) | r3_lattice3(X0,X1,X2) | ~sP11(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f78])).
% 0.21/0.57  fof(f78,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP10(X1,X0,X2)) & (sP10(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP11(X0,X1))),
% 0.21/0.57    inference(nnf_transformation,[],[f41])).
% 0.21/0.57  fof(f815,plain,(
% 0.21/0.57    ( ! [X0] : (sP10(X0,sK14,a_2_2_lattice3(sK14,sK15)) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~sP5(sK15,sK14,X0)) ) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f814,f89])).
% 0.21/0.57  fof(f814,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK14)) | sP10(X0,sK14,a_2_2_lattice3(sK14,sK15)) | ~sP5(sK15,sK14,X0) | v2_struct_0(sK14)) ) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f813,f90])).
% 0.21/0.57  fof(f813,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK14)) | sP10(X0,sK14,a_2_2_lattice3(sK14,sK15)) | ~sP5(sK15,sK14,X0) | ~v10_lattices(sK14) | v2_struct_0(sK14)) ) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f812,f91])).
% 0.21/0.57  fof(f812,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK14)) | sP10(X0,sK14,a_2_2_lattice3(sK14,sK15)) | ~sP5(sK15,sK14,X0) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14)) ) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f811,f92])).
% 0.21/0.57  fof(f811,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK14)) | sP10(X0,sK14,a_2_2_lattice3(sK14,sK15)) | ~sP5(sK15,sK14,X0) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14)) ) | ~spl23_12),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f810])).
% 0.21/0.57  fof(f810,plain,(
% 0.21/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK14)) | sP10(X0,sK14,a_2_2_lattice3(sK14,sK15)) | ~sP5(sK15,sK14,X0) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | sP10(X0,sK14,a_2_2_lattice3(sK14,sK15))) ) | ~spl23_12),
% 0.21/0.57    inference(resolution,[],[f712,f290])).
% 0.21/0.57  fof(f290,plain,(
% 0.21/0.57    ( ! [X10,X8,X11,X9] : (r4_lattice3(X10,sK21(X8,X9,a_2_2_lattice3(X10,X11)),X11) | ~l3_lattices(X10) | ~v4_lattice3(X10) | ~v10_lattices(X10) | v2_struct_0(X10) | sP10(X8,X9,a_2_2_lattice3(X10,X11))) )),
% 0.21/0.57    inference(resolution,[],[f259,f175])).
% 0.21/0.57  fof(f175,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~sP12(X0,X1,X2) | r4_lattice3(X1,X2,X0)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f174])).
% 0.21/0.57  fof(f174,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r4_lattice3(X1,X2,X0) | ~sP12(X0,X1,X2) | ~sP12(X0,X1,X2)) )),
% 0.21/0.57    inference(superposition,[],[f146,f145])).
% 0.21/0.57  fof(f145,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sK22(X0,X1,X2) = X2 | ~sP12(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f88])).
% 0.21/0.57  fof(f88,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP12(X0,X1,X2) | ! [X3] : (~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK22(X0,X1,X2),X0) & sK22(X0,X1,X2) = X2 & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1))) | ~sP12(X0,X1,X2)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f86,f87])).
% 0.21/0.57  fof(f87,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK22(X0,X1,X2),X0) & sK22(X0,X1,X2) = X2 & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f86,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP12(X0,X1,X2) | ! [X3] : (~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP12(X0,X1,X2)))),
% 0.21/0.57    inference(rectify,[],[f85])).
% 0.21/0.57  fof(f85,plain,(
% 0.21/0.57    ! [X2,X1,X0] : ((sP12(X2,X1,X0) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP12(X2,X1,X0)))),
% 0.21/0.57    inference(nnf_transformation,[],[f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (sP12(X2,X1,X0) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP12])])).
% 0.21/0.57  fof(f146,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK22(X0,X1,X2),X0) | ~sP12(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f88])).
% 0.21/0.57  fof(f259,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (sP12(X0,X1,sK21(X2,X3,a_2_2_lattice3(X1,X0))) | sP10(X2,X3,a_2_2_lattice3(X1,X0)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 0.21/0.57    inference(resolution,[],[f200,f148])).
% 0.21/0.57  fof(f148,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP13(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (sP13(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 0.21/0.57    inference(definition_folding,[],[f25,f44,f43])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> sP12(X2,X1,X0)) | ~sP13(X0,X1,X2))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP13])])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 0.21/0.57    inference(flattening,[],[f24])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 0.21/0.57  fof(f200,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~sP13(sK21(X2,X3,a_2_2_lattice3(X1,X0)),X1,X0) | sP12(X0,X1,sK21(X2,X3,a_2_2_lattice3(X1,X0))) | sP10(X2,X3,a_2_2_lattice3(X1,X0))) )),
% 0.21/0.57    inference(resolution,[],[f142,f137])).
% 0.21/0.57  fof(f137,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(sK21(X0,X1,X2),X2) | sP10(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f82])).
% 0.21/0.57  fof(f82,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP10(X0,X1,X2) | (~r1_lattices(X1,X0,sK21(X0,X1,X2)) & r2_hidden(sK21(X0,X1,X2),X2) & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP10(X0,X1,X2)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f80,f81])).
% 0.21/0.57  fof(f81,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK21(X0,X1,X2)) & r2_hidden(sK21(X0,X1,X2),X2) & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP10(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP10(X0,X1,X2)))),
% 0.21/0.57    inference(rectify,[],[f79])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    ! [X1,X0,X2] : ((sP10(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP10(X1,X0,X2)))),
% 0.21/0.57    inference(nnf_transformation,[],[f40])).
% 0.21/0.57  fof(f142,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | sP12(X2,X1,X0) | ~sP13(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f84])).
% 0.21/0.57  fof(f84,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~sP12(X2,X1,X0)) & (sP12(X2,X1,X0) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~sP13(X0,X1,X2))),
% 0.21/0.57    inference(nnf_transformation,[],[f44])).
% 0.21/0.57  fof(f712,plain,(
% 0.21/0.57    ( ! [X24,X23] : (~r4_lattice3(sK14,sK21(X23,sK14,X24),sK15) | ~m1_subset_1(X23,u1_struct_0(sK14)) | sP10(X23,sK14,X24) | ~sP5(sK15,sK14,X23)) ) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f711,f91])).
% 0.21/0.57  fof(f711,plain,(
% 0.21/0.57    ( ! [X24,X23] : (~r4_lattice3(sK14,sK21(X23,sK14,X24),sK15) | ~m1_subset_1(X23,u1_struct_0(sK14)) | ~v4_lattice3(sK14) | sP10(X23,sK14,X24) | ~sP5(sK15,sK14,X23)) ) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f710,f90])).
% 0.21/0.57  fof(f710,plain,(
% 0.21/0.57    ( ! [X24,X23] : (~r4_lattice3(sK14,sK21(X23,sK14,X24),sK15) | ~m1_subset_1(X23,u1_struct_0(sK14)) | ~v10_lattices(sK14) | ~v4_lattice3(sK14) | sP10(X23,sK14,X24) | ~sP5(sK15,sK14,X23)) ) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f709,f92])).
% 0.21/0.57  fof(f709,plain,(
% 0.21/0.57    ( ! [X24,X23] : (~r4_lattice3(sK14,sK21(X23,sK14,X24),sK15) | ~m1_subset_1(X23,u1_struct_0(sK14)) | ~l3_lattices(sK14) | ~v10_lattices(sK14) | ~v4_lattice3(sK14) | sP10(X23,sK14,X24) | ~sP5(sK15,sK14,X23)) ) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f688,f89])).
% 0.21/0.57  fof(f688,plain,(
% 0.21/0.57    ( ! [X24,X23] : (~r4_lattice3(sK14,sK21(X23,sK14,X24),sK15) | v2_struct_0(sK14) | ~m1_subset_1(X23,u1_struct_0(sK14)) | ~l3_lattices(sK14) | ~v10_lattices(sK14) | ~v4_lattice3(sK14) | sP10(X23,sK14,X24) | ~sP5(sK15,sK14,X23)) ) | ~spl23_12),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f687])).
% 0.21/0.57  fof(f687,plain,(
% 0.21/0.57    ( ! [X24,X23] : (~r4_lattice3(sK14,sK21(X23,sK14,X24),sK15) | v2_struct_0(sK14) | ~m1_subset_1(X23,u1_struct_0(sK14)) | ~l3_lattices(sK14) | ~v10_lattices(sK14) | ~v4_lattice3(sK14) | sP10(X23,sK14,X24) | ~m1_subset_1(X23,u1_struct_0(sK14)) | ~sP5(sK15,sK14,X23)) ) | ~spl23_12),
% 0.21/0.57    inference(superposition,[],[f411,f600])).
% 0.21/0.57  fof(f411,plain,(
% 0.21/0.57    ( ! [X10,X11,X9] : (~r4_lattice3(X9,sK21(k15_lattice3(X9,X10),X9,X11),X10) | v2_struct_0(X9) | ~m1_subset_1(k15_lattice3(X9,X10),u1_struct_0(X9)) | ~l3_lattices(X9) | ~v10_lattices(X9) | ~v4_lattice3(X9) | sP10(k15_lattice3(X9,X10),X9,X11)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f403,f136])).
% 0.21/0.57  fof(f136,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)) | sP10(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f82])).
% 0.21/0.57  fof(f403,plain,(
% 0.21/0.57    ( ! [X10,X11,X9] : (~v10_lattices(X9) | v2_struct_0(X9) | ~m1_subset_1(k15_lattice3(X9,X10),u1_struct_0(X9)) | ~l3_lattices(X9) | ~r4_lattice3(X9,sK21(k15_lattice3(X9,X10),X9,X11),X10) | ~m1_subset_1(sK21(k15_lattice3(X9,X10),X9,X11),u1_struct_0(X9)) | ~v4_lattice3(X9) | sP10(k15_lattice3(X9,X10),X9,X11)) )),
% 0.21/0.57    inference(resolution,[],[f260,f138])).
% 0.21/0.57  fof(f138,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK21(X0,X1,X2)) | sP10(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f82])).
% 0.21/0.57  fof(f260,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X2) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_lattice3(X0)) )),
% 0.21/0.57    inference(resolution,[],[f256,f117])).
% 0.21/0.57  fof(f117,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (~sP4(X0,X1,X2) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | (~r1_lattices(X1,X0,sK17(X0,X1,X2)) & r4_lattice3(X1,sK17(X0,X1,X2),X2) & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f65,f66])).
% 0.21/0.57  fof(f66,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK17(X0,X1,X2)) & r4_lattice3(X1,sK17(X0,X1,X2),X2) & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 0.21/0.57    inference(rectify,[],[f64])).
% 0.21/0.57  fof(f64,plain,(
% 0.21/0.57    ! [X2,X0,X1] : ((sP4(X2,X0,X1) | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP4(X2,X0,X1)))),
% 0.21/0.57    inference(nnf_transformation,[],[f32])).
% 0.21/0.57  fof(f256,plain,(
% 0.21/0.57    ( ! [X0,X1] : (sP4(k15_lattice3(X0,X1),X0,X1) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0)) )),
% 0.21/0.57    inference(resolution,[],[f217,f115])).
% 0.21/0.57  fof(f115,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | sP4(X2,X1,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f63])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ~sP4(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) & ((sP4(X2,X1,X0) & r4_lattice3(X1,X2,X0)) | ~sP5(X0,X1,X2)))),
% 0.21/0.57    inference(rectify,[],[f62])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | ~sP4(X2,X0,X1) | ~r4_lattice3(X0,X2,X1)) & ((sP4(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP5(X1,X0,X2)))),
% 0.21/0.57    inference(flattening,[],[f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | (~sP4(X2,X0,X1) | ~r4_lattice3(X0,X2,X1))) & ((sP4(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP5(X1,X0,X2)))),
% 0.21/0.57    inference(nnf_transformation,[],[f33])).
% 0.21/0.57  fof(f617,plain,(
% 0.21/0.57    ~spl23_12 | spl23_13),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f616])).
% 0.21/0.57  fof(f616,plain,(
% 0.21/0.57    $false | (~spl23_12 | spl23_13)),
% 0.21/0.57    inference(subsumption_resolution,[],[f615,f92])).
% 0.21/0.57  fof(f615,plain,(
% 0.21/0.57    ~l3_lattices(sK14) | (~spl23_12 | spl23_13)),
% 0.21/0.57    inference(subsumption_resolution,[],[f614,f549])).
% 0.21/0.57  fof(f614,plain,(
% 0.21/0.57    ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~l3_lattices(sK14) | spl23_13),
% 0.21/0.57    inference(subsumption_resolution,[],[f613,f89])).
% 0.21/0.57  fof(f613,plain,(
% 0.21/0.57    v2_struct_0(sK14) | ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~l3_lattices(sK14) | spl23_13),
% 0.21/0.57    inference(subsumption_resolution,[],[f612,f90])).
% 0.21/0.57  fof(f612,plain,(
% 0.21/0.57    ~v10_lattices(sK14) | v2_struct_0(sK14) | ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~l3_lattices(sK14) | spl23_13),
% 0.21/0.57    inference(subsumption_resolution,[],[f610,f91])).
% 0.21/0.57  fof(f610,plain,(
% 0.21/0.57    ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~l3_lattices(sK14) | spl23_13),
% 0.21/0.57    inference(resolution,[],[f554,f257])).
% 0.21/0.57  fof(f257,plain,(
% 0.21/0.57    ( ! [X2,X3] : (r4_lattice3(X2,k15_lattice3(X2,X3),X3) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | ~m1_subset_1(k15_lattice3(X2,X3),u1_struct_0(X2)) | ~l3_lattices(X2)) )),
% 0.21/0.57    inference(resolution,[],[f217,f114])).
% 0.21/0.57  fof(f114,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | r4_lattice3(X1,X2,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f63])).
% 0.21/0.57  fof(f554,plain,(
% 0.21/0.57    ~r4_lattice3(sK14,k15_lattice3(sK14,sK15),sK15) | spl23_13),
% 0.21/0.57    inference(avatar_component_clause,[],[f552])).
% 0.21/0.57  fof(f552,plain,(
% 0.21/0.57    spl23_13 <=> r4_lattice3(sK14,k15_lattice3(sK14,sK15),sK15)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl23_13])])).
% 0.21/0.57  fof(f605,plain,(
% 0.21/0.57    spl23_7 | ~spl23_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f604,f548,f508])).
% 0.21/0.57  fof(f604,plain,(
% 0.21/0.57    sP3(k15_lattice3(sK14,sK15),sK14) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f603,f89])).
% 0.21/0.57  fof(f603,plain,(
% 0.21/0.57    sP3(k15_lattice3(sK14,sK15),sK14) | v2_struct_0(sK14) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f602,f90])).
% 0.21/0.57  fof(f602,plain,(
% 0.21/0.57    sP3(k15_lattice3(sK14,sK15),sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f601,f91])).
% 0.21/0.57  fof(f601,plain,(
% 0.21/0.57    sP3(k15_lattice3(sK14,sK15),sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | ~spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f594,f92])).
% 0.21/0.57  fof(f594,plain,(
% 0.21/0.57    sP3(k15_lattice3(sK14,sK15),sK14) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | ~spl23_12),
% 0.21/0.57    inference(resolution,[],[f549,f111])).
% 0.21/0.57  fof(f111,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP3(X1,X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f31])).
% 0.21/0.57  fof(f31,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (sP3(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(definition_folding,[],[f15,f30,f29,f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> (sP1(X1,X0,X2) & r3_lattice3(X0,X1,X2)))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.57  fof(f30,plain,(
% 0.21/0.57    ! [X1,X0] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> sP2(X2,X0,X1)) | ~sP3(X1,X0))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f14])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).
% 0.21/0.57  fof(f591,plain,(
% 0.21/0.57    spl23_8),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f590])).
% 0.21/0.57  fof(f590,plain,(
% 0.21/0.57    $false | spl23_8),
% 0.21/0.57    inference(subsumption_resolution,[],[f589,f92])).
% 0.21/0.57  fof(f589,plain,(
% 0.21/0.57    ~l3_lattices(sK14) | spl23_8),
% 0.21/0.57    inference(subsumption_resolution,[],[f588,f91])).
% 0.21/0.57  fof(f588,plain,(
% 0.21/0.57    ~v4_lattice3(sK14) | ~l3_lattices(sK14) | spl23_8),
% 0.21/0.57    inference(subsumption_resolution,[],[f587,f89])).
% 0.21/0.57  fof(f587,plain,(
% 0.21/0.57    v2_struct_0(sK14) | ~v4_lattice3(sK14) | ~l3_lattices(sK14) | spl23_8),
% 0.21/0.57    inference(resolution,[],[f520,f154])).
% 0.21/0.57  fof(f154,plain,(
% 0.21/0.57    ( ! [X1] : (sP8(X1) | v2_struct_0(X1) | ~v4_lattice3(X1) | ~l3_lattices(X1)) )),
% 0.21/0.57    inference(resolution,[],[f132,f122])).
% 0.21/0.57  fof(f122,plain,(
% 0.21/0.57    ( ! [X0] : (~sP9(X0) | ~v4_lattice3(X0) | sP8(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f68])).
% 0.21/0.57  fof(f68,plain,(
% 0.21/0.57    ! [X0] : (((v4_lattice3(X0) | ~sP8(X0)) & (sP8(X0) | ~v4_lattice3(X0))) | ~sP9(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f38])).
% 0.21/0.57  fof(f38,plain,(
% 0.21/0.57    ! [X0] : ((v4_lattice3(X0) <=> sP8(X0)) | ~sP9(X0))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 0.21/0.57  fof(f132,plain,(
% 0.21/0.57    ( ! [X0] : (sP9(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f39])).
% 0.21/0.57  fof(f39,plain,(
% 0.21/0.57    ! [X0] : (sP9(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(definition_folding,[],[f19,f38,f37,f36])).
% 0.21/0.57  fof(f36,plain,(
% 0.21/0.57    ! [X2,X0,X1] : (sP7(X2,X0,X1) <=> ! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    ! [X0] : (sP8(X0) <=> ! [X1] : ? [X2] : (sP7(X2,X0,X1) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0] : ((v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v4_lattice3(X0) <=> ! [X1] : ? [X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_lattice3)).
% 0.21/0.57  fof(f520,plain,(
% 0.21/0.57    ~sP8(sK14) | spl23_8),
% 0.21/0.57    inference(avatar_component_clause,[],[f518])).
% 0.21/0.57  fof(f518,plain,(
% 0.21/0.57    spl23_8 <=> sP8(sK14)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl23_8])])).
% 0.21/0.57  fof(f582,plain,(
% 0.21/0.57    ~spl23_8 | spl23_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f581,f548,f518])).
% 0.21/0.57  fof(f581,plain,(
% 0.21/0.57    ~sP8(sK14) | spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f580,f125])).
% 0.21/0.57  fof(f125,plain,(
% 0.21/0.57    ( ! [X0,X3] : (r4_lattice3(X0,sK19(X0,X3),X3) | ~sP8(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f73])).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    ! [X0] : ((sP8(X0) | ! [X2] : (~sP7(X2,X0,sK18(X0)) | ~r4_lattice3(X0,X2,sK18(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : (sP7(sK19(X0,X3),X0,X3) & r4_lattice3(X0,sK19(X0,X3),X3) & m1_subset_1(sK19(X0,X3),u1_struct_0(X0))) | ~sP8(X0)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18,sK19])],[f70,f72,f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    ! [X0] : (? [X1] : ! [X2] : (~sP7(X2,X0,X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) => ! [X2] : (~sP7(X2,X0,sK18(X0)) | ~r4_lattice3(X0,X2,sK18(X0)) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f72,plain,(
% 0.21/0.57    ! [X3,X0] : (? [X4] : (sP7(X4,X0,X3) & r4_lattice3(X0,X4,X3) & m1_subset_1(X4,u1_struct_0(X0))) => (sP7(sK19(X0,X3),X0,X3) & r4_lattice3(X0,sK19(X0,X3),X3) & m1_subset_1(sK19(X0,X3),u1_struct_0(X0))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f70,plain,(
% 0.21/0.57    ! [X0] : ((sP8(X0) | ? [X1] : ! [X2] : (~sP7(X2,X0,X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ? [X4] : (sP7(X4,X0,X3) & r4_lattice3(X0,X4,X3) & m1_subset_1(X4,u1_struct_0(X0))) | ~sP8(X0)))),
% 0.21/0.57    inference(rectify,[],[f69])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ! [X0] : ((sP8(X0) | ? [X1] : ! [X2] : (~sP7(X2,X0,X1) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & (! [X1] : ? [X2] : (sP7(X2,X0,X1) & r4_lattice3(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~sP8(X0)))),
% 0.21/0.57    inference(nnf_transformation,[],[f37])).
% 0.21/0.57  fof(f580,plain,(
% 0.21/0.57    ~r4_lattice3(sK14,sK19(sK14,sK15),sK15) | ~sP8(sK14) | spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f577,f124])).
% 0.21/0.57  fof(f124,plain,(
% 0.21/0.57    ( ! [X0,X3] : (m1_subset_1(sK19(X0,X3),u1_struct_0(X0)) | ~sP8(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f73])).
% 0.21/0.57  fof(f577,plain,(
% 0.21/0.57    ~m1_subset_1(sK19(sK14,sK15),u1_struct_0(sK14)) | ~r4_lattice3(sK14,sK19(sK14,sK15),sK15) | ~sP8(sK14) | spl23_12),
% 0.21/0.57    inference(resolution,[],[f574,f228])).
% 0.21/0.57  fof(f228,plain,(
% 0.21/0.57    ( ! [X0,X1] : (sP4(sK19(X0,X1),X0,X1) | ~sP8(X0)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f227])).
% 0.21/0.57  fof(f227,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~sP8(X0) | sP4(sK19(X0,X1),X0,X1) | sP4(sK19(X0,X1),X0,X1)) )),
% 0.21/0.57    inference(resolution,[],[f221,f119])).
% 0.21/0.57  fof(f119,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK17(X0,X1,X2),X2) | sP4(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f67])).
% 0.21/0.57  fof(f221,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r4_lattice3(X0,sK17(sK19(X0,X1),X0,X2),X1) | ~sP8(X0) | sP4(sK19(X0,X1),X0,X2)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f218,f118])).
% 0.21/0.57  fof(f118,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) | sP4(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f67])).
% 0.21/0.57  fof(f218,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(sK17(sK19(X0,X1),X0,X2),u1_struct_0(X0)) | ~r4_lattice3(X0,sK17(sK19(X0,X1),X0,X2),X1) | ~sP8(X0) | sP4(sK19(X0,X1),X0,X2)) )),
% 0.21/0.57    inference(resolution,[],[f216,f120])).
% 0.21/0.57  fof(f120,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK17(X0,X1,X2)) | sP4(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f67])).
% 0.21/0.57  fof(f216,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r1_lattices(X0,sK19(X0,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~sP8(X0)) )),
% 0.21/0.57    inference(resolution,[],[f128,f126])).
% 0.21/0.57  fof(f126,plain,(
% 0.21/0.57    ( ! [X0,X3] : (sP7(sK19(X0,X3),X0,X3) | ~sP8(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f73])).
% 0.21/0.57  fof(f128,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (~sP7(X0,X1,X2) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f77])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | (~r1_lattices(X1,X0,sK20(X0,X1,X2)) & r4_lattice3(X1,sK20(X0,X1,X2),X2) & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f75,f76])).
% 0.21/0.57  fof(f76,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK20(X0,X1,X2)) & r4_lattice3(X1,sK20(X0,X1,X2),X2) & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 0.21/0.57    inference(rectify,[],[f74])).
% 0.21/0.57  fof(f74,plain,(
% 0.21/0.57    ! [X2,X0,X1] : ((sP7(X2,X0,X1) | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP7(X2,X0,X1)))),
% 0.21/0.57    inference(nnf_transformation,[],[f36])).
% 0.21/0.57  fof(f574,plain,(
% 0.21/0.57    ( ! [X0] : (~sP4(X0,sK14,sK15) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~r4_lattice3(sK14,X0,sK15)) ) | spl23_12),
% 0.21/0.57    inference(resolution,[],[f573,f116])).
% 0.21/0.57  fof(f116,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP5(X0,X1,X2) | ~sP4(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f63])).
% 0.21/0.57  fof(f573,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14))) ) | spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f572,f89])).
% 0.21/0.57  fof(f572,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | v2_struct_0(sK14)) ) | spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f571,f90])).
% 0.21/0.57  fof(f571,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~v10_lattices(sK14) | v2_struct_0(sK14)) ) | spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f570,f91])).
% 0.21/0.57  fof(f570,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14)) ) | spl23_12),
% 0.21/0.57    inference(subsumption_resolution,[],[f569,f92])).
% 0.21/0.57  fof(f569,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14)) ) | spl23_12),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f568])).
% 0.21/0.57  fof(f568,plain,(
% 0.21/0.57    ( ! [X0] : (~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14)) ) | spl23_12),
% 0.21/0.57    inference(resolution,[],[f556,f152])).
% 0.21/0.57  fof(f556,plain,(
% 0.21/0.57    ( ! [X0] : (~sP6(X0,sK14,sK15) | ~sP5(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14))) ) | spl23_12),
% 0.21/0.57    inference(superposition,[],[f550,f113])).
% 0.21/0.57  fof(f550,plain,(
% 0.21/0.57    ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | spl23_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f548])).
% 0.21/0.57  fof(f555,plain,(
% 0.21/0.57    ~spl23_12 | ~spl23_13 | spl23_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f545,f533,f552,f548])).
% 0.21/0.57  fof(f533,plain,(
% 0.21/0.57    spl23_11 <=> sP12(sK15,sK14,k15_lattice3(sK14,sK15))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl23_11])])).
% 0.21/0.57  fof(f545,plain,(
% 0.21/0.57    ~r4_lattice3(sK14,k15_lattice3(sK14,sK15),sK15) | ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | spl23_11),
% 0.21/0.57    inference(resolution,[],[f535,f151])).
% 0.21/0.57  fof(f151,plain,(
% 0.21/0.57    ( ! [X0,X3,X1] : (sP12(X0,X1,X3) | ~r4_lattice3(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.21/0.57    inference(equality_resolution,[],[f147])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (sP12(X0,X1,X2) | ~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f88])).
% 0.21/0.57  fof(f535,plain,(
% 0.21/0.57    ~sP12(sK15,sK14,k15_lattice3(sK14,sK15)) | spl23_11),
% 0.21/0.57    inference(avatar_component_clause,[],[f533])).
% 0.21/0.57  fof(f543,plain,(
% 0.21/0.57    spl23_10),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f542])).
% 0.21/0.57  fof(f542,plain,(
% 0.21/0.57    $false | spl23_10),
% 0.21/0.57    inference(subsumption_resolution,[],[f541,f89])).
% 0.21/0.57  fof(f541,plain,(
% 0.21/0.57    v2_struct_0(sK14) | spl23_10),
% 0.21/0.57    inference(subsumption_resolution,[],[f540,f90])).
% 0.21/0.57  fof(f540,plain,(
% 0.21/0.57    ~v10_lattices(sK14) | v2_struct_0(sK14) | spl23_10),
% 0.21/0.57    inference(subsumption_resolution,[],[f539,f91])).
% 0.21/0.57  fof(f539,plain,(
% 0.21/0.57    ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | spl23_10),
% 0.21/0.57    inference(subsumption_resolution,[],[f537,f92])).
% 0.21/0.57  fof(f537,plain,(
% 0.21/0.57    ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | spl23_10),
% 0.21/0.57    inference(resolution,[],[f531,f148])).
% 0.21/0.57  fof(f531,plain,(
% 0.21/0.57    ~sP13(k15_lattice3(sK14,sK15),sK14,sK15) | spl23_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f529])).
% 0.21/0.57  fof(f529,plain,(
% 0.21/0.57    spl23_10 <=> sP13(k15_lattice3(sK14,sK15),sK14,sK15)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl23_10])])).
% 0.21/0.57  fof(f536,plain,(
% 0.21/0.57    ~spl23_10 | ~spl23_11 | spl23_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f526,f501,f533,f529])).
% 0.21/0.57  fof(f526,plain,(
% 0.21/0.57    ~sP12(sK15,sK14,k15_lattice3(sK14,sK15)) | ~sP13(k15_lattice3(sK14,sK15),sK14,sK15) | spl23_5),
% 0.21/0.57    inference(resolution,[],[f503,f143])).
% 0.21/0.57  fof(f143,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~sP12(X2,X1,X0) | ~sP13(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f84])).
% 0.21/0.57  fof(f503,plain,(
% 0.21/0.57    ~r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15)) | spl23_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f501])).
% 0.21/0.57  fof(f473,plain,(
% 0.21/0.57    spl23_3),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f472])).
% 0.21/0.57  fof(f472,plain,(
% 0.21/0.57    $false | spl23_3),
% 0.21/0.57    inference(subsumption_resolution,[],[f471,f90])).
% 0.21/0.57  fof(f471,plain,(
% 0.21/0.57    ~v10_lattices(sK14) | spl23_3),
% 0.21/0.57    inference(subsumption_resolution,[],[f470,f92])).
% 0.21/0.57  fof(f470,plain,(
% 0.21/0.57    ~l3_lattices(sK14) | ~v10_lattices(sK14) | spl23_3),
% 0.21/0.57    inference(subsumption_resolution,[],[f469,f89])).
% 0.21/0.57  fof(f469,plain,(
% 0.21/0.57    v2_struct_0(sK14) | ~l3_lattices(sK14) | ~v10_lattices(sK14) | spl23_3),
% 0.21/0.57    inference(resolution,[],[f443,f161])).
% 0.21/0.57  fof(f161,plain,(
% 0.21/0.57    ( ! [X6] : (v9_lattices(X6) | v2_struct_0(X6) | ~l3_lattices(X6) | ~v10_lattices(X6)) )),
% 0.21/0.57    inference(resolution,[],[f101,f100])).
% 0.21/0.57  fof(f100,plain,(
% 0.21/0.57    ( ! [X0] : (~sP0(X0) | v9_lattices(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f49])).
% 0.21/0.57  fof(f49,plain,(
% 0.21/0.57    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 0.21/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.57  fof(f101,plain,(
% 0.21/0.57    ( ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f27])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.57    inference(definition_folding,[],[f13,f26])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.57    inference(flattening,[],[f12])).
% 0.21/0.57  fof(f12,plain,(
% 0.21/0.57    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.57  fof(f443,plain,(
% 0.21/0.57    ~v9_lattices(sK14) | spl23_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f441])).
% 0.21/0.57  fof(f441,plain,(
% 0.21/0.57    spl23_3 <=> v9_lattices(sK14)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl23_3])])).
% 0.21/0.57  fof(f468,plain,(
% 0.21/0.57    spl23_2),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f467])).
% 0.21/0.57  fof(f467,plain,(
% 0.21/0.57    $false | spl23_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f466,f90])).
% 0.21/0.57  fof(f466,plain,(
% 0.21/0.57    ~v10_lattices(sK14) | spl23_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f465,f92])).
% 0.21/0.57  fof(f465,plain,(
% 0.21/0.57    ~l3_lattices(sK14) | ~v10_lattices(sK14) | spl23_2),
% 0.21/0.57    inference(subsumption_resolution,[],[f464,f89])).
% 0.21/0.57  fof(f464,plain,(
% 0.21/0.57    v2_struct_0(sK14) | ~l3_lattices(sK14) | ~v10_lattices(sK14) | spl23_2),
% 0.21/0.57    inference(resolution,[],[f439,f160])).
% 0.21/0.57  fof(f160,plain,(
% 0.21/0.57    ( ! [X5] : (v8_lattices(X5) | v2_struct_0(X5) | ~l3_lattices(X5) | ~v10_lattices(X5)) )),
% 0.21/0.57    inference(resolution,[],[f101,f99])).
% 0.21/0.57  fof(f99,plain,(
% 0.21/0.57    ( ! [X0] : (~sP0(X0) | v8_lattices(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f49])).
% 0.21/0.57  fof(f439,plain,(
% 0.21/0.57    ~v8_lattices(sK14) | spl23_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f437])).
% 0.21/0.57  fof(f437,plain,(
% 0.21/0.57    spl23_2 <=> v8_lattices(sK14)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl23_2])])).
% 0.21/0.57  fof(f463,plain,(
% 0.21/0.57    spl23_1),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f462])).
% 0.21/0.57  fof(f462,plain,(
% 0.21/0.57    $false | spl23_1),
% 0.21/0.57    inference(subsumption_resolution,[],[f461,f90])).
% 0.21/0.57  fof(f461,plain,(
% 0.21/0.57    ~v10_lattices(sK14) | spl23_1),
% 0.21/0.57    inference(subsumption_resolution,[],[f460,f92])).
% 0.21/0.57  fof(f460,plain,(
% 0.21/0.57    ~l3_lattices(sK14) | ~v10_lattices(sK14) | spl23_1),
% 0.21/0.57    inference(subsumption_resolution,[],[f459,f89])).
% 0.21/0.57  fof(f459,plain,(
% 0.21/0.57    v2_struct_0(sK14) | ~l3_lattices(sK14) | ~v10_lattices(sK14) | spl23_1),
% 0.21/0.57    inference(resolution,[],[f435,f158])).
% 0.21/0.57  fof(f158,plain,(
% 0.21/0.57    ( ! [X3] : (v6_lattices(X3) | v2_struct_0(X3) | ~l3_lattices(X3) | ~v10_lattices(X3)) )),
% 0.21/0.57    inference(resolution,[],[f101,f97])).
% 0.21/0.57  fof(f97,plain,(
% 0.21/0.57    ( ! [X0] : (~sP0(X0) | v6_lattices(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f49])).
% 0.21/0.57  fof(f435,plain,(
% 0.21/0.57    ~v6_lattices(sK14) | spl23_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f433])).
% 0.21/0.57  fof(f433,plain,(
% 0.21/0.57    spl23_1 <=> v6_lattices(sK14)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl23_1])])).
% 0.21/0.57  fof(f447,plain,(
% 0.21/0.57    ~spl23_1 | ~spl23_2 | ~spl23_3 | spl23_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f431,f445,f441,f437,f433])).
% 0.21/0.57  fof(f431,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~v9_lattices(sK14) | ~v8_lattices(sK14) | ~v6_lattices(sK14) | ~r3_lattice3(sK14,X0,a_2_2_lattice3(sK14,sK15)) | k15_lattice3(sK14,sK15) != X0 | ~sP3(X0,sK14)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f430,f89])).
% 0.21/0.57  fof(f430,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~v9_lattices(sK14) | ~v8_lattices(sK14) | ~v6_lattices(sK14) | v2_struct_0(sK14) | ~r3_lattice3(sK14,X0,a_2_2_lattice3(sK14,sK15)) | k15_lattice3(sK14,sK15) != X0 | ~sP3(X0,sK14)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f427,f92])).
% 0.21/0.57  fof(f427,plain,(
% 0.21/0.57    ( ! [X0] : (~r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~l3_lattices(sK14) | ~v9_lattices(sK14) | ~v8_lattices(sK14) | ~v6_lattices(sK14) | v2_struct_0(sK14) | ~r3_lattice3(sK14,X0,a_2_2_lattice3(sK14,sK15)) | k15_lattice3(sK14,sK15) != X0 | ~sP3(X0,sK14)) )),
% 0.21/0.57    inference(resolution,[],[f420,f190])).
% 0.21/0.57  fof(f190,plain,(
% 0.21/0.57    ( ! [X6] : (~sP1(X6,sK14,a_2_2_lattice3(sK14,sK15)) | ~r3_lattice3(sK14,X6,a_2_2_lattice3(sK14,sK15)) | k15_lattice3(sK14,sK15) != X6 | ~sP3(X6,sK14)) )),
% 0.21/0.57    inference(resolution,[],[f106,f179])).
% 0.21/0.57  fof(f179,plain,(
% 0.21/0.57    ( ! [X0] : (~sP2(a_2_2_lattice3(sK14,sK15),sK14,X0) | k15_lattice3(sK14,sK15) != X0 | ~sP3(X0,sK14)) )),
% 0.21/0.57    inference(superposition,[],[f93,f103])).
% 0.21/0.57  fof(f103,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (k16_lattice3(X1,X2) = X0 | ~sP2(X2,X1,X0) | ~sP3(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ! [X0,X1] : (! [X2] : ((k16_lattice3(X1,X2) = X0 | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | k16_lattice3(X1,X2) != X0)) | ~sP3(X0,X1))),
% 0.21/0.57    inference(rectify,[],[f50])).
% 0.21/0.57  fof(f50,plain,(
% 0.21/0.57    ! [X1,X0] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | k16_lattice3(X0,X2) != X1)) | ~sP3(X1,X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f30])).
% 0.21/0.57  fof(f93,plain,(
% 0.21/0.57    k15_lattice3(sK14,sK15) != k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15))),
% 0.21/0.57    inference(cnf_transformation,[],[f48])).
% 0.21/0.57  fof(f106,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~sP1(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f54])).
% 0.21/0.57  fof(f54,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ~sP1(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) & ((sP1(X2,X1,X0) & r3_lattice3(X1,X2,X0)) | ~sP2(X0,X1,X2)))),
% 0.21/0.57    inference(rectify,[],[f53])).
% 0.21/0.57  fof(f53,plain,(
% 0.21/0.57    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ~sP1(X1,X0,X2) | ~r3_lattice3(X0,X1,X2)) & ((sP1(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP2(X2,X0,X1)))),
% 0.21/0.57    inference(flattening,[],[f52])).
% 0.21/0.57  fof(f52,plain,(
% 0.21/0.57    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | (~sP1(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) & ((sP1(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP2(X2,X0,X1)))),
% 0.21/0.57    inference(nnf_transformation,[],[f29])).
% 0.21/0.57  fof(f420,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v9_lattices(X2) | ~v8_lattices(X2) | ~v6_lattices(X2) | v2_struct_0(X2)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f413])).
% 0.21/0.57  fof(f413,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | sP1(X0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v9_lattices(X2) | ~v8_lattices(X2) | ~v6_lattices(X2) | v2_struct_0(X2) | sP1(X0,X2,X1)) )),
% 0.21/0.57    inference(resolution,[],[f345,f110])).
% 0.21/0.57  fof(f110,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r3_lattices(X1,sK16(X0,X1,X2),X0) | sP1(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f58])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (~r3_lattices(X1,sK16(X0,X1,X2),X0) & r3_lattice3(X1,sK16(X0,X1,X2),X2) & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f56,f57])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r3_lattices(X1,sK16(X0,X1,X2),X0) & r3_lattice3(X1,sK16(X0,X1,X2),X2) & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f56,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 0.21/0.57    inference(rectify,[],[f55])).
% 0.21/0.57  fof(f55,plain,(
% 0.21/0.57    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP1(X1,X0,X2)))),
% 0.21/0.57    inference(nnf_transformation,[],[f28])).
% 0.21/0.57  fof(f345,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (r3_lattices(X1,sK16(X3,X1,X2),X0) | ~r2_hidden(X0,X2) | sP1(X3,X1,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f344,f108])).
% 0.21/0.57  fof(f108,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) | sP1(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f58])).
% 0.21/0.57  fof(f344,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | sP1(X3,X1,X2) | r3_lattices(X1,sK16(X3,X1,X2),X0) | ~m1_subset_1(sK16(X3,X1,X2),u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1)) )),
% 0.21/0.57    inference(subsumption_resolution,[],[f343,f139])).
% 0.21/0.57  fof(f343,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~sP11(X1,sK16(X3,X1,X2)) | sP1(X3,X1,X2) | r3_lattices(X1,sK16(X3,X1,X2),X0) | ~m1_subset_1(sK16(X3,X1,X2),u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1)) )),
% 0.21/0.57    inference(duplicate_literal_removal,[],[f339])).
% 0.21/0.57  fof(f339,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~sP11(X1,sK16(X3,X1,X2)) | sP1(X3,X1,X2) | r3_lattices(X1,sK16(X3,X1,X2),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(sK16(X3,X1,X2),u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1)) )),
% 0.21/0.57    inference(resolution,[],[f246,f141])).
% 0.21/0.57  fof(f141,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f83])).
% 0.21/0.57  fof(f83,plain,(
% 0.21/0.57    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.57    inference(flattening,[],[f22])).
% 0.21/0.57  fof(f22,plain,(
% 0.21/0.57    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.57    inference(ennf_transformation,[],[f2])).
% 0.21/0.57  fof(f2,axiom,(
% 0.21/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.21/0.57  fof(f246,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (r1_lattices(X1,sK16(X2,X1,X3),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X3) | ~sP11(X1,sK16(X2,X1,X3)) | sP1(X2,X1,X3)) )),
% 0.21/0.57    inference(resolution,[],[f213,f109])).
% 0.21/0.57  fof(f109,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK16(X0,X1,X2),X2) | sP1(X0,X1,X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f58])).
% 0.21/0.57  fof(f213,plain,(
% 0.21/0.57    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X2,X3,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | r1_lattices(X2,X3,X0) | ~r2_hidden(X0,X1) | ~sP11(X2,X3)) )),
% 0.21/0.57    inference(resolution,[],[f135,f133])).
% 0.21/0.57  fof(f133,plain,(
% 0.21/0.57    ( ! [X2,X0,X1] : (sP10(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | ~sP11(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f78])).
% 0.21/0.57  fof(f135,plain,(
% 0.21/0.57    ( ! [X4,X2,X0,X1] : (~sP10(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f82])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (10560)------------------------------
% 0.21/0.57  % (10560)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (10560)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (10560)Memory used [KB]: 6524
% 0.21/0.57  % (10560)Time elapsed: 0.145 s
% 0.21/0.57  % (10560)------------------------------
% 0.21/0.57  % (10560)------------------------------
% 0.21/0.57  % (10568)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.58  % (10555)Success in time 0.212 s
%------------------------------------------------------------------------------
