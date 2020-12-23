%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:40 EST 2020

% Result     : Theorem 3.12s
% Output     : Refutation 3.81s
% Verified   : 
% Statistics : Number of formulae       :  310 (1007 expanded)
%              Number of leaves         :   37 ( 307 expanded)
%              Depth                    :   33
%              Number of atoms          : 1511 (5155 expanded)
%              Number of equality atoms :   80 ( 534 expanded)
%              Maximal formula depth    :   15 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2471,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1680,f1687,f1706,f2346,f2355,f2378,f2451,f2470])).

fof(f2470,plain,
    ( ~ spl22_2
    | ~ spl22_6 ),
    inference(avatar_split_clause,[],[f2469,f1699,f1659])).

fof(f1659,plain,
    ( spl22_2
  <=> r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_2])])).

fof(f1699,plain,
    ( spl22_6
  <=> m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_6])])).

fof(f2469,plain,
    ( ~ r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15))
    | ~ spl22_6 ),
    inference(subsumption_resolution,[],[f2468,f90])).

fof(f90,plain,(
    ~ v2_struct_0(sK14) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( k15_lattice3(sK14,sK15) != k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15))
    & l3_lattices(sK14)
    & v4_lattice3(sK14)
    & v10_lattices(sK14)
    & ~ v2_struct_0(sK14) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15])],[f12,f50,f49])).

fof(f49,plain,
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

fof(f50,plain,
    ( ? [X1] : k15_lattice3(sK14,X1) != k16_lattice3(sK14,a_2_2_lattice3(sK14,X1))
   => k15_lattice3(sK14,sK15) != k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).

fof(f2468,plain,
    ( ~ r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15))
    | v2_struct_0(sK14)
    | ~ spl22_6 ),
    inference(subsumption_resolution,[],[f2467,f92])).

fof(f92,plain,(
    v4_lattice3(sK14) ),
    inference(cnf_transformation,[],[f51])).

fof(f2467,plain,
    ( ~ r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15))
    | ~ v4_lattice3(sK14)
    | v2_struct_0(sK14)
    | ~ spl22_6 ),
    inference(subsumption_resolution,[],[f2466,f91])).

fof(f91,plain,(
    v10_lattices(sK14) ),
    inference(cnf_transformation,[],[f51])).

fof(f2466,plain,
    ( ~ r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15))
    | ~ v10_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | v2_struct_0(sK14)
    | ~ spl22_6 ),
    inference(subsumption_resolution,[],[f2465,f93])).

fof(f93,plain,(
    l3_lattices(sK14) ),
    inference(cnf_transformation,[],[f51])).

fof(f2465,plain,
    ( ~ r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15))
    | ~ l3_lattices(sK14)
    | ~ v10_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | v2_struct_0(sK14)
    | ~ spl22_6 ),
    inference(subsumption_resolution,[],[f1885,f1700])).

fof(f1700,plain,
    ( m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ spl22_6 ),
    inference(avatar_component_clause,[],[f1699])).

fof(f1885,plain,
    ( ~ r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15))
    | ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ l3_lattices(sK14)
    | ~ v10_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | v2_struct_0(sK14) ),
    inference(trivial_inequality_removal,[],[f1884])).

fof(f1884,plain,
    ( k15_lattice3(sK14,sK15) != k15_lattice3(sK14,sK15)
    | ~ r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15))
    | ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ l3_lattices(sK14)
    | ~ v10_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | v2_struct_0(sK14) ),
    inference(duplicate_literal_removal,[],[f1877])).

fof(f1877,plain,
    ( k15_lattice3(sK14,sK15) != k15_lattice3(sK14,sK15)
    | ~ r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15))
    | ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ l3_lattices(sK14)
    | ~ v10_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | v2_struct_0(sK14)
    | ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) ),
    inference(resolution,[],[f1649,f1079])).

fof(f1079,plain,(
    ! [X4,X3] :
      ( r3_lattice3(X3,k15_lattice3(X3,X4),a_2_2_lattice3(X3,X4))
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3)
      | ~ v4_lattice3(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(k15_lattice3(X3,X4),u1_struct_0(X3)) ) ),
    inference(subsumption_resolution,[],[f1075,f129])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP9(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP9(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f22,f41,f40])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( sP8(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP8(X1,X0,X2) )
      | ~ sP9(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).

fof(f1075,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(k15_lattice3(X3,X4),u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3)
      | ~ v4_lattice3(X3)
      | v2_struct_0(X3)
      | r3_lattice3(X3,k15_lattice3(X3,X4),a_2_2_lattice3(X3,X4))
      | ~ sP9(X3,k15_lattice3(X3,X4)) ) ),
    inference(resolution,[],[f1067,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ sP8(X1,X0,X2)
      | r3_lattice3(X0,X1,X2)
      | ~ sP9(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP8(X1,X0,X2) )
          & ( sP8(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP9(X0,X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f1067,plain,(
    ! [X0,X1] :
      ( sP8(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f1055])).

fof(f1055,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | ~ v4_lattice3(X0)
      | sP8(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP8(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1)) ) ),
    inference(resolution,[],[f803,f355])).

fof(f355,plain,(
    ! [X14,X12,X15,X13] :
      ( r4_lattice3(X14,sK19(X12,X13,a_2_2_lattice3(X14,X15)),X15)
      | ~ l3_lattices(X14)
      | ~ v4_lattice3(X14)
      | ~ v10_lattices(X14)
      | v2_struct_0(X14)
      | sP8(X12,X13,a_2_2_lattice3(X14,X15)) ) ),
    inference(resolution,[],[f351,f171])).

fof(f171,plain,(
    ! [X2,X0,X1] :
      ( ~ sP10(X0,X1,X2)
      | r4_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,X2,X0)
      | ~ sP10(X0,X1,X2)
      | ~ sP10(X0,X1,X2) ) ),
    inference(superposition,[],[f135,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( sK20(X0,X1,X2) = X2
      | ~ sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( sP10(X0,X1,X2)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r4_lattice3(X1,sK20(X0,X1,X2),X0)
          & sK20(X0,X1,X2) = X2
          & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP10(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f82,f83])).

fof(f83,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK20(X0,X1,X2),X0)
        & sK20(X0,X1,X2) = X2
        & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( sP10(X0,X1,X2)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r4_lattice3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP10(X0,X1,X2) ) ) ),
    inference(rectify,[],[f81])).

fof(f81,plain,(
    ! [X2,X1,X0] :
      ( ( sP10(X2,X1,X0)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP10(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( sP10(X2,X1,X0)
    <=> ? [X3] :
          ( r4_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK20(X0,X1,X2),X0)
      | ~ sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f351,plain,(
    ! [X2,X0,X3,X1] :
      ( sP10(X0,X1,sK19(X2,X3,a_2_2_lattice3(X1,X0)))
      | sP8(X2,X3,a_2_2_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f211,f137])).

fof(f137,plain,(
    ! [X2,X0,X1] :
      ( sP11(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( sP11(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f26,f44,f43])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> sP10(X2,X1,X0) )
      | ~ sP11(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f211,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ sP11(sK19(X6,X7,a_2_2_lattice3(X5,X4)),X5,X4)
      | sP10(X4,X5,sK19(X6,X7,a_2_2_lattice3(X5,X4)))
      | sP8(X6,X7,a_2_2_lattice3(X5,X4)) ) ),
    inference(resolution,[],[f131,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK19(X0,X1,X2),X2)
      | sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( ( sP8(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK19(X0,X1,X2))
          & r2_hidden(sK19(X0,X1,X2),X2)
          & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP8(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f77,f78])).

fof(f78,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK19(X0,X1,X2))
        & r2_hidden(sK19(X0,X1,X2),X2)
        & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
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
    inference(rectify,[],[f76])).

fof(f76,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | sP10(X2,X1,X0)
      | ~ sP11(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ~ sP10(X2,X1,X0) )
        & ( sP10(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ sP11(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f803,plain,(
    ! [X4,X5,X3] :
      ( ~ r4_lattice3(X3,sK19(k15_lattice3(X3,X4),X3,X5),X4)
      | v2_struct_0(X3)
      | ~ m1_subset_1(k15_lattice3(X3,X4),u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3)
      | ~ v4_lattice3(X3)
      | sP8(k15_lattice3(X3,X4),X3,X5) ) ),
    inference(subsumption_resolution,[],[f798,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1))
      | sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f798,plain,(
    ! [X4,X5,X3] :
      ( ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ m1_subset_1(k15_lattice3(X3,X4),u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ r4_lattice3(X3,sK19(k15_lattice3(X3,X4),X3,X5),X4)
      | ~ m1_subset_1(sK19(k15_lattice3(X3,X4),X3,X5),u1_struct_0(X3))
      | ~ v4_lattice3(X3)
      | sP8(k15_lattice3(X3,X4),X3,X5) ) ),
    inference(resolution,[],[f305,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK19(X0,X1,X2))
      | sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f305,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X2)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_lattice3(X0) ) ),
    inference(resolution,[],[f295,f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r4_lattice3(X1,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK17(X0,X1,X2))
          & r4_lattice3(X1,sK17(X0,X1,X2),X2)
          & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r4_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK17(X0,X1,X2))
        & r4_lattice3(X1,sK17(X0,X1,X2),X2)
        & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
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
    inference(rectify,[],[f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X0,X1)
    <=> ! [X3] :
          ( r1_lattices(X0,X2,X3)
          | ~ r4_lattice3(X0,X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f295,plain,(
    ! [X0,X1] :
      ( sP3(k15_lattice3(X0,X1),X0,X1)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f251,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | sP3(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ~ sP3(X2,X1,X0)
        | ~ r4_lattice3(X1,X2,X0) )
      & ( ( sP3(X2,X1,X0)
          & r4_lattice3(X1,X2,X0) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X1,X0,X2] :
      ( ( sP4(X1,X0,X2)
        | ~ sP3(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP3(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP4(X1,X0,X2) ) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X1,X0,X2] :
      ( ( sP4(X1,X0,X2)
        | ~ sP3(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP3(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP4(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( sP4(X1,X0,X2)
    <=> ( sP3(X2,X0,X1)
        & r4_lattice3(X0,X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f251,plain,(
    ! [X0,X1] :
      ( sP4(X1,X0,k15_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f149,f146])).

fof(f146,plain,(
    ! [X2,X1] :
      ( ~ sP5(k15_lattice3(X1,X2),X1,X2)
      | sP4(X2,X1,k15_lattice3(X1,X2)) ) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X1,X0)
      | k15_lattice3(X1,X2) != X0
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( ( k15_lattice3(X1,X2) = X0
          | ~ sP4(X2,X1,X0) )
        & ( sP4(X2,X1,X0)
          | k15_lattice3(X1,X2) != X0 ) )
      | ~ sP5(X0,X1,X2) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ( ( k15_lattice3(X0,X1) = X2
          | ~ sP4(X1,X0,X2) )
        & ( sP4(X1,X0,X2)
          | k15_lattice3(X0,X1) != X2 ) )
      | ~ sP5(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ( k15_lattice3(X0,X1) = X2
      <=> sP4(X1,X0,X2) )
      | ~ sP5(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(definition_folding,[],[f16,f35,f34,f33])).

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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).

fof(f1649,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK14,X0,a_2_2_lattice3(sK14,sK15))
      | k15_lattice3(sK14,sK15) != X0
      | ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15))
      | ~ m1_subset_1(X0,u1_struct_0(sK14)) ) ),
    inference(resolution,[],[f1643,f148])).

fof(f148,plain,(
    ! [X0,X3,X1] :
      ( sP12(X0,X1,X3)
      | ~ r3_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f143])).

fof(f143,plain,(
    ! [X2,X0,X3,X1] :
      ( sP12(X0,X1,X2)
      | ~ r3_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( ( sP12(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r3_lattice3(X1,sK21(X0,X1,X2),X0)
          & sK21(X0,X1,X2) = X2
          & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP12(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f87,f88])).

fof(f88,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK21(X0,X1,X2),X0)
        & sK21(X0,X1,X2) = X2
        & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( ( sP12(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattice3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP12(X0,X1,X2) ) ) ),
    inference(rectify,[],[f86])).

fof(f86,plain,(
    ! [X2,X1,X0] :
      ( ( sP12(X2,X1,X0)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP12(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( sP12(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP12])])).

fof(f1643,plain,(
    ! [X0] :
      ( ~ sP12(a_2_2_lattice3(sK14,sK15),sK14,X0)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15))
      | k15_lattice3(sK14,sK15) != X0 ) ),
    inference(subsumption_resolution,[],[f1642,f92])).

fof(f1642,plain,(
    ! [X0] :
      ( k15_lattice3(sK14,sK15) != X0
      | ~ v4_lattice3(sK14)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15))
      | ~ sP12(a_2_2_lattice3(sK14,sK15),sK14,X0) ) ),
    inference(subsumption_resolution,[],[f1641,f93])).

fof(f1641,plain,(
    ! [X0] :
      ( k15_lattice3(sK14,sK15) != X0
      | ~ l3_lattices(sK14)
      | ~ v4_lattice3(sK14)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15))
      | ~ sP12(a_2_2_lattice3(sK14,sK15),sK14,X0) ) ),
    inference(subsumption_resolution,[],[f1640,f90])).

fof(f1640,plain,(
    ! [X0] :
      ( k15_lattice3(sK14,sK15) != X0
      | v2_struct_0(sK14)
      | ~ l3_lattices(sK14)
      | ~ v4_lattice3(sK14)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15))
      | ~ sP12(a_2_2_lattice3(sK14,sK15),sK14,X0) ) ),
    inference(subsumption_resolution,[],[f1533,f91])).

fof(f1533,plain,(
    ! [X0] :
      ( k15_lattice3(sK14,sK15) != X0
      | ~ v10_lattices(sK14)
      | v2_struct_0(sK14)
      | ~ l3_lattices(sK14)
      | ~ v4_lattice3(sK14)
      | ~ r2_hidden(X0,a_2_2_lattice3(sK14,sK15))
      | ~ sP12(a_2_2_lattice3(sK14,sK15),sK14,X0) ) ),
    inference(superposition,[],[f94,f1526])).

fof(f1526,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X1,X2) = X0
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ r2_hidden(X0,X2)
      | ~ sP12(X2,X1,X0) ) ),
    inference(subsumption_resolution,[],[f1525,f144])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( sP13(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( sP13(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f28,f47,f46])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> sP12(X2,X1,X0) )
      | ~ sP13(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP13])])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

fof(f1525,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | k16_lattice3(X1,X2) = X0
      | ~ r2_hidden(X0,X2)
      | ~ sP12(X2,X1,X0)
      | ~ sP13(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f1522,f175])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ sP12(X0,X1,X2)
      | m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X1))
      | ~ sP12(X0,X1,X2)
      | ~ sP12(X0,X1,X2) ) ),
    inference(superposition,[],[f140,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( sK21(X0,X1,X2) = X2
      | ~ sP12(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1))
      | ~ sP12(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f1522,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | k16_lattice3(X1,X2) = X0
      | ~ r2_hidden(X0,X2)
      | ~ sP12(X2,X1,X0)
      | ~ sP13(X0,X1,X2) ) ),
    inference(resolution,[],[f1489,f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ sP12(X2,X1,X0)
      | ~ sP13(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ~ sP12(X2,X1,X0) )
        & ( sP12(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ sP13(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f1489,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X8,a_2_1_lattice3(X6,X7))
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v4_lattice3(X6)
      | ~ v10_lattices(X6)
      | v2_struct_0(X6)
      | ~ l3_lattices(X6)
      | k16_lattice3(X6,X7) = X8
      | ~ r2_hidden(X8,X7) ) ),
    inference(duplicate_literal_removal,[],[f1474])).

fof(f1474,plain,(
    ! [X6,X8,X7] :
      ( k16_lattice3(X6,X7) = X8
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ v4_lattice3(X6)
      | ~ v10_lattices(X6)
      | v2_struct_0(X6)
      | ~ l3_lattices(X6)
      | ~ r2_hidden(X8,a_2_1_lattice3(X6,X7))
      | ~ r2_hidden(X8,X7)
      | ~ l3_lattices(X6)
      | v2_struct_0(X6)
      | ~ m1_subset_1(X8,u1_struct_0(X6)) ) ),
    inference(resolution,[],[f812,f451])).

fof(f451,plain,(
    ! [X6,X4,X5] :
      ( r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | ~ m1_subset_1(X4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f450,f122])).

fof(f122,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP7(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP7(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f20,f38,f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( sP6(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP6(X1,X0,X2) )
      | ~ sP7(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).

fof(f450,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6))
      | ~ sP7(X5,X4) ) ),
    inference(resolution,[],[f448,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP7(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP6(X1,X0,X2) )
          & ( sP6(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP7(X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f448,plain,(
    ! [X2,X0,X1] :
      ( sP6(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f447,f163])).

fof(f163,plain,(
    ! [X10,X8,X9] :
      ( sP9(X8,sK18(X9,X8,X10))
      | ~ l3_lattices(X8)
      | v2_struct_0(X8)
      | sP6(X9,X8,X10) ) ),
    inference(resolution,[],[f129,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1))
      | sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( sP6(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK18(X0,X1,X2),X0)
          & r2_hidden(sK18(X0,X1,X2),X2)
          & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP6(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f72,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK18(X0,X1,X2),X0)
        & r2_hidden(sK18(X0,X1,X2),X2)
        & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
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
    inference(rectify,[],[f71])).

fof(f71,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f447,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ sP9(X2,sK18(X0,X2,a_2_1_lattice3(X2,X1)))
      | sP6(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f446])).

fof(f446,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ sP9(X2,sK18(X0,X2,a_2_1_lattice3(X2,X1)))
      | sP6(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP6(X0,X2,a_2_1_lattice3(X2,X1)) ) ),
    inference(resolution,[],[f265,f364])).

fof(f364,plain,(
    ! [X14,X12,X15,X13] :
      ( r3_lattice3(X14,sK18(X12,X13,a_2_1_lattice3(X14,X15)),X15)
      | ~ l3_lattices(X14)
      | v2_struct_0(X14)
      | sP6(X12,X13,a_2_1_lattice3(X14,X15)) ) ),
    inference(resolution,[],[f360,f177])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( ~ sP12(X0,X1,X2)
      | r3_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f176])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,X2,X0)
      | ~ sP12(X0,X1,X2)
      | ~ sP12(X0,X1,X2) ) ),
    inference(superposition,[],[f142,f141])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK21(X0,X1,X2),X0)
      | ~ sP12(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f360,plain,(
    ! [X2,X0,X3,X1] :
      ( sP12(X0,X1,sK18(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP6(X2,X3,a_2_1_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f214,f144])).

fof(f214,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP13(sK18(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0)
      | sP12(X0,X1,sK18(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP6(X2,X3,a_2_1_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f138,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK18(X0,X1,X2),X2)
      | sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | sP12(X2,X1,X0)
      | ~ sP13(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f265,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r3_lattice3(X9,sK18(X8,X9,X11),X10)
      | ~ r2_hidden(X8,X10)
      | ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ sP9(X9,sK18(X8,X9,X11))
      | sP6(X8,X9,X11) ) ),
    inference(resolution,[],[f240,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK18(X0,X1,X2),X0)
      | sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f240,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X2,X3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ r3_lattice3(X2,X3,X1)
      | ~ sP9(X2,X3) ) ),
    inference(resolution,[],[f125,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( sP8(X1,X0,X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP9(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f125,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP8(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f812,plain,(
    ! [X12,X10,X11] :
      ( ~ r4_lattice3(X10,X12,a_2_1_lattice3(X10,X11))
      | k16_lattice3(X10,X11) = X12
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ v4_lattice3(X10)
      | ~ v10_lattices(X10)
      | v2_struct_0(X10)
      | ~ l3_lattices(X10)
      | ~ r2_hidden(X12,a_2_1_lattice3(X10,X11)) ) ),
    inference(duplicate_literal_removal,[],[f811])).

fof(f811,plain,(
    ! [X12,X10,X11] :
      ( ~ l3_lattices(X10)
      | k16_lattice3(X10,X11) = X12
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ v4_lattice3(X10)
      | ~ v10_lattices(X10)
      | v2_struct_0(X10)
      | ~ r4_lattice3(X10,X12,a_2_1_lattice3(X10,X11))
      | ~ m1_subset_1(X12,u1_struct_0(X10))
      | ~ r2_hidden(X12,a_2_1_lattice3(X10,X11))
      | ~ l3_lattices(X10)
      | v2_struct_0(X10) ) ),
    inference(resolution,[],[f338,f395])).

fof(f395,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f394])).

fof(f394,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | sP3(X0,X2,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP3(X0,X2,X1) ) ),
    inference(resolution,[],[f392,f154])).

fof(f154,plain,(
    ! [X6,X7,X5] :
      ( sP7(X5,sK17(X6,X5,X7))
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | sP3(X6,X5,X7) ) ),
    inference(resolution,[],[f122,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f392,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X1,sK17(X0,X1,X2))
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | sP3(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f390])).

fof(f390,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ sP7(X1,sK17(X0,X1,X2))
      | sP3(X0,X1,X2)
      | sP3(X0,X1,X2) ) ),
    inference(resolution,[],[f261,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK17(X0,X1,X2))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f261,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X1,X0,sK17(X2,X1,X3))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X3)
      | ~ sP7(X1,sK17(X2,X1,X3))
      | sP3(X2,X1,X3) ) ),
    inference(resolution,[],[f230,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK17(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f230,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_lattice3(X2,X3,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | r1_lattices(X2,X0,X3)
      | ~ r2_hidden(X0,X1)
      | ~ sP7(X2,X3) ) ),
    inference(resolution,[],[f118,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( sP6(X1,X0,X2)
      | ~ r4_lattice3(X0,X1,X2)
      | ~ sP7(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f118,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP6(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f338,plain,(
    ! [X6,X7,X5] :
      ( ~ sP3(X7,X5,a_2_1_lattice3(X5,X6))
      | ~ l3_lattices(X5)
      | k16_lattice3(X5,X6) = X7
      | ~ m1_subset_1(X7,u1_struct_0(X5))
      | ~ v4_lattice3(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | ~ r4_lattice3(X5,X7,a_2_1_lattice3(X5,X6)) ) ),
    inference(resolution,[],[f321,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X1,X2)
      | ~ sP3(X2,X1,X0)
      | ~ r4_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f321,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(a_2_1_lattice3(X0,X1),X0,X2)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | k16_lattice3(X0,X1) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ sP4(a_2_1_lattice3(X0,X1),X0,X2)
      | k16_lattice3(X0,X1) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f207,f149])).

fof(f207,plain,(
    ! [X4,X2,X3] :
      ( ~ sP5(X4,X2,a_2_1_lattice3(X2,X3))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | ~ sP4(a_2_1_lattice3(X2,X3),X2,X4)
      | k16_lattice3(X2,X3) = X4 ) ),
    inference(superposition,[],[f115,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X1,X2) = X0
      | ~ sP4(X2,X1,X0)
      | ~ sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattice3)).

fof(f94,plain,(
    k15_lattice3(sK14,sK15) != k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)) ),
    inference(cnf_transformation,[],[f51])).

fof(f2451,plain,
    ( ~ spl22_6
    | spl22_7 ),
    inference(avatar_contradiction_clause,[],[f2450])).

fof(f2450,plain,
    ( $false
    | ~ spl22_6
    | spl22_7 ),
    inference(subsumption_resolution,[],[f2449,f93])).

fof(f2449,plain,
    ( ~ l3_lattices(sK14)
    | ~ spl22_6
    | spl22_7 ),
    inference(subsumption_resolution,[],[f2448,f1700])).

fof(f2448,plain,
    ( ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ l3_lattices(sK14)
    | spl22_7 ),
    inference(subsumption_resolution,[],[f2447,f90])).

fof(f2447,plain,
    ( v2_struct_0(sK14)
    | ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ l3_lattices(sK14)
    | spl22_7 ),
    inference(subsumption_resolution,[],[f2446,f91])).

fof(f2446,plain,
    ( ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ l3_lattices(sK14)
    | spl22_7 ),
    inference(subsumption_resolution,[],[f2444,f92])).

fof(f2444,plain,
    ( ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | ~ l3_lattices(sK14)
    | spl22_7 ),
    inference(resolution,[],[f1705,f296])).

fof(f296,plain,(
    ! [X2,X3] :
      ( r4_lattice3(X2,k15_lattice3(X2,X3),X3)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(k15_lattice3(X2,X3),u1_struct_0(X2))
      | ~ l3_lattices(X2) ) ),
    inference(resolution,[],[f251,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | r4_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f1705,plain,
    ( ~ r4_lattice3(sK14,k15_lattice3(sK14,sK15),sK15)
    | spl22_7 ),
    inference(avatar_component_clause,[],[f1703])).

fof(f1703,plain,
    ( spl22_7
  <=> r4_lattice3(sK14,k15_lattice3(sK14,sK15),sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_7])])).

fof(f2378,plain,(
    spl22_10 ),
    inference(avatar_contradiction_clause,[],[f2377])).

fof(f2377,plain,
    ( $false
    | spl22_10 ),
    inference(subsumption_resolution,[],[f2376,f92])).

fof(f2376,plain,
    ( ~ v4_lattice3(sK14)
    | spl22_10 ),
    inference(subsumption_resolution,[],[f2375,f93])).

fof(f2375,plain,
    ( ~ l3_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | spl22_10 ),
    inference(subsumption_resolution,[],[f2374,f90])).

fof(f2374,plain,
    ( v2_struct_0(sK14)
    | ~ l3_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | spl22_10 ),
    inference(subsumption_resolution,[],[f2369,f91])).

fof(f2369,plain,
    ( ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ l3_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | spl22_10 ),
    inference(resolution,[],[f2345,f1237])).

fof(f1237,plain,(
    ! [X4,X3] :
      ( r4_lattice3(X3,k16_lattice3(X3,a_2_2_lattice3(X3,X4)),X4)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3) ) ),
    inference(subsumption_resolution,[],[f1231,f156])).

fof(f156,plain,(
    ! [X0,X1] :
      ( sP7(X0,k16_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X0,X1] :
      ( sP7(X0,k16_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f122,f130])).

fof(f130,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).

fof(f1231,plain,(
    ! [X4,X3] :
      ( ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | r4_lattice3(X3,k16_lattice3(X3,a_2_2_lattice3(X3,X4)),X4)
      | ~ sP7(X3,k16_lattice3(X3,a_2_2_lattice3(X3,X4))) ) ),
    inference(resolution,[],[f1229,f117])).

fof(f1229,plain,(
    ! [X0,X1] :
      ( sP6(k16_lattice3(X0,a_2_2_lattice3(X0,X1)),X0,X1)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f1221])).

fof(f1221,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP6(k16_lattice3(X0,a_2_2_lattice3(X0,X1)),X0,X1)
      | sP6(k16_lattice3(X0,a_2_2_lattice3(X0,X1)),X0,X1) ) ),
    inference(resolution,[],[f1211,f120])).

fof(f1211,plain,(
    ! [X21,X19,X20] :
      ( ~ r2_hidden(sK18(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21),X20)
      | ~ l3_lattices(X19)
      | ~ v4_lattice3(X19)
      | ~ v10_lattices(X19)
      | v2_struct_0(X19)
      | sP6(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21) ) ),
    inference(subsumption_resolution,[],[f1201,f119])).

fof(f1201,plain,(
    ! [X21,X19,X20] :
      ( ~ r2_hidden(sK18(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21),X20)
      | ~ l3_lattices(X19)
      | ~ v4_lattice3(X19)
      | ~ v10_lattices(X19)
      | v2_struct_0(X19)
      | ~ m1_subset_1(sK18(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21),u1_struct_0(X19))
      | sP6(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21) ) ),
    inference(duplicate_literal_removal,[],[f1200])).

fof(f1200,plain,(
    ! [X21,X19,X20] :
      ( ~ r2_hidden(sK18(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21),X20)
      | ~ l3_lattices(X19)
      | ~ v4_lattice3(X19)
      | ~ v10_lattices(X19)
      | v2_struct_0(X19)
      | ~ m1_subset_1(sK18(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21),u1_struct_0(X19))
      | v2_struct_0(X19)
      | ~ v4_lattice3(X19)
      | sP6(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21)
      | ~ v10_lattices(X19)
      | ~ l3_lattices(X19) ) ),
    inference(resolution,[],[f1194,f606])).

fof(f606,plain,(
    ! [X4,X2,X3] :
      ( ~ r3_lattice3(X2,sK18(k16_lattice3(X2,X3),X2,X4),X3)
      | v2_struct_0(X2)
      | ~ v4_lattice3(X2)
      | sP6(k16_lattice3(X2,X3),X2,X4)
      | ~ v10_lattices(X2)
      | ~ l3_lattices(X2) ) ),
    inference(subsumption_resolution,[],[f601,f119])).

fof(f601,plain,(
    ! [X4,X2,X3] :
      ( ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | ~ v4_lattice3(X2)
      | sP6(k16_lattice3(X2,X3),X2,X4)
      | ~ v10_lattices(X2)
      | ~ r3_lattice3(X2,sK18(k16_lattice3(X2,X3),X2,X4),X3)
      | ~ m1_subset_1(sK18(k16_lattice3(X2,X3),X2,X4),u1_struct_0(X2)) ) ),
    inference(resolution,[],[f592,f148])).

fof(f592,plain,(
    ! [X2,X0,X1] :
      ( ~ sP12(X1,X0,sK18(k16_lattice3(X0,X1),X0,X2))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | sP6(k16_lattice3(X0,X1),X0,X2)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f586,f144])).

fof(f586,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | sP6(k16_lattice3(X0,X1),X0,X2)
      | ~ sP12(X1,X0,sK18(k16_lattice3(X0,X1),X0,X2))
      | ~ sP13(sK18(k16_lattice3(X0,X1),X0,X2),X0,X1) ) ),
    inference(resolution,[],[f424,f139])).

fof(f424,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK18(k16_lattice3(X0,X1),X0,X2),a_2_1_lattice3(X0,X1))
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | sP6(k16_lattice3(X0,X1),X0,X2) ) ),
    inference(subsumption_resolution,[],[f422,f119])).

fof(f422,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(sK18(k16_lattice3(X0,X1),X0,X2),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(sK18(k16_lattice3(X0,X1),X0,X2),a_2_1_lattice3(X0,X1))
      | sP6(k16_lattice3(X0,X1),X0,X2) ) ),
    inference(resolution,[],[f304,f121])).

fof(f304,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,k16_lattice3(X0,X2))
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2)) ) ),
    inference(subsumption_resolution,[],[f302,f156])).

fof(f302,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattices(X0,X1,k16_lattice3(X0,X2))
      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X2))
      | ~ sP7(X0,k16_lattice3(X0,X2)) ) ),
    inference(resolution,[],[f293,f230])).

fof(f293,plain,(
    ! [X2,X3] :
      ( r4_lattice3(X2,k16_lattice3(X2,X3),a_2_1_lattice3(X2,X3))
      | v2_struct_0(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | ~ l3_lattices(X2) ) ),
    inference(resolution,[],[f291,f107])).

fof(f291,plain,(
    ! [X0,X1] :
      ( sP4(a_2_1_lattice3(X0,X1),X0,k16_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f290,f130])).

fof(f290,plain,(
    ! [X0,X1] :
      ( sP4(a_2_1_lattice3(X0,X1),X0,k16_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,(
    ! [X0,X1] :
      ( sP4(a_2_1_lattice3(X0,X1),X0,k16_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f209,f149])).

fof(f209,plain,(
    ! [X4,X3] :
      ( ~ sP5(k16_lattice3(X3,X4),X3,a_2_1_lattice3(X3,X4))
      | sP4(a_2_1_lattice3(X3,X4),X3,k16_lattice3(X3,X4))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f146,f115])).

fof(f1194,plain,(
    ! [X6,X4,X5] :
      ( r3_lattice3(X5,X4,a_2_2_lattice3(X5,X6))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | ~ v4_lattice3(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | ~ m1_subset_1(X4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f1193,f129])).

fof(f1193,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | ~ v4_lattice3(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | r3_lattice3(X5,X4,a_2_2_lattice3(X5,X6))
      | ~ sP9(X5,X4) ) ),
    inference(resolution,[],[f1190,f124])).

fof(f1190,plain,(
    ! [X2,X0,X1] :
      ( sP8(X0,X2,a_2_2_lattice3(X2,X1))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f1188])).

fof(f1188,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | sP8(X0,X2,a_2_2_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | sP8(X0,X2,a_2_2_lattice3(X2,X1)) ) ),
    inference(resolution,[],[f413,f128])).

fof(f413,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( r1_lattices(X10,X9,sK19(X12,X13,a_2_2_lattice3(X10,X11)))
      | ~ r2_hidden(X9,X11)
      | ~ m1_subset_1(X9,u1_struct_0(X10))
      | sP8(X12,X13,a_2_2_lattice3(X10,X11))
      | ~ l3_lattices(X10)
      | ~ v4_lattice3(X10)
      | ~ v10_lattices(X10)
      | v2_struct_0(X10) ) ),
    inference(subsumption_resolution,[],[f411,f358])).

fof(f358,plain,(
    ! [X6,X4,X7,X5] :
      ( sP7(X6,sK19(X4,X5,a_2_2_lattice3(X6,X7)))
      | ~ l3_lattices(X6)
      | ~ v4_lattice3(X6)
      | ~ v10_lattices(X6)
      | v2_struct_0(X6)
      | sP8(X4,X5,a_2_2_lattice3(X6,X7)) ) ),
    inference(duplicate_literal_removal,[],[f353])).

fof(f353,plain,(
    ! [X6,X4,X7,X5] :
      ( sP8(X4,X5,a_2_2_lattice3(X6,X7))
      | ~ l3_lattices(X6)
      | ~ v4_lattice3(X6)
      | ~ v10_lattices(X6)
      | v2_struct_0(X6)
      | sP7(X6,sK19(X4,X5,a_2_2_lattice3(X6,X7)))
      | ~ l3_lattices(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f351,f232])).

fof(f232,plain,(
    ! [X2,X0,X1] :
      ( ~ sP10(X0,X1,X2)
      | sP7(X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,(
    ! [X2,X0,X1] :
      ( sP7(X1,X2)
      | ~ sP10(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP10(X0,X1,X2) ) ),
    inference(superposition,[],[f167,f134])).

fof(f167,plain,(
    ! [X4,X5,X3] :
      ( sP7(X4,sK20(X3,X4,X5))
      | ~ sP10(X3,X4,X5)
      | ~ l3_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f133,f122])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1))
      | ~ sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f411,plain,(
    ! [X12,X10,X13,X11,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(X10))
      | ~ r2_hidden(X9,X11)
      | ~ sP7(X10,sK19(X12,X13,a_2_2_lattice3(X10,X11)))
      | r1_lattices(X10,X9,sK19(X12,X13,a_2_2_lattice3(X10,X11)))
      | sP8(X12,X13,a_2_2_lattice3(X10,X11))
      | ~ l3_lattices(X10)
      | ~ v4_lattice3(X10)
      | ~ v10_lattices(X10)
      | v2_struct_0(X10) ) ),
    inference(resolution,[],[f407,f351])).

fof(f407,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP10(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X3,X0)
      | ~ sP7(X1,X2)
      | r1_lattices(X1,X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f406])).

fof(f406,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X3,X0)
      | ~ sP7(X1,X2)
      | ~ sP10(X0,X1,X2)
      | ~ sP10(X0,X1,X2) ) ),
    inference(superposition,[],[f262,f134])).

fof(f262,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_lattices(X5,X4,sK20(X6,X5,X7))
      | ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ r2_hidden(X4,X6)
      | ~ sP7(X5,sK20(X6,X5,X7))
      | ~ sP10(X6,X5,X7) ) ),
    inference(resolution,[],[f230,f135])).

fof(f2345,plain,
    ( ~ r4_lattice3(sK14,k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),sK15)
    | spl22_10 ),
    inference(avatar_component_clause,[],[f2343])).

fof(f2343,plain,
    ( spl22_10
  <=> r4_lattice3(sK14,k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_10])])).

fof(f2355,plain,(
    spl22_9 ),
    inference(avatar_contradiction_clause,[],[f2354])).

fof(f2354,plain,
    ( $false
    | spl22_9 ),
    inference(subsumption_resolution,[],[f2353,f90])).

fof(f2353,plain,
    ( v2_struct_0(sK14)
    | spl22_9 ),
    inference(subsumption_resolution,[],[f2347,f93])).

fof(f2347,plain,
    ( ~ l3_lattices(sK14)
    | v2_struct_0(sK14)
    | spl22_9 ),
    inference(resolution,[],[f1769,f130])).

fof(f1769,plain,
    ( ~ m1_subset_1(k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),u1_struct_0(sK14))
    | spl22_9 ),
    inference(avatar_component_clause,[],[f1767])).

fof(f1767,plain,
    ( spl22_9
  <=> m1_subset_1(k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),u1_struct_0(sK14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_9])])).

fof(f2346,plain,
    ( ~ spl22_10
    | ~ spl22_9
    | spl22_6 ),
    inference(avatar_split_clause,[],[f2341,f1699,f1767,f2343])).

fof(f2341,plain,
    ( ~ m1_subset_1(k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),u1_struct_0(sK14))
    | ~ r4_lattice3(sK14,k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),sK15)
    | spl22_6 ),
    inference(subsumption_resolution,[],[f2340,f93])).

fof(f2340,plain,
    ( ~ l3_lattices(sK14)
    | ~ m1_subset_1(k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),u1_struct_0(sK14))
    | ~ r4_lattice3(sK14,k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),sK15)
    | spl22_6 ),
    inference(subsumption_resolution,[],[f2339,f90])).

fof(f2339,plain,
    ( v2_struct_0(sK14)
    | ~ l3_lattices(sK14)
    | ~ m1_subset_1(k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),u1_struct_0(sK14))
    | ~ r4_lattice3(sK14,k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),sK15)
    | spl22_6 ),
    inference(subsumption_resolution,[],[f2338,f91])).

fof(f2338,plain,
    ( ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ l3_lattices(sK14)
    | ~ m1_subset_1(k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),u1_struct_0(sK14))
    | ~ r4_lattice3(sK14,k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),sK15)
    | spl22_6 ),
    inference(subsumption_resolution,[],[f2327,f92])).

fof(f2327,plain,
    ( ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | ~ l3_lattices(sK14)
    | ~ m1_subset_1(k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),u1_struct_0(sK14))
    | ~ r4_lattice3(sK14,k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),sK15)
    | spl22_6 ),
    inference(resolution,[],[f2320,f1733])).

fof(f1733,plain,
    ( ! [X0] :
        ( ~ sP3(X0,sK14,sK15)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ r4_lattice3(sK14,X0,sK15) )
    | spl22_6 ),
    inference(resolution,[],[f1732,f109])).

fof(f1732,plain,
    ( ! [X0] :
        ( ~ sP4(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14)) )
    | spl22_6 ),
    inference(subsumption_resolution,[],[f1731,f90])).

fof(f1731,plain,
    ( ! [X0] :
        ( ~ sP4(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | v2_struct_0(sK14) )
    | spl22_6 ),
    inference(subsumption_resolution,[],[f1730,f91])).

fof(f1730,plain,
    ( ! [X0] :
        ( ~ sP4(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14) )
    | spl22_6 ),
    inference(subsumption_resolution,[],[f1729,f92])).

fof(f1729,plain,
    ( ! [X0] :
        ( ~ sP4(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ v4_lattice3(sK14)
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14) )
    | spl22_6 ),
    inference(subsumption_resolution,[],[f1728,f93])).

fof(f1728,plain,
    ( ! [X0] :
        ( ~ sP4(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ l3_lattices(sK14)
        | ~ v4_lattice3(sK14)
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14) )
    | spl22_6 ),
    inference(duplicate_literal_removal,[],[f1727])).

fof(f1727,plain,
    ( ! [X0] :
        ( ~ sP4(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ m1_subset_1(X0,u1_struct_0(sK14))
        | ~ l3_lattices(sK14)
        | ~ v4_lattice3(sK14)
        | ~ v10_lattices(sK14)
        | v2_struct_0(sK14) )
    | spl22_6 ),
    inference(resolution,[],[f1707,f149])).

fof(f1707,plain,
    ( ! [X0] :
        ( ~ sP5(X0,sK14,sK15)
        | ~ sP4(sK15,sK14,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK14)) )
    | spl22_6 ),
    inference(superposition,[],[f1701,f106])).

fof(f1701,plain,
    ( ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | spl22_6 ),
    inference(avatar_component_clause,[],[f1699])).

fof(f2320,plain,(
    ! [X24,X25] :
      ( sP3(k16_lattice3(X24,a_2_2_lattice3(X24,X25)),X24,X25)
      | ~ v4_lattice3(X24)
      | ~ v10_lattices(X24)
      | v2_struct_0(X24)
      | ~ l3_lattices(X24) ) ),
    inference(subsumption_resolution,[],[f2319,f225])).

fof(f225,plain,(
    ! [X0,X1] :
      ( sP2(k16_lattice3(X0,X1),X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,(
    ! [X0,X1] :
      ( sP2(k16_lattice3(X0,X1),X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f104,f130])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP2(X1,X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f14,f31,f30,f29])).

fof(f29,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r3_lattices(X0,X3,X1)
          | ~ r3_lattice3(X0,X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X0,X1)
    <=> ( sP0(X1,X0,X2)
        & r3_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( k16_lattice3(X0,X2) = X1
        <=> sP1(X2,X0,X1) )
      | ~ sP2(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).

fof(f2319,plain,(
    ! [X24,X25] :
      ( ~ l3_lattices(X24)
      | ~ v4_lattice3(X24)
      | ~ v10_lattices(X24)
      | v2_struct_0(X24)
      | sP3(k16_lattice3(X24,a_2_2_lattice3(X24,X25)),X24,X25)
      | ~ sP2(k16_lattice3(X24,a_2_2_lattice3(X24,X25)),X24) ) ),
    inference(subsumption_resolution,[],[f2302,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( sP9(X0,k16_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f160])).

fof(f160,plain,(
    ! [X0,X1] :
      ( sP9(X0,k16_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f129,f130])).

fof(f2302,plain,(
    ! [X24,X25] :
      ( ~ sP9(X24,k16_lattice3(X24,a_2_2_lattice3(X24,X25)))
      | ~ l3_lattices(X24)
      | ~ v4_lattice3(X24)
      | ~ v10_lattices(X24)
      | v2_struct_0(X24)
      | sP3(k16_lattice3(X24,a_2_2_lattice3(X24,X25)),X24,X25)
      | ~ sP2(k16_lattice3(X24,a_2_2_lattice3(X24,X25)),X24) ) ),
    inference(resolution,[],[f2289,f179])).

fof(f179,plain,(
    ! [X2,X3] :
      ( r3_lattice3(X2,k16_lattice3(X2,X3),X3)
      | ~ sP2(k16_lattice3(X2,X3),X2) ) ),
    inference(resolution,[],[f145,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r3_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ~ sP0(X2,X1,X0)
        | ~ r3_lattice3(X1,X2,X0) )
      & ( ( sP0(X2,X1,X0)
          & r3_lattice3(X1,X2,X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ~ sP0(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP0(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ~ sP0(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP0(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f145,plain,(
    ! [X2,X1] :
      ( sP1(X2,X1,k16_lattice3(X1,X2))
      | ~ sP2(k16_lattice3(X1,X2),X1) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | k16_lattice3(X1,X2) != X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k16_lattice3(X1,X2) = X0
            | ~ sP1(X2,X1,X0) )
          & ( sP1(X2,X1,X0)
            | k16_lattice3(X1,X2) != X0 ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( ( k16_lattice3(X0,X2) = X1
            | ~ sP1(X2,X0,X1) )
          & ( sP1(X2,X0,X1)
            | k16_lattice3(X0,X2) != X1 ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f2289,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattice3(X0,X1,a_2_2_lattice3(X0,X2))
      | ~ sP9(X0,X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP3(X1,X0,X2) ) ),
    inference(subsumption_resolution,[],[f2288,f111])).

fof(f2288,plain,(
    ! [X2,X0,X1] :
      ( ~ sP9(X0,X1)
      | ~ r3_lattice3(X0,X1,a_2_2_lattice3(X0,X2))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP3(X1,X0,X2)
      | ~ m1_subset_1(sK17(X1,X0,X2),u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f2277])).

fof(f2277,plain,(
    ! [X2,X0,X1] :
      ( ~ sP9(X0,X1)
      | ~ r3_lattice3(X0,X1,a_2_2_lattice3(X0,X2))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP3(X1,X0,X2)
      | ~ m1_subset_1(sK17(X1,X0,X2),u1_struct_0(X0))
      | sP3(X1,X0,X2) ) ),
    inference(resolution,[],[f836,f112])).

fof(f836,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ r4_lattice3(X3,sK17(X0,X1,X2),X4)
      | ~ sP9(X1,X0)
      | ~ r3_lattice3(X1,X0,a_2_2_lattice3(X3,X4))
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | sP3(X0,X1,X2)
      | ~ m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X3)) ) ),
    inference(resolution,[],[f636,f147])).

fof(f147,plain,(
    ! [X0,X3,X1] :
      ( sP10(X0,X1,X3)
      | ~ r4_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f136])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( sP10(X0,X1,X2)
      | ~ r4_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f636,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP10(X3,X4,sK17(X1,X0,X2))
      | sP3(X1,X0,X2)
      | ~ sP9(X0,X1)
      | ~ r3_lattice3(X0,X1,a_2_2_lattice3(X4,X3))
      | ~ l3_lattices(X4)
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f268,f137])).

fof(f268,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP11(sK17(X1,X0,X4),X2,X3)
      | ~ sP9(X0,X1)
      | sP3(X1,X0,X4)
      | ~ sP10(X3,X2,sK17(X1,X0,X4))
      | ~ r3_lattice3(X0,X1,a_2_2_lattice3(X2,X3)) ) ),
    inference(resolution,[],[f266,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ sP10(X2,X1,X0)
      | ~ sP11(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f266,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK17(X0,X1,X2),X3)
      | ~ r3_lattice3(X1,X0,X3)
      | ~ sP9(X1,X0)
      | sP3(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f263,f111])).

fof(f263,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))
      | ~ r2_hidden(sK17(X0,X1,X2),X3)
      | ~ r3_lattice3(X1,X0,X3)
      | ~ sP9(X1,X0)
      | sP3(X0,X1,X2) ) ),
    inference(resolution,[],[f240,f113])).

fof(f1706,plain,
    ( ~ spl22_6
    | ~ spl22_7
    | spl22_5 ),
    inference(avatar_split_clause,[],[f1696,f1677,f1703,f1699])).

fof(f1677,plain,
    ( spl22_5
  <=> sP10(sK15,sK14,k15_lattice3(sK14,sK15)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_5])])).

fof(f1696,plain,
    ( ~ r4_lattice3(sK14,k15_lattice3(sK14,sK15),sK15)
    | ~ m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))
    | spl22_5 ),
    inference(resolution,[],[f1679,f147])).

fof(f1679,plain,
    ( ~ sP10(sK15,sK14,k15_lattice3(sK14,sK15))
    | spl22_5 ),
    inference(avatar_component_clause,[],[f1677])).

fof(f1687,plain,(
    spl22_4 ),
    inference(avatar_contradiction_clause,[],[f1686])).

fof(f1686,plain,
    ( $false
    | spl22_4 ),
    inference(subsumption_resolution,[],[f1685,f90])).

fof(f1685,plain,
    ( v2_struct_0(sK14)
    | spl22_4 ),
    inference(subsumption_resolution,[],[f1684,f91])).

fof(f1684,plain,
    ( ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | spl22_4 ),
    inference(subsumption_resolution,[],[f1683,f92])).

fof(f1683,plain,
    ( ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | spl22_4 ),
    inference(subsumption_resolution,[],[f1681,f93])).

fof(f1681,plain,
    ( ~ l3_lattices(sK14)
    | ~ v4_lattice3(sK14)
    | ~ v10_lattices(sK14)
    | v2_struct_0(sK14)
    | spl22_4 ),
    inference(resolution,[],[f1675,f137])).

fof(f1675,plain,
    ( ~ sP11(k15_lattice3(sK14,sK15),sK14,sK15)
    | spl22_4 ),
    inference(avatar_component_clause,[],[f1673])).

fof(f1673,plain,
    ( spl22_4
  <=> sP11(k15_lattice3(sK14,sK15),sK14,sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl22_4])])).

fof(f1680,plain,
    ( ~ spl22_4
    | ~ spl22_5
    | spl22_2 ),
    inference(avatar_split_clause,[],[f1670,f1659,f1677,f1673])).

fof(f1670,plain,
    ( ~ sP10(sK15,sK14,k15_lattice3(sK14,sK15))
    | ~ sP11(k15_lattice3(sK14,sK15),sK14,sK15)
    | spl22_2 ),
    inference(resolution,[],[f1661,f132])).

fof(f1661,plain,
    ( ~ r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15))
    | spl22_2 ),
    inference(avatar_component_clause,[],[f1659])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:17:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.54  % (26718)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (26717)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.55  % (26728)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.55  % (26729)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.55  % (26723)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.56  % (26720)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.56  % (26717)Refutation not found, incomplete strategy% (26717)------------------------------
% 0.22/0.56  % (26717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (26717)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (26717)Memory used [KB]: 10618
% 0.22/0.56  % (26717)Time elapsed: 0.129 s
% 0.22/0.56  % (26717)------------------------------
% 0.22/0.56  % (26717)------------------------------
% 0.22/0.57  % (26738)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.57  % (26740)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.57  % (26721)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.57  % (26732)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.57  % (26731)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.57  % (26724)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.57  % (26733)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.57  % (26725)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.57  % (26734)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.58  % (26739)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.58  % (26726)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.59  % (26722)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.59  % (26736)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.59  % (26724)Refutation not found, incomplete strategy% (26724)------------------------------
% 0.22/0.59  % (26724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (26724)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (26724)Memory used [KB]: 1663
% 0.22/0.59  % (26724)Time elapsed: 0.100 s
% 0.22/0.59  % (26724)------------------------------
% 0.22/0.59  % (26724)------------------------------
% 1.89/0.62  % (26730)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.89/0.63  % (26719)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.89/0.63  % (26742)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 2.10/0.63  % (26737)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 2.10/0.64  % (26735)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 2.10/0.64  % (26727)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 2.26/0.65  % (26741)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 2.76/0.75  % (26726)Refutation not found, incomplete strategy% (26726)------------------------------
% 2.76/0.75  % (26726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.12/0.77  % (26726)Termination reason: Refutation not found, incomplete strategy
% 3.12/0.77  
% 3.12/0.77  % (26726)Memory used [KB]: 6140
% 3.12/0.77  % (26726)Time elapsed: 0.320 s
% 3.12/0.77  % (26726)------------------------------
% 3.12/0.77  % (26726)------------------------------
% 3.12/0.84  % (26721)Refutation found. Thanks to Tanya!
% 3.12/0.84  % SZS status Theorem for theBenchmark
% 3.12/0.84  % SZS output start Proof for theBenchmark
% 3.12/0.84  fof(f2471,plain,(
% 3.12/0.84    $false),
% 3.12/0.84    inference(avatar_sat_refutation,[],[f1680,f1687,f1706,f2346,f2355,f2378,f2451,f2470])).
% 3.12/0.84  fof(f2470,plain,(
% 3.12/0.84    ~spl22_2 | ~spl22_6),
% 3.12/0.84    inference(avatar_split_clause,[],[f2469,f1699,f1659])).
% 3.12/0.84  fof(f1659,plain,(
% 3.12/0.84    spl22_2 <=> r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15))),
% 3.12/0.84    introduced(avatar_definition,[new_symbols(naming,[spl22_2])])).
% 3.12/0.84  fof(f1699,plain,(
% 3.12/0.84    spl22_6 <=> m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))),
% 3.12/0.84    introduced(avatar_definition,[new_symbols(naming,[spl22_6])])).
% 3.12/0.84  fof(f2469,plain,(
% 3.12/0.84    ~r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15)) | ~spl22_6),
% 3.12/0.84    inference(subsumption_resolution,[],[f2468,f90])).
% 3.12/0.84  fof(f90,plain,(
% 3.12/0.84    ~v2_struct_0(sK14)),
% 3.12/0.84    inference(cnf_transformation,[],[f51])).
% 3.12/0.84  fof(f51,plain,(
% 3.12/0.84    k15_lattice3(sK14,sK15) != k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)) & l3_lattices(sK14) & v4_lattice3(sK14) & v10_lattices(sK14) & ~v2_struct_0(sK14)),
% 3.12/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14,sK15])],[f12,f50,f49])).
% 3.12/0.84  fof(f49,plain,(
% 3.12/0.84    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : k15_lattice3(sK14,X1) != k16_lattice3(sK14,a_2_2_lattice3(sK14,X1)) & l3_lattices(sK14) & v4_lattice3(sK14) & v10_lattices(sK14) & ~v2_struct_0(sK14))),
% 3.12/0.84    introduced(choice_axiom,[])).
% 3.12/0.84  fof(f50,plain,(
% 3.12/0.84    ? [X1] : k15_lattice3(sK14,X1) != k16_lattice3(sK14,a_2_2_lattice3(sK14,X1)) => k15_lattice3(sK14,sK15) != k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15))),
% 3.12/0.84    introduced(choice_axiom,[])).
% 3.12/0.84  fof(f12,plain,(
% 3.12/0.84    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 3.12/0.84    inference(flattening,[],[f11])).
% 3.12/0.84  fof(f11,plain,(
% 3.12/0.84    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 3.12/0.84    inference(ennf_transformation,[],[f10])).
% 3.12/0.84  fof(f10,negated_conjecture,(
% 3.12/0.84    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 3.12/0.84    inference(negated_conjecture,[],[f9])).
% 3.12/0.84  fof(f9,conjecture,(
% 3.12/0.84    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 3.12/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_lattice3)).
% 3.12/0.84  fof(f2468,plain,(
% 3.12/0.84    ~r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15)) | v2_struct_0(sK14) | ~spl22_6),
% 3.12/0.84    inference(subsumption_resolution,[],[f2467,f92])).
% 3.12/0.84  fof(f92,plain,(
% 3.12/0.84    v4_lattice3(sK14)),
% 3.12/0.84    inference(cnf_transformation,[],[f51])).
% 3.12/0.84  fof(f2467,plain,(
% 3.12/0.84    ~r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15)) | ~v4_lattice3(sK14) | v2_struct_0(sK14) | ~spl22_6),
% 3.12/0.84    inference(subsumption_resolution,[],[f2466,f91])).
% 3.12/0.84  fof(f91,plain,(
% 3.12/0.84    v10_lattices(sK14)),
% 3.12/0.84    inference(cnf_transformation,[],[f51])).
% 3.12/0.84  fof(f2466,plain,(
% 3.12/0.84    ~r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15)) | ~v10_lattices(sK14) | ~v4_lattice3(sK14) | v2_struct_0(sK14) | ~spl22_6),
% 3.12/0.84    inference(subsumption_resolution,[],[f2465,f93])).
% 3.12/0.84  fof(f93,plain,(
% 3.12/0.84    l3_lattices(sK14)),
% 3.12/0.84    inference(cnf_transformation,[],[f51])).
% 3.12/0.84  fof(f2465,plain,(
% 3.12/0.84    ~r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15)) | ~l3_lattices(sK14) | ~v10_lattices(sK14) | ~v4_lattice3(sK14) | v2_struct_0(sK14) | ~spl22_6),
% 3.12/0.84    inference(subsumption_resolution,[],[f1885,f1700])).
% 3.12/0.84  fof(f1700,plain,(
% 3.12/0.84    m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~spl22_6),
% 3.12/0.84    inference(avatar_component_clause,[],[f1699])).
% 3.12/0.84  fof(f1885,plain,(
% 3.12/0.84    ~r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15)) | ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~l3_lattices(sK14) | ~v10_lattices(sK14) | ~v4_lattice3(sK14) | v2_struct_0(sK14)),
% 3.12/0.84    inference(trivial_inequality_removal,[],[f1884])).
% 3.12/0.84  fof(f1884,plain,(
% 3.12/0.84    k15_lattice3(sK14,sK15) != k15_lattice3(sK14,sK15) | ~r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15)) | ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~l3_lattices(sK14) | ~v10_lattices(sK14) | ~v4_lattice3(sK14) | v2_struct_0(sK14)),
% 3.12/0.84    inference(duplicate_literal_removal,[],[f1877])).
% 3.12/0.84  fof(f1877,plain,(
% 3.12/0.84    k15_lattice3(sK14,sK15) != k15_lattice3(sK14,sK15) | ~r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15)) | ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~l3_lattices(sK14) | ~v10_lattices(sK14) | ~v4_lattice3(sK14) | v2_struct_0(sK14) | ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14))),
% 3.12/0.84    inference(resolution,[],[f1649,f1079])).
% 3.12/0.84  fof(f1079,plain,(
% 3.12/0.84    ( ! [X4,X3] : (r3_lattice3(X3,k15_lattice3(X3,X4),a_2_2_lattice3(X3,X4)) | ~l3_lattices(X3) | ~v10_lattices(X3) | ~v4_lattice3(X3) | v2_struct_0(X3) | ~m1_subset_1(k15_lattice3(X3,X4),u1_struct_0(X3))) )),
% 3.12/0.84    inference(subsumption_resolution,[],[f1075,f129])).
% 3.12/0.84  fof(f129,plain,(
% 3.12/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP9(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.12/0.84    inference(cnf_transformation,[],[f42])).
% 3.12/0.84  fof(f42,plain,(
% 3.12/0.84    ! [X0] : (! [X1] : (sP9(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.12/0.84    inference(definition_folding,[],[f22,f41,f40])).
% 3.12/0.84  fof(f40,plain,(
% 3.12/0.84    ! [X1,X0,X2] : (sP8(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 3.12/0.84    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 3.12/0.84  fof(f41,plain,(
% 3.12/0.84    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP8(X1,X0,X2)) | ~sP9(X0,X1))),
% 3.12/0.84    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 3.12/0.84  fof(f22,plain,(
% 3.12/0.84    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.12/0.84    inference(flattening,[],[f21])).
% 3.12/0.84  fof(f21,plain,(
% 3.12/0.84    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.12/0.84    inference(ennf_transformation,[],[f1])).
% 3.12/0.84  fof(f1,axiom,(
% 3.12/0.84    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 3.12/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 3.12/0.84  fof(f1075,plain,(
% 3.12/0.84    ( ! [X4,X3] : (~m1_subset_1(k15_lattice3(X3,X4),u1_struct_0(X3)) | ~l3_lattices(X3) | ~v10_lattices(X3) | ~v4_lattice3(X3) | v2_struct_0(X3) | r3_lattice3(X3,k15_lattice3(X3,X4),a_2_2_lattice3(X3,X4)) | ~sP9(X3,k15_lattice3(X3,X4))) )),
% 3.12/0.84    inference(resolution,[],[f1067,f124])).
% 3.12/0.84  fof(f124,plain,(
% 3.12/0.84    ( ! [X2,X0,X1] : (~sP8(X1,X0,X2) | r3_lattice3(X0,X1,X2) | ~sP9(X0,X1)) )),
% 3.12/0.84    inference(cnf_transformation,[],[f75])).
% 3.12/0.84  fof(f75,plain,(
% 3.12/0.84    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP8(X1,X0,X2)) & (sP8(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP9(X0,X1))),
% 3.12/0.84    inference(nnf_transformation,[],[f41])).
% 3.12/0.84  fof(f1067,plain,(
% 3.12/0.84    ( ! [X0,X1] : (sP8(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | v2_struct_0(X0)) )),
% 3.12/0.84    inference(duplicate_literal_removal,[],[f1055])).
% 3.12/0.84  fof(f1055,plain,(
% 3.12/0.84    ( ! [X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | ~v4_lattice3(X0) | sP8(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP8(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1))) )),
% 3.12/0.84    inference(resolution,[],[f803,f355])).
% 3.12/0.84  fof(f355,plain,(
% 3.12/0.84    ( ! [X14,X12,X15,X13] : (r4_lattice3(X14,sK19(X12,X13,a_2_2_lattice3(X14,X15)),X15) | ~l3_lattices(X14) | ~v4_lattice3(X14) | ~v10_lattices(X14) | v2_struct_0(X14) | sP8(X12,X13,a_2_2_lattice3(X14,X15))) )),
% 3.12/0.84    inference(resolution,[],[f351,f171])).
% 3.12/0.84  fof(f171,plain,(
% 3.12/0.84    ( ! [X2,X0,X1] : (~sP10(X0,X1,X2) | r4_lattice3(X1,X2,X0)) )),
% 3.12/0.84    inference(duplicate_literal_removal,[],[f170])).
% 3.12/0.84  fof(f170,plain,(
% 3.12/0.84    ( ! [X2,X0,X1] : (r4_lattice3(X1,X2,X0) | ~sP10(X0,X1,X2) | ~sP10(X0,X1,X2)) )),
% 3.12/0.84    inference(superposition,[],[f135,f134])).
% 3.12/0.84  fof(f134,plain,(
% 3.12/0.84    ( ! [X2,X0,X1] : (sK20(X0,X1,X2) = X2 | ~sP10(X0,X1,X2)) )),
% 3.12/0.84    inference(cnf_transformation,[],[f84])).
% 3.12/0.84  fof(f84,plain,(
% 3.12/0.84    ! [X0,X1,X2] : ((sP10(X0,X1,X2) | ! [X3] : (~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK20(X0,X1,X2),X0) & sK20(X0,X1,X2) = X2 & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1))) | ~sP10(X0,X1,X2)))),
% 3.12/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f82,f83])).
% 3.12/0.84  fof(f83,plain,(
% 3.12/0.84    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK20(X0,X1,X2),X0) & sK20(X0,X1,X2) = X2 & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1))))),
% 3.12/0.84    introduced(choice_axiom,[])).
% 3.12/0.84  fof(f82,plain,(
% 3.12/0.84    ! [X0,X1,X2] : ((sP10(X0,X1,X2) | ! [X3] : (~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP10(X0,X1,X2)))),
% 3.12/0.84    inference(rectify,[],[f81])).
% 3.12/0.84  fof(f81,plain,(
% 3.12/0.84    ! [X2,X1,X0] : ((sP10(X2,X1,X0) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP10(X2,X1,X0)))),
% 3.12/0.84    inference(nnf_transformation,[],[f43])).
% 3.12/0.84  fof(f43,plain,(
% 3.12/0.84    ! [X2,X1,X0] : (sP10(X2,X1,X0) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 3.12/0.84    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).
% 3.12/0.84  fof(f135,plain,(
% 3.12/0.84    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK20(X0,X1,X2),X0) | ~sP10(X0,X1,X2)) )),
% 3.12/0.84    inference(cnf_transformation,[],[f84])).
% 3.12/0.84  fof(f351,plain,(
% 3.12/0.84    ( ! [X2,X0,X3,X1] : (sP10(X0,X1,sK19(X2,X3,a_2_2_lattice3(X1,X0))) | sP8(X2,X3,a_2_2_lattice3(X1,X0)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.12/0.84    inference(resolution,[],[f211,f137])).
% 3.12/0.84  fof(f137,plain,(
% 3.12/0.84    ( ! [X2,X0,X1] : (sP11(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 3.12/0.84    inference(cnf_transformation,[],[f45])).
% 3.12/0.85  fof(f45,plain,(
% 3.12/0.85    ! [X0,X1,X2] : (sP11(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.12/0.85    inference(definition_folding,[],[f26,f44,f43])).
% 3.12/0.85  fof(f44,plain,(
% 3.12/0.85    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> sP10(X2,X1,X0)) | ~sP11(X0,X1,X2))),
% 3.12/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).
% 3.12/0.85  fof(f26,plain,(
% 3.12/0.85    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 3.12/0.85    inference(flattening,[],[f25])).
% 3.12/0.85  fof(f25,plain,(
% 3.12/0.85    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 3.12/0.85    inference(ennf_transformation,[],[f7])).
% 3.12/0.85  fof(f7,axiom,(
% 3.12/0.85    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.12/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 3.12/0.85  fof(f211,plain,(
% 3.12/0.85    ( ! [X6,X4,X7,X5] : (~sP11(sK19(X6,X7,a_2_2_lattice3(X5,X4)),X5,X4) | sP10(X4,X5,sK19(X6,X7,a_2_2_lattice3(X5,X4))) | sP8(X6,X7,a_2_2_lattice3(X5,X4))) )),
% 3.12/0.85    inference(resolution,[],[f131,f127])).
% 3.12/0.85  fof(f127,plain,(
% 3.12/0.85    ( ! [X2,X0,X1] : (r2_hidden(sK19(X0,X1,X2),X2) | sP8(X0,X1,X2)) )),
% 3.12/0.85    inference(cnf_transformation,[],[f79])).
% 3.12/0.85  fof(f79,plain,(
% 3.12/0.85    ! [X0,X1,X2] : ((sP8(X0,X1,X2) | (~r1_lattices(X1,X0,sK19(X0,X1,X2)) & r2_hidden(sK19(X0,X1,X2),X2) & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP8(X0,X1,X2)))),
% 3.12/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f77,f78])).
% 3.12/0.85  fof(f78,plain,(
% 3.12/0.85    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK19(X0,X1,X2)) & r2_hidden(sK19(X0,X1,X2),X2) & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1))))),
% 3.12/0.85    introduced(choice_axiom,[])).
% 3.12/0.85  fof(f77,plain,(
% 3.12/0.85    ! [X0,X1,X2] : ((sP8(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP8(X0,X1,X2)))),
% 3.12/0.85    inference(rectify,[],[f76])).
% 3.12/0.85  fof(f76,plain,(
% 3.12/0.85    ! [X1,X0,X2] : ((sP8(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP8(X1,X0,X2)))),
% 3.12/0.85    inference(nnf_transformation,[],[f40])).
% 3.12/0.85  fof(f131,plain,(
% 3.12/0.85    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | sP10(X2,X1,X0) | ~sP11(X0,X1,X2)) )),
% 3.12/0.85    inference(cnf_transformation,[],[f80])).
% 3.12/0.85  fof(f80,plain,(
% 3.12/0.85    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~sP10(X2,X1,X0)) & (sP10(X2,X1,X0) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~sP11(X0,X1,X2))),
% 3.12/0.85    inference(nnf_transformation,[],[f44])).
% 3.12/0.85  fof(f803,plain,(
% 3.12/0.85    ( ! [X4,X5,X3] : (~r4_lattice3(X3,sK19(k15_lattice3(X3,X4),X3,X5),X4) | v2_struct_0(X3) | ~m1_subset_1(k15_lattice3(X3,X4),u1_struct_0(X3)) | ~l3_lattices(X3) | ~v10_lattices(X3) | ~v4_lattice3(X3) | sP8(k15_lattice3(X3,X4),X3,X5)) )),
% 3.12/0.85    inference(subsumption_resolution,[],[f798,f126])).
% 3.12/0.85  fof(f126,plain,(
% 3.12/0.85    ( ! [X2,X0,X1] : (m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)) | sP8(X0,X1,X2)) )),
% 3.12/0.85    inference(cnf_transformation,[],[f79])).
% 3.12/0.85  fof(f798,plain,(
% 3.12/0.85    ( ! [X4,X5,X3] : (~v10_lattices(X3) | v2_struct_0(X3) | ~m1_subset_1(k15_lattice3(X3,X4),u1_struct_0(X3)) | ~l3_lattices(X3) | ~r4_lattice3(X3,sK19(k15_lattice3(X3,X4),X3,X5),X4) | ~m1_subset_1(sK19(k15_lattice3(X3,X4),X3,X5),u1_struct_0(X3)) | ~v4_lattice3(X3) | sP8(k15_lattice3(X3,X4),X3,X5)) )),
% 3.12/0.85    inference(resolution,[],[f305,f128])).
% 3.12/0.85  fof(f128,plain,(
% 3.12/0.85    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK19(X0,X1,X2)) | sP8(X0,X1,X2)) )),
% 3.12/0.85    inference(cnf_transformation,[],[f79])).
% 3.12/0.85  fof(f305,plain,(
% 3.12/0.85    ( ! [X2,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X2) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~r4_lattice3(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_lattice3(X0)) )),
% 3.12/0.85    inference(resolution,[],[f295,f110])).
% 3.12/0.85  fof(f110,plain,(
% 3.12/0.85    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 3.12/0.85    inference(cnf_transformation,[],[f69])).
% 3.12/0.85  fof(f69,plain,(
% 3.12/0.85    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (~r1_lattices(X1,X0,sK17(X0,X1,X2)) & r4_lattice3(X1,sK17(X0,X1,X2),X2) & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 3.12/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f67,f68])).
% 3.12/0.85  fof(f68,plain,(
% 3.12/0.85    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK17(X0,X1,X2)) & r4_lattice3(X1,sK17(X0,X1,X2),X2) & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))))),
% 3.12/0.85    introduced(choice_axiom,[])).
% 3.12/0.85  fof(f67,plain,(
% 3.12/0.85    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 3.12/0.85    inference(rectify,[],[f66])).
% 3.12/0.85  fof(f66,plain,(
% 3.12/0.85    ! [X2,X0,X1] : ((sP3(X2,X0,X1) | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP3(X2,X0,X1)))),
% 3.12/0.85    inference(nnf_transformation,[],[f33])).
% 3.12/0.85  fof(f33,plain,(
% 3.12/0.85    ! [X2,X0,X1] : (sP3(X2,X0,X1) <=> ! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 3.12/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 3.12/0.85  fof(f295,plain,(
% 3.12/0.85    ( ! [X0,X1] : (sP3(k15_lattice3(X0,X1),X0,X1) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0)) )),
% 3.12/0.85    inference(resolution,[],[f251,f108])).
% 3.12/0.85  fof(f108,plain,(
% 3.12/0.85    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | sP3(X2,X1,X0)) )),
% 3.12/0.85    inference(cnf_transformation,[],[f65])).
% 3.12/0.85  fof(f65,plain,(
% 3.12/0.85    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ~sP3(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) & ((sP3(X2,X1,X0) & r4_lattice3(X1,X2,X0)) | ~sP4(X0,X1,X2)))),
% 3.12/0.85    inference(rectify,[],[f64])).
% 3.12/0.85  fof(f64,plain,(
% 3.12/0.85    ! [X1,X0,X2] : ((sP4(X1,X0,X2) | ~sP3(X2,X0,X1) | ~r4_lattice3(X0,X2,X1)) & ((sP3(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP4(X1,X0,X2)))),
% 3.12/0.85    inference(flattening,[],[f63])).
% 3.12/0.85  fof(f63,plain,(
% 3.12/0.85    ! [X1,X0,X2] : ((sP4(X1,X0,X2) | (~sP3(X2,X0,X1) | ~r4_lattice3(X0,X2,X1))) & ((sP3(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP4(X1,X0,X2)))),
% 3.12/0.85    inference(nnf_transformation,[],[f34])).
% 3.12/0.85  fof(f34,plain,(
% 3.12/0.85    ! [X1,X0,X2] : (sP4(X1,X0,X2) <=> (sP3(X2,X0,X1) & r4_lattice3(X0,X2,X1)))),
% 3.12/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 3.12/0.85  fof(f251,plain,(
% 3.12/0.85    ( ! [X0,X1] : (sP4(X1,X0,k15_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))) )),
% 3.12/0.85    inference(resolution,[],[f149,f146])).
% 3.12/0.85  fof(f146,plain,(
% 3.12/0.85    ( ! [X2,X1] : (~sP5(k15_lattice3(X1,X2),X1,X2) | sP4(X2,X1,k15_lattice3(X1,X2))) )),
% 3.12/0.85    inference(equality_resolution,[],[f105])).
% 3.12/0.85  fof(f105,plain,(
% 3.12/0.85    ( ! [X2,X0,X1] : (sP4(X2,X1,X0) | k15_lattice3(X1,X2) != X0 | ~sP5(X0,X1,X2)) )),
% 3.12/0.85    inference(cnf_transformation,[],[f62])).
% 3.12/0.85  fof(f62,plain,(
% 3.12/0.85    ! [X0,X1,X2] : (((k15_lattice3(X1,X2) = X0 | ~sP4(X2,X1,X0)) & (sP4(X2,X1,X0) | k15_lattice3(X1,X2) != X0)) | ~sP5(X0,X1,X2))),
% 3.12/0.85    inference(rectify,[],[f61])).
% 3.12/0.85  fof(f61,plain,(
% 3.12/0.85    ! [X2,X0,X1] : (((k15_lattice3(X0,X1) = X2 | ~sP4(X1,X0,X2)) & (sP4(X1,X0,X2) | k15_lattice3(X0,X1) != X2)) | ~sP5(X2,X0,X1))),
% 3.12/0.85    inference(nnf_transformation,[],[f35])).
% 3.12/0.85  fof(f35,plain,(
% 3.12/0.85    ! [X2,X0,X1] : ((k15_lattice3(X0,X1) = X2 <=> sP4(X1,X0,X2)) | ~sP5(X2,X0,X1))),
% 3.12/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 3.12/0.85  fof(f149,plain,(
% 3.12/0.85    ( ! [X2,X0,X1] : (sP5(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.12/0.85    inference(duplicate_literal_removal,[],[f114])).
% 3.12/0.85  fof(f114,plain,(
% 3.12/0.85    ( ! [X2,X0,X1] : (sP5(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.12/0.85    inference(cnf_transformation,[],[f36])).
% 3.12/0.85  fof(f36,plain,(
% 3.12/0.85    ! [X0] : (! [X1,X2] : (sP5(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.12/0.85    inference(definition_folding,[],[f16,f35,f34,f33])).
% 3.81/0.85  fof(f16,plain,(
% 3.81/0.85    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.81/0.85    inference(flattening,[],[f15])).
% 3.81/0.85  fof(f15,plain,(
% 3.81/0.85    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.81/0.85    inference(ennf_transformation,[],[f3])).
% 3.81/0.85  fof(f3,axiom,(
% 3.81/0.85    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 3.81/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 3.81/0.85  fof(f1649,plain,(
% 3.81/0.85    ( ! [X0] : (~r3_lattice3(sK14,X0,a_2_2_lattice3(sK14,sK15)) | k15_lattice3(sK14,sK15) != X0 | ~r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) | ~m1_subset_1(X0,u1_struct_0(sK14))) )),
% 3.81/0.85    inference(resolution,[],[f1643,f148])).
% 3.81/0.85  fof(f148,plain,(
% 3.81/0.85    ( ! [X0,X3,X1] : (sP12(X0,X1,X3) | ~r3_lattice3(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 3.81/0.85    inference(equality_resolution,[],[f143])).
% 3.81/0.85  fof(f143,plain,(
% 3.81/0.85    ( ! [X2,X0,X3,X1] : (sP12(X0,X1,X2) | ~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 3.81/0.85    inference(cnf_transformation,[],[f89])).
% 3.81/0.85  fof(f89,plain,(
% 3.81/0.85    ! [X0,X1,X2] : ((sP12(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK21(X0,X1,X2),X0) & sK21(X0,X1,X2) = X2 & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1))) | ~sP12(X0,X1,X2)))),
% 3.81/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f87,f88])).
% 3.81/0.85  fof(f88,plain,(
% 3.81/0.85    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK21(X0,X1,X2),X0) & sK21(X0,X1,X2) = X2 & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1))))),
% 3.81/0.85    introduced(choice_axiom,[])).
% 3.81/0.85  fof(f87,plain,(
% 3.81/0.85    ! [X0,X1,X2] : ((sP12(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP12(X0,X1,X2)))),
% 3.81/0.85    inference(rectify,[],[f86])).
% 3.81/0.85  fof(f86,plain,(
% 3.81/0.85    ! [X2,X1,X0] : ((sP12(X2,X1,X0) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP12(X2,X1,X0)))),
% 3.81/0.85    inference(nnf_transformation,[],[f46])).
% 3.81/0.85  fof(f46,plain,(
% 3.81/0.85    ! [X2,X1,X0] : (sP12(X2,X1,X0) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 3.81/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP12])])).
% 3.81/0.85  fof(f1643,plain,(
% 3.81/0.85    ( ! [X0] : (~sP12(a_2_2_lattice3(sK14,sK15),sK14,X0) | ~r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) | k15_lattice3(sK14,sK15) != X0) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f1642,f92])).
% 3.81/0.85  fof(f1642,plain,(
% 3.81/0.85    ( ! [X0] : (k15_lattice3(sK14,sK15) != X0 | ~v4_lattice3(sK14) | ~r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) | ~sP12(a_2_2_lattice3(sK14,sK15),sK14,X0)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f1641,f93])).
% 3.81/0.85  fof(f1641,plain,(
% 3.81/0.85    ( ! [X0] : (k15_lattice3(sK14,sK15) != X0 | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) | ~sP12(a_2_2_lattice3(sK14,sK15),sK14,X0)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f1640,f90])).
% 3.81/0.85  fof(f1640,plain,(
% 3.81/0.85    ( ! [X0] : (k15_lattice3(sK14,sK15) != X0 | v2_struct_0(sK14) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) | ~sP12(a_2_2_lattice3(sK14,sK15),sK14,X0)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f1533,f91])).
% 3.81/0.85  fof(f1533,plain,(
% 3.81/0.85    ( ! [X0] : (k15_lattice3(sK14,sK15) != X0 | ~v10_lattices(sK14) | v2_struct_0(sK14) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~r2_hidden(X0,a_2_2_lattice3(sK14,sK15)) | ~sP12(a_2_2_lattice3(sK14,sK15),sK14,X0)) )),
% 3.81/0.85    inference(superposition,[],[f94,f1526])).
% 3.81/0.85  fof(f1526,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (k16_lattice3(X1,X2) = X0 | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~r2_hidden(X0,X2) | ~sP12(X2,X1,X0)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f1525,f144])).
% 3.81/0.85  fof(f144,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (sP13(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f48])).
% 3.81/0.85  fof(f48,plain,(
% 3.81/0.85    ! [X0,X1,X2] : (sP13(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 3.81/0.85    inference(definition_folding,[],[f28,f47,f46])).
% 3.81/0.85  fof(f47,plain,(
% 3.81/0.85    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> sP12(X2,X1,X0)) | ~sP13(X0,X1,X2))),
% 3.81/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP13])])).
% 3.81/0.85  fof(f28,plain,(
% 3.81/0.85    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 3.81/0.85    inference(flattening,[],[f27])).
% 3.81/0.85  fof(f27,plain,(
% 3.81/0.85    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 3.81/0.85    inference(ennf_transformation,[],[f6])).
% 3.81/0.85  fof(f6,axiom,(
% 3.81/0.85    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 3.81/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).
% 3.81/0.85  fof(f1525,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | k16_lattice3(X1,X2) = X0 | ~r2_hidden(X0,X2) | ~sP12(X2,X1,X0) | ~sP13(X0,X1,X2)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f1522,f175])).
% 3.81/0.85  fof(f175,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~sP12(X0,X1,X2) | m1_subset_1(X2,u1_struct_0(X1))) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f174])).
% 3.81/0.85  fof(f174,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X1)) | ~sP12(X0,X1,X2) | ~sP12(X0,X1,X2)) )),
% 3.81/0.85    inference(superposition,[],[f140,f141])).
% 3.81/0.85  fof(f141,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (sK21(X0,X1,X2) = X2 | ~sP12(X0,X1,X2)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f89])).
% 3.81/0.85  fof(f140,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)) | ~sP12(X0,X1,X2)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f89])).
% 3.81/0.85  fof(f1522,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1) | k16_lattice3(X1,X2) = X0 | ~r2_hidden(X0,X2) | ~sP12(X2,X1,X0) | ~sP13(X0,X1,X2)) )),
% 3.81/0.85    inference(resolution,[],[f1489,f139])).
% 3.81/0.85  fof(f139,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP12(X2,X1,X0) | ~sP13(X0,X1,X2)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f85])).
% 3.81/0.85  fof(f85,plain,(
% 3.81/0.85    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP12(X2,X1,X0)) & (sP12(X2,X1,X0) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~sP13(X0,X1,X2))),
% 3.81/0.85    inference(nnf_transformation,[],[f47])).
% 3.81/0.85  fof(f1489,plain,(
% 3.81/0.85    ( ! [X6,X8,X7] : (~r2_hidden(X8,a_2_1_lattice3(X6,X7)) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~v4_lattice3(X6) | ~v10_lattices(X6) | v2_struct_0(X6) | ~l3_lattices(X6) | k16_lattice3(X6,X7) = X8 | ~r2_hidden(X8,X7)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f1474])).
% 3.81/0.85  fof(f1474,plain,(
% 3.81/0.85    ( ! [X6,X8,X7] : (k16_lattice3(X6,X7) = X8 | ~m1_subset_1(X8,u1_struct_0(X6)) | ~v4_lattice3(X6) | ~v10_lattices(X6) | v2_struct_0(X6) | ~l3_lattices(X6) | ~r2_hidden(X8,a_2_1_lattice3(X6,X7)) | ~r2_hidden(X8,X7) | ~l3_lattices(X6) | v2_struct_0(X6) | ~m1_subset_1(X8,u1_struct_0(X6))) )),
% 3.81/0.85    inference(resolution,[],[f812,f451])).
% 3.81/0.85  fof(f451,plain,(
% 3.81/0.85    ( ! [X6,X4,X5] : (r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | v2_struct_0(X5) | ~m1_subset_1(X4,u1_struct_0(X5))) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f450,f122])).
% 3.81/0.85  fof(f122,plain,(
% 3.81/0.85    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP7(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f39])).
% 3.81/0.85  fof(f39,plain,(
% 3.81/0.85    ! [X0] : (! [X1] : (sP7(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.81/0.85    inference(definition_folding,[],[f20,f38,f37])).
% 3.81/0.85  fof(f37,plain,(
% 3.81/0.85    ! [X1,X0,X2] : (sP6(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 3.81/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 3.81/0.85  fof(f38,plain,(
% 3.81/0.85    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP6(X1,X0,X2)) | ~sP7(X0,X1))),
% 3.81/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 3.81/0.85  fof(f20,plain,(
% 3.81/0.85    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.81/0.85    inference(flattening,[],[f19])).
% 3.81/0.85  fof(f19,plain,(
% 3.81/0.85    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.81/0.85    inference(ennf_transformation,[],[f2])).
% 3.81/0.85  fof(f2,axiom,(
% 3.81/0.85    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 3.81/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 3.81/0.85  fof(f450,plain,(
% 3.81/0.85    ( ! [X6,X4,X5] : (~m1_subset_1(X4,u1_struct_0(X5)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | v2_struct_0(X5) | r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6)) | ~sP7(X5,X4)) )),
% 3.81/0.85    inference(resolution,[],[f448,f117])).
% 3.81/0.85  fof(f117,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~sP6(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP7(X0,X1)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f70])).
% 3.81/0.85  fof(f70,plain,(
% 3.81/0.85    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP6(X1,X0,X2)) & (sP6(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP7(X0,X1))),
% 3.81/0.85    inference(nnf_transformation,[],[f38])).
% 3.81/0.85  fof(f448,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (sP6(X0,X2,a_2_1_lattice3(X2,X1)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f447,f163])).
% 3.81/0.85  fof(f163,plain,(
% 3.81/0.85    ( ! [X10,X8,X9] : (sP9(X8,sK18(X9,X8,X10)) | ~l3_lattices(X8) | v2_struct_0(X8) | sP6(X9,X8,X10)) )),
% 3.81/0.85    inference(resolution,[],[f129,f119])).
% 3.81/0.85  fof(f119,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)) | sP6(X0,X1,X2)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f74])).
% 3.81/0.85  fof(f74,plain,(
% 3.81/0.85    ! [X0,X1,X2] : ((sP6(X0,X1,X2) | (~r1_lattices(X1,sK18(X0,X1,X2),X0) & r2_hidden(sK18(X0,X1,X2),X2) & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP6(X0,X1,X2)))),
% 3.81/0.85    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f72,f73])).
% 3.81/0.85  fof(f73,plain,(
% 3.81/0.85    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK18(X0,X1,X2),X0) & r2_hidden(sK18(X0,X1,X2),X2) & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1))))),
% 3.81/0.85    introduced(choice_axiom,[])).
% 3.81/0.85  fof(f72,plain,(
% 3.81/0.85    ! [X0,X1,X2] : ((sP6(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP6(X0,X1,X2)))),
% 3.81/0.85    inference(rectify,[],[f71])).
% 3.81/0.85  fof(f71,plain,(
% 3.81/0.85    ! [X1,X0,X2] : ((sP6(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP6(X1,X0,X2)))),
% 3.81/0.85    inference(nnf_transformation,[],[f37])).
% 3.81/0.85  fof(f447,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~sP9(X2,sK18(X0,X2,a_2_1_lattice3(X2,X1))) | sP6(X0,X2,a_2_1_lattice3(X2,X1)) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f446])).
% 3.81/0.85  fof(f446,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~sP9(X2,sK18(X0,X2,a_2_1_lattice3(X2,X1))) | sP6(X0,X2,a_2_1_lattice3(X2,X1)) | ~l3_lattices(X2) | v2_struct_0(X2) | sP6(X0,X2,a_2_1_lattice3(X2,X1))) )),
% 3.81/0.85    inference(resolution,[],[f265,f364])).
% 3.81/0.85  fof(f364,plain,(
% 3.81/0.85    ( ! [X14,X12,X15,X13] : (r3_lattice3(X14,sK18(X12,X13,a_2_1_lattice3(X14,X15)),X15) | ~l3_lattices(X14) | v2_struct_0(X14) | sP6(X12,X13,a_2_1_lattice3(X14,X15))) )),
% 3.81/0.85    inference(resolution,[],[f360,f177])).
% 3.81/0.85  fof(f177,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~sP12(X0,X1,X2) | r3_lattice3(X1,X2,X0)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f176])).
% 3.81/0.85  fof(f176,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (r3_lattice3(X1,X2,X0) | ~sP12(X0,X1,X2) | ~sP12(X0,X1,X2)) )),
% 3.81/0.85    inference(superposition,[],[f142,f141])).
% 3.81/0.85  fof(f142,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK21(X0,X1,X2),X0) | ~sP12(X0,X1,X2)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f89])).
% 3.81/0.85  fof(f360,plain,(
% 3.81/0.85    ( ! [X2,X0,X3,X1] : (sP12(X0,X1,sK18(X2,X3,a_2_1_lattice3(X1,X0))) | sP6(X2,X3,a_2_1_lattice3(X1,X0)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.81/0.85    inference(resolution,[],[f214,f144])).
% 3.81/0.85  fof(f214,plain,(
% 3.81/0.85    ( ! [X2,X0,X3,X1] : (~sP13(sK18(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0) | sP12(X0,X1,sK18(X2,X3,a_2_1_lattice3(X1,X0))) | sP6(X2,X3,a_2_1_lattice3(X1,X0))) )),
% 3.81/0.85    inference(resolution,[],[f138,f120])).
% 3.81/0.85  fof(f120,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (r2_hidden(sK18(X0,X1,X2),X2) | sP6(X0,X1,X2)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f74])).
% 3.81/0.85  fof(f138,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | sP12(X2,X1,X0) | ~sP13(X0,X1,X2)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f85])).
% 3.81/0.85  fof(f265,plain,(
% 3.81/0.85    ( ! [X10,X8,X11,X9] : (~r3_lattice3(X9,sK18(X8,X9,X11),X10) | ~r2_hidden(X8,X10) | ~m1_subset_1(X8,u1_struct_0(X9)) | ~sP9(X9,sK18(X8,X9,X11)) | sP6(X8,X9,X11)) )),
% 3.81/0.85    inference(resolution,[],[f240,f121])).
% 3.81/0.85  fof(f121,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK18(X0,X1,X2),X0) | sP6(X0,X1,X2)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f74])).
% 3.81/0.85  fof(f240,plain,(
% 3.81/0.85    ( ! [X2,X0,X3,X1] : (r1_lattices(X2,X3,X0) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~r3_lattice3(X2,X3,X1) | ~sP9(X2,X3)) )),
% 3.81/0.85    inference(resolution,[],[f125,f123])).
% 3.81/0.85  fof(f123,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (sP8(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | ~sP9(X0,X1)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f75])).
% 3.81/0.85  fof(f125,plain,(
% 3.81/0.85    ( ! [X4,X2,X0,X1] : (~sP8(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f79])).
% 3.81/0.85  fof(f812,plain,(
% 3.81/0.85    ( ! [X12,X10,X11] : (~r4_lattice3(X10,X12,a_2_1_lattice3(X10,X11)) | k16_lattice3(X10,X11) = X12 | ~m1_subset_1(X12,u1_struct_0(X10)) | ~v4_lattice3(X10) | ~v10_lattices(X10) | v2_struct_0(X10) | ~l3_lattices(X10) | ~r2_hidden(X12,a_2_1_lattice3(X10,X11))) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f811])).
% 3.81/0.85  fof(f811,plain,(
% 3.81/0.85    ( ! [X12,X10,X11] : (~l3_lattices(X10) | k16_lattice3(X10,X11) = X12 | ~m1_subset_1(X12,u1_struct_0(X10)) | ~v4_lattice3(X10) | ~v10_lattices(X10) | v2_struct_0(X10) | ~r4_lattice3(X10,X12,a_2_1_lattice3(X10,X11)) | ~m1_subset_1(X12,u1_struct_0(X10)) | ~r2_hidden(X12,a_2_1_lattice3(X10,X11)) | ~l3_lattices(X10) | v2_struct_0(X10)) )),
% 3.81/0.85    inference(resolution,[],[f338,f395])).
% 3.81/0.85  fof(f395,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (sP3(X0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f394])).
% 3.81/0.85  fof(f394,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | sP3(X0,X2,X1) | ~l3_lattices(X2) | v2_struct_0(X2) | sP3(X0,X2,X1)) )),
% 3.81/0.85    inference(resolution,[],[f392,f154])).
% 3.81/0.85  fof(f154,plain,(
% 3.81/0.85    ( ! [X6,X7,X5] : (sP7(X5,sK17(X6,X5,X7)) | ~l3_lattices(X5) | v2_struct_0(X5) | sP3(X6,X5,X7)) )),
% 3.81/0.85    inference(resolution,[],[f122,f111])).
% 3.81/0.85  fof(f111,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) | sP3(X0,X1,X2)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f69])).
% 3.81/0.85  fof(f392,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~sP7(X1,sK17(X0,X1,X2)) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | sP3(X0,X1,X2)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f390])).
% 3.81/0.85  fof(f390,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~sP7(X1,sK17(X0,X1,X2)) | sP3(X0,X1,X2) | sP3(X0,X1,X2)) )),
% 3.81/0.85    inference(resolution,[],[f261,f113])).
% 3.81/0.85  fof(f113,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK17(X0,X1,X2)) | sP3(X0,X1,X2)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f69])).
% 3.81/0.85  fof(f261,plain,(
% 3.81/0.85    ( ! [X2,X0,X3,X1] : (r1_lattices(X1,X0,sK17(X2,X1,X3)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X3) | ~sP7(X1,sK17(X2,X1,X3)) | sP3(X2,X1,X3)) )),
% 3.81/0.85    inference(resolution,[],[f230,f112])).
% 3.81/0.85  fof(f112,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK17(X0,X1,X2),X2) | sP3(X0,X1,X2)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f69])).
% 3.81/0.85  fof(f230,plain,(
% 3.81/0.85    ( ! [X2,X0,X3,X1] : (~r4_lattice3(X2,X3,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | r1_lattices(X2,X0,X3) | ~r2_hidden(X0,X1) | ~sP7(X2,X3)) )),
% 3.81/0.85    inference(resolution,[],[f118,f116])).
% 3.81/0.85  fof(f116,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (sP6(X1,X0,X2) | ~r4_lattice3(X0,X1,X2) | ~sP7(X0,X1)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f70])).
% 3.81/0.85  fof(f118,plain,(
% 3.81/0.85    ( ! [X4,X2,X0,X1] : (~sP6(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X4,X0)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f74])).
% 3.81/0.85  fof(f338,plain,(
% 3.81/0.85    ( ! [X6,X7,X5] : (~sP3(X7,X5,a_2_1_lattice3(X5,X6)) | ~l3_lattices(X5) | k16_lattice3(X5,X6) = X7 | ~m1_subset_1(X7,u1_struct_0(X5)) | ~v4_lattice3(X5) | ~v10_lattices(X5) | v2_struct_0(X5) | ~r4_lattice3(X5,X7,a_2_1_lattice3(X5,X6))) )),
% 3.81/0.85    inference(resolution,[],[f321,f109])).
% 3.81/0.85  fof(f109,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (sP4(X0,X1,X2) | ~sP3(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f65])).
% 3.81/0.85  fof(f321,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~sP4(a_2_1_lattice3(X0,X1),X0,X2) | v2_struct_0(X0) | ~l3_lattices(X0) | k16_lattice3(X0,X1) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~v10_lattices(X0)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f320])).
% 3.81/0.85  fof(f320,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~l3_lattices(X0) | v2_struct_0(X0) | ~sP4(a_2_1_lattice3(X0,X1),X0,X2) | k16_lattice3(X0,X1) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.81/0.85    inference(resolution,[],[f207,f149])).
% 3.81/0.85  fof(f207,plain,(
% 3.81/0.85    ( ! [X4,X2,X3] : (~sP5(X4,X2,a_2_1_lattice3(X2,X3)) | ~l3_lattices(X2) | v2_struct_0(X2) | ~sP4(a_2_1_lattice3(X2,X3),X2,X4) | k16_lattice3(X2,X3) = X4) )),
% 3.81/0.85    inference(superposition,[],[f115,f106])).
% 3.81/0.85  fof(f106,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (k15_lattice3(X1,X2) = X0 | ~sP4(X2,X1,X0) | ~sP5(X0,X1,X2)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f62])).
% 3.81/0.85  fof(f115,plain,(
% 3.81/0.85    ( ! [X0,X1] : (k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f18])).
% 3.81/0.85  fof(f18,plain,(
% 3.81/0.85    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.81/0.85    inference(flattening,[],[f17])).
% 3.81/0.85  fof(f17,plain,(
% 3.81/0.85    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.81/0.85    inference(ennf_transformation,[],[f4])).
% 3.81/0.85  fof(f4,axiom,(
% 3.81/0.85    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)))),
% 3.81/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattice3)).
% 3.81/0.85  fof(f94,plain,(
% 3.81/0.85    k15_lattice3(sK14,sK15) != k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15))),
% 3.81/0.85    inference(cnf_transformation,[],[f51])).
% 3.81/0.85  fof(f2451,plain,(
% 3.81/0.85    ~spl22_6 | spl22_7),
% 3.81/0.85    inference(avatar_contradiction_clause,[],[f2450])).
% 3.81/0.85  fof(f2450,plain,(
% 3.81/0.85    $false | (~spl22_6 | spl22_7)),
% 3.81/0.85    inference(subsumption_resolution,[],[f2449,f93])).
% 3.81/0.85  fof(f2449,plain,(
% 3.81/0.85    ~l3_lattices(sK14) | (~spl22_6 | spl22_7)),
% 3.81/0.85    inference(subsumption_resolution,[],[f2448,f1700])).
% 3.81/0.85  fof(f2448,plain,(
% 3.81/0.85    ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~l3_lattices(sK14) | spl22_7),
% 3.81/0.85    inference(subsumption_resolution,[],[f2447,f90])).
% 3.81/0.85  fof(f2447,plain,(
% 3.81/0.85    v2_struct_0(sK14) | ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~l3_lattices(sK14) | spl22_7),
% 3.81/0.85    inference(subsumption_resolution,[],[f2446,f91])).
% 3.81/0.85  fof(f2446,plain,(
% 3.81/0.85    ~v10_lattices(sK14) | v2_struct_0(sK14) | ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~l3_lattices(sK14) | spl22_7),
% 3.81/0.85    inference(subsumption_resolution,[],[f2444,f92])).
% 3.81/0.85  fof(f2444,plain,(
% 3.81/0.85    ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | ~l3_lattices(sK14) | spl22_7),
% 3.81/0.85    inference(resolution,[],[f1705,f296])).
% 3.81/0.85  fof(f296,plain,(
% 3.81/0.85    ( ! [X2,X3] : (r4_lattice3(X2,k15_lattice3(X2,X3),X3) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | ~m1_subset_1(k15_lattice3(X2,X3),u1_struct_0(X2)) | ~l3_lattices(X2)) )),
% 3.81/0.85    inference(resolution,[],[f251,f107])).
% 3.81/0.85  fof(f107,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~sP4(X0,X1,X2) | r4_lattice3(X1,X2,X0)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f65])).
% 3.81/0.85  fof(f1705,plain,(
% 3.81/0.85    ~r4_lattice3(sK14,k15_lattice3(sK14,sK15),sK15) | spl22_7),
% 3.81/0.85    inference(avatar_component_clause,[],[f1703])).
% 3.81/0.85  fof(f1703,plain,(
% 3.81/0.85    spl22_7 <=> r4_lattice3(sK14,k15_lattice3(sK14,sK15),sK15)),
% 3.81/0.85    introduced(avatar_definition,[new_symbols(naming,[spl22_7])])).
% 3.81/0.85  fof(f2378,plain,(
% 3.81/0.85    spl22_10),
% 3.81/0.85    inference(avatar_contradiction_clause,[],[f2377])).
% 3.81/0.85  fof(f2377,plain,(
% 3.81/0.85    $false | spl22_10),
% 3.81/0.85    inference(subsumption_resolution,[],[f2376,f92])).
% 3.81/0.85  fof(f2376,plain,(
% 3.81/0.85    ~v4_lattice3(sK14) | spl22_10),
% 3.81/0.85    inference(subsumption_resolution,[],[f2375,f93])).
% 3.81/0.85  fof(f2375,plain,(
% 3.81/0.85    ~l3_lattices(sK14) | ~v4_lattice3(sK14) | spl22_10),
% 3.81/0.85    inference(subsumption_resolution,[],[f2374,f90])).
% 3.81/0.85  fof(f2374,plain,(
% 3.81/0.85    v2_struct_0(sK14) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | spl22_10),
% 3.81/0.85    inference(subsumption_resolution,[],[f2369,f91])).
% 3.81/0.85  fof(f2369,plain,(
% 3.81/0.85    ~v10_lattices(sK14) | v2_struct_0(sK14) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | spl22_10),
% 3.81/0.85    inference(resolution,[],[f2345,f1237])).
% 3.81/0.85  fof(f1237,plain,(
% 3.81/0.85    ( ! [X4,X3] : (r4_lattice3(X3,k16_lattice3(X3,a_2_2_lattice3(X3,X4)),X4) | ~v10_lattices(X3) | v2_struct_0(X3) | ~l3_lattices(X3) | ~v4_lattice3(X3)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f1231,f156])).
% 3.81/0.85  fof(f156,plain,(
% 3.81/0.85    ( ! [X0,X1] : (sP7(X0,k16_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f152])).
% 3.81/0.85  fof(f152,plain,(
% 3.81/0.85    ( ! [X0,X1] : (sP7(X0,k16_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.81/0.85    inference(resolution,[],[f122,f130])).
% 3.81/0.85  fof(f130,plain,(
% 3.81/0.85    ( ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f24])).
% 3.81/0.85  fof(f24,plain,(
% 3.81/0.85    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 3.81/0.85    inference(flattening,[],[f23])).
% 3.81/0.85  fof(f23,plain,(
% 3.81/0.85    ! [X0,X1] : (m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 3.81/0.85    inference(ennf_transformation,[],[f5])).
% 3.81/0.85  fof(f5,axiom,(
% 3.81/0.85    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)))),
% 3.81/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k16_lattice3)).
% 3.81/0.85  fof(f1231,plain,(
% 3.81/0.85    ( ! [X4,X3] : (~v4_lattice3(X3) | ~v10_lattices(X3) | v2_struct_0(X3) | ~l3_lattices(X3) | r4_lattice3(X3,k16_lattice3(X3,a_2_2_lattice3(X3,X4)),X4) | ~sP7(X3,k16_lattice3(X3,a_2_2_lattice3(X3,X4)))) )),
% 3.81/0.85    inference(resolution,[],[f1229,f117])).
% 3.81/0.85  fof(f1229,plain,(
% 3.81/0.85    ( ! [X0,X1] : (sP6(k16_lattice3(X0,a_2_2_lattice3(X0,X1)),X0,X1) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f1221])).
% 3.81/0.85  fof(f1221,plain,(
% 3.81/0.85    ( ! [X0,X1] : (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP6(k16_lattice3(X0,a_2_2_lattice3(X0,X1)),X0,X1) | sP6(k16_lattice3(X0,a_2_2_lattice3(X0,X1)),X0,X1)) )),
% 3.81/0.85    inference(resolution,[],[f1211,f120])).
% 3.81/0.85  fof(f1211,plain,(
% 3.81/0.85    ( ! [X21,X19,X20] : (~r2_hidden(sK18(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21),X20) | ~l3_lattices(X19) | ~v4_lattice3(X19) | ~v10_lattices(X19) | v2_struct_0(X19) | sP6(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f1201,f119])).
% 3.81/0.85  fof(f1201,plain,(
% 3.81/0.85    ( ! [X21,X19,X20] : (~r2_hidden(sK18(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21),X20) | ~l3_lattices(X19) | ~v4_lattice3(X19) | ~v10_lattices(X19) | v2_struct_0(X19) | ~m1_subset_1(sK18(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21),u1_struct_0(X19)) | sP6(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f1200])).
% 3.81/0.85  fof(f1200,plain,(
% 3.81/0.85    ( ! [X21,X19,X20] : (~r2_hidden(sK18(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21),X20) | ~l3_lattices(X19) | ~v4_lattice3(X19) | ~v10_lattices(X19) | v2_struct_0(X19) | ~m1_subset_1(sK18(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21),u1_struct_0(X19)) | v2_struct_0(X19) | ~v4_lattice3(X19) | sP6(k16_lattice3(X19,a_2_2_lattice3(X19,X20)),X19,X21) | ~v10_lattices(X19) | ~l3_lattices(X19)) )),
% 3.81/0.85    inference(resolution,[],[f1194,f606])).
% 3.81/0.85  fof(f606,plain,(
% 3.81/0.85    ( ! [X4,X2,X3] : (~r3_lattice3(X2,sK18(k16_lattice3(X2,X3),X2,X4),X3) | v2_struct_0(X2) | ~v4_lattice3(X2) | sP6(k16_lattice3(X2,X3),X2,X4) | ~v10_lattices(X2) | ~l3_lattices(X2)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f601,f119])).
% 3.81/0.85  fof(f601,plain,(
% 3.81/0.85    ( ! [X4,X2,X3] : (~l3_lattices(X2) | v2_struct_0(X2) | ~v4_lattice3(X2) | sP6(k16_lattice3(X2,X3),X2,X4) | ~v10_lattices(X2) | ~r3_lattice3(X2,sK18(k16_lattice3(X2,X3),X2,X4),X3) | ~m1_subset_1(sK18(k16_lattice3(X2,X3),X2,X4),u1_struct_0(X2))) )),
% 3.81/0.85    inference(resolution,[],[f592,f148])).
% 3.81/0.85  fof(f592,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~sP12(X1,X0,sK18(k16_lattice3(X0,X1),X0,X2)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~v4_lattice3(X0) | sP6(k16_lattice3(X0,X1),X0,X2) | ~v10_lattices(X0)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f586,f144])).
% 3.81/0.85  fof(f586,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~v4_lattice3(X0) | sP6(k16_lattice3(X0,X1),X0,X2) | ~sP12(X1,X0,sK18(k16_lattice3(X0,X1),X0,X2)) | ~sP13(sK18(k16_lattice3(X0,X1),X0,X2),X0,X1)) )),
% 3.81/0.85    inference(resolution,[],[f424,f139])).
% 3.81/0.85  fof(f424,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~r2_hidden(sK18(k16_lattice3(X0,X1),X0,X2),a_2_1_lattice3(X0,X1)) | ~v10_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | ~v4_lattice3(X0) | sP6(k16_lattice3(X0,X1),X0,X2)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f422,f119])).
% 3.81/0.85  fof(f422,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(sK18(k16_lattice3(X0,X1),X0,X2),u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(sK18(k16_lattice3(X0,X1),X0,X2),a_2_1_lattice3(X0,X1)) | sP6(k16_lattice3(X0,X1),X0,X2)) )),
% 3.81/0.85    inference(resolution,[],[f304,f121])).
% 3.81/0.85  fof(f304,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,k16_lattice3(X0,X2)) | ~v4_lattice3(X0) | ~v10_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X1,a_2_1_lattice3(X0,X2))) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f302,f156])).
% 3.81/0.85  fof(f302,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | ~l3_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattices(X0,X1,k16_lattice3(X0,X2)) | ~r2_hidden(X1,a_2_1_lattice3(X0,X2)) | ~sP7(X0,k16_lattice3(X0,X2))) )),
% 3.81/0.85    inference(resolution,[],[f293,f230])).
% 3.81/0.85  fof(f293,plain,(
% 3.81/0.85    ( ! [X2,X3] : (r4_lattice3(X2,k16_lattice3(X2,X3),a_2_1_lattice3(X2,X3)) | v2_struct_0(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | ~l3_lattices(X2)) )),
% 3.81/0.85    inference(resolution,[],[f291,f107])).
% 3.81/0.85  fof(f291,plain,(
% 3.81/0.85    ( ! [X0,X1] : (sP4(a_2_1_lattice3(X0,X1),X0,k16_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f290,f130])).
% 3.81/0.85  fof(f290,plain,(
% 3.81/0.85    ( ! [X0,X1] : (sP4(a_2_1_lattice3(X0,X1),X0,k16_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~v4_lattice3(X0) | ~v10_lattices(X0)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f288])).
% 3.81/0.85  fof(f288,plain,(
% 3.81/0.85    ( ! [X0,X1] : (sP4(a_2_1_lattice3(X0,X1),X0,k16_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k16_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.81/0.85    inference(resolution,[],[f209,f149])).
% 3.81/0.85  fof(f209,plain,(
% 3.81/0.85    ( ! [X4,X3] : (~sP5(k16_lattice3(X3,X4),X3,a_2_1_lattice3(X3,X4)) | sP4(a_2_1_lattice3(X3,X4),X3,k16_lattice3(X3,X4)) | ~l3_lattices(X3) | v2_struct_0(X3)) )),
% 3.81/0.85    inference(superposition,[],[f146,f115])).
% 3.81/0.85  fof(f1194,plain,(
% 3.81/0.85    ( ! [X6,X4,X5] : (r3_lattice3(X5,X4,a_2_2_lattice3(X5,X6)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | ~v4_lattice3(X5) | ~v10_lattices(X5) | v2_struct_0(X5) | ~m1_subset_1(X4,u1_struct_0(X5))) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f1193,f129])).
% 3.81/0.85  fof(f1193,plain,(
% 3.81/0.85    ( ! [X6,X4,X5] : (~m1_subset_1(X4,u1_struct_0(X5)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | ~v4_lattice3(X5) | ~v10_lattices(X5) | v2_struct_0(X5) | r3_lattice3(X5,X4,a_2_2_lattice3(X5,X6)) | ~sP9(X5,X4)) )),
% 3.81/0.85    inference(resolution,[],[f1190,f124])).
% 3.81/0.85  fof(f1190,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (sP8(X0,X2,a_2_2_lattice3(X2,X1)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f1188])).
% 3.81/0.85  fof(f1188,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | sP8(X0,X2,a_2_2_lattice3(X2,X1)) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | sP8(X0,X2,a_2_2_lattice3(X2,X1))) )),
% 3.81/0.85    inference(resolution,[],[f413,f128])).
% 3.81/0.85  fof(f413,plain,(
% 3.81/0.85    ( ! [X12,X10,X13,X11,X9] : (r1_lattices(X10,X9,sK19(X12,X13,a_2_2_lattice3(X10,X11))) | ~r2_hidden(X9,X11) | ~m1_subset_1(X9,u1_struct_0(X10)) | sP8(X12,X13,a_2_2_lattice3(X10,X11)) | ~l3_lattices(X10) | ~v4_lattice3(X10) | ~v10_lattices(X10) | v2_struct_0(X10)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f411,f358])).
% 3.81/0.85  fof(f358,plain,(
% 3.81/0.85    ( ! [X6,X4,X7,X5] : (sP7(X6,sK19(X4,X5,a_2_2_lattice3(X6,X7))) | ~l3_lattices(X6) | ~v4_lattice3(X6) | ~v10_lattices(X6) | v2_struct_0(X6) | sP8(X4,X5,a_2_2_lattice3(X6,X7))) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f353])).
% 3.81/0.85  fof(f353,plain,(
% 3.81/0.85    ( ! [X6,X4,X7,X5] : (sP8(X4,X5,a_2_2_lattice3(X6,X7)) | ~l3_lattices(X6) | ~v4_lattice3(X6) | ~v10_lattices(X6) | v2_struct_0(X6) | sP7(X6,sK19(X4,X5,a_2_2_lattice3(X6,X7))) | ~l3_lattices(X6) | v2_struct_0(X6)) )),
% 3.81/0.85    inference(resolution,[],[f351,f232])).
% 3.81/0.85  fof(f232,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~sP10(X0,X1,X2) | sP7(X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f231])).
% 3.81/0.85  fof(f231,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (sP7(X1,X2) | ~sP10(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1) | ~sP10(X0,X1,X2)) )),
% 3.81/0.85    inference(superposition,[],[f167,f134])).
% 3.81/0.85  fof(f167,plain,(
% 3.81/0.85    ( ! [X4,X5,X3] : (sP7(X4,sK20(X3,X4,X5)) | ~sP10(X3,X4,X5) | ~l3_lattices(X4) | v2_struct_0(X4)) )),
% 3.81/0.85    inference(resolution,[],[f133,f122])).
% 3.81/0.85  fof(f133,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)) | ~sP10(X0,X1,X2)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f84])).
% 3.81/0.85  fof(f411,plain,(
% 3.81/0.85    ( ! [X12,X10,X13,X11,X9] : (~m1_subset_1(X9,u1_struct_0(X10)) | ~r2_hidden(X9,X11) | ~sP7(X10,sK19(X12,X13,a_2_2_lattice3(X10,X11))) | r1_lattices(X10,X9,sK19(X12,X13,a_2_2_lattice3(X10,X11))) | sP8(X12,X13,a_2_2_lattice3(X10,X11)) | ~l3_lattices(X10) | ~v4_lattice3(X10) | ~v10_lattices(X10) | v2_struct_0(X10)) )),
% 3.81/0.85    inference(resolution,[],[f407,f351])).
% 3.81/0.85  fof(f407,plain,(
% 3.81/0.85    ( ! [X2,X0,X3,X1] : (~sP10(X0,X1,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~r2_hidden(X3,X0) | ~sP7(X1,X2) | r1_lattices(X1,X3,X2)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f406])).
% 3.81/0.85  fof(f406,plain,(
% 3.81/0.85    ( ! [X2,X0,X3,X1] : (r1_lattices(X1,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~r2_hidden(X3,X0) | ~sP7(X1,X2) | ~sP10(X0,X1,X2) | ~sP10(X0,X1,X2)) )),
% 3.81/0.85    inference(superposition,[],[f262,f134])).
% 3.81/0.85  fof(f262,plain,(
% 3.81/0.85    ( ! [X6,X4,X7,X5] : (r1_lattices(X5,X4,sK20(X6,X5,X7)) | ~m1_subset_1(X4,u1_struct_0(X5)) | ~r2_hidden(X4,X6) | ~sP7(X5,sK20(X6,X5,X7)) | ~sP10(X6,X5,X7)) )),
% 3.81/0.85    inference(resolution,[],[f230,f135])).
% 3.81/0.85  fof(f2345,plain,(
% 3.81/0.85    ~r4_lattice3(sK14,k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),sK15) | spl22_10),
% 3.81/0.85    inference(avatar_component_clause,[],[f2343])).
% 3.81/0.85  fof(f2343,plain,(
% 3.81/0.85    spl22_10 <=> r4_lattice3(sK14,k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),sK15)),
% 3.81/0.85    introduced(avatar_definition,[new_symbols(naming,[spl22_10])])).
% 3.81/0.85  fof(f2355,plain,(
% 3.81/0.85    spl22_9),
% 3.81/0.85    inference(avatar_contradiction_clause,[],[f2354])).
% 3.81/0.85  fof(f2354,plain,(
% 3.81/0.85    $false | spl22_9),
% 3.81/0.85    inference(subsumption_resolution,[],[f2353,f90])).
% 3.81/0.85  fof(f2353,plain,(
% 3.81/0.85    v2_struct_0(sK14) | spl22_9),
% 3.81/0.85    inference(subsumption_resolution,[],[f2347,f93])).
% 3.81/0.85  fof(f2347,plain,(
% 3.81/0.85    ~l3_lattices(sK14) | v2_struct_0(sK14) | spl22_9),
% 3.81/0.85    inference(resolution,[],[f1769,f130])).
% 3.81/0.85  fof(f1769,plain,(
% 3.81/0.85    ~m1_subset_1(k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),u1_struct_0(sK14)) | spl22_9),
% 3.81/0.85    inference(avatar_component_clause,[],[f1767])).
% 3.81/0.85  fof(f1767,plain,(
% 3.81/0.85    spl22_9 <=> m1_subset_1(k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),u1_struct_0(sK14))),
% 3.81/0.85    introduced(avatar_definition,[new_symbols(naming,[spl22_9])])).
% 3.81/0.85  fof(f2346,plain,(
% 3.81/0.85    ~spl22_10 | ~spl22_9 | spl22_6),
% 3.81/0.85    inference(avatar_split_clause,[],[f2341,f1699,f1767,f2343])).
% 3.81/0.85  fof(f2341,plain,(
% 3.81/0.85    ~m1_subset_1(k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),u1_struct_0(sK14)) | ~r4_lattice3(sK14,k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),sK15) | spl22_6),
% 3.81/0.85    inference(subsumption_resolution,[],[f2340,f93])).
% 3.81/0.85  fof(f2340,plain,(
% 3.81/0.85    ~l3_lattices(sK14) | ~m1_subset_1(k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),u1_struct_0(sK14)) | ~r4_lattice3(sK14,k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),sK15) | spl22_6),
% 3.81/0.85    inference(subsumption_resolution,[],[f2339,f90])).
% 3.81/0.85  fof(f2339,plain,(
% 3.81/0.85    v2_struct_0(sK14) | ~l3_lattices(sK14) | ~m1_subset_1(k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),u1_struct_0(sK14)) | ~r4_lattice3(sK14,k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),sK15) | spl22_6),
% 3.81/0.85    inference(subsumption_resolution,[],[f2338,f91])).
% 3.81/0.85  fof(f2338,plain,(
% 3.81/0.85    ~v10_lattices(sK14) | v2_struct_0(sK14) | ~l3_lattices(sK14) | ~m1_subset_1(k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),u1_struct_0(sK14)) | ~r4_lattice3(sK14,k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),sK15) | spl22_6),
% 3.81/0.85    inference(subsumption_resolution,[],[f2327,f92])).
% 3.81/0.85  fof(f2327,plain,(
% 3.81/0.85    ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | ~l3_lattices(sK14) | ~m1_subset_1(k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),u1_struct_0(sK14)) | ~r4_lattice3(sK14,k16_lattice3(sK14,a_2_2_lattice3(sK14,sK15)),sK15) | spl22_6),
% 3.81/0.85    inference(resolution,[],[f2320,f1733])).
% 3.81/0.85  fof(f1733,plain,(
% 3.81/0.85    ( ! [X0] : (~sP3(X0,sK14,sK15) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~r4_lattice3(sK14,X0,sK15)) ) | spl22_6),
% 3.81/0.85    inference(resolution,[],[f1732,f109])).
% 3.81/0.85  fof(f1732,plain,(
% 3.81/0.85    ( ! [X0] : (~sP4(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14))) ) | spl22_6),
% 3.81/0.85    inference(subsumption_resolution,[],[f1731,f90])).
% 3.81/0.85  fof(f1731,plain,(
% 3.81/0.85    ( ! [X0] : (~sP4(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | v2_struct_0(sK14)) ) | spl22_6),
% 3.81/0.85    inference(subsumption_resolution,[],[f1730,f91])).
% 3.81/0.85  fof(f1730,plain,(
% 3.81/0.85    ( ! [X0] : (~sP4(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~v10_lattices(sK14) | v2_struct_0(sK14)) ) | spl22_6),
% 3.81/0.85    inference(subsumption_resolution,[],[f1729,f92])).
% 3.81/0.85  fof(f1729,plain,(
% 3.81/0.85    ( ! [X0] : (~sP4(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14)) ) | spl22_6),
% 3.81/0.85    inference(subsumption_resolution,[],[f1728,f93])).
% 3.81/0.85  fof(f1728,plain,(
% 3.81/0.85    ( ! [X0] : (~sP4(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14)) ) | spl22_6),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f1727])).
% 3.81/0.85  fof(f1727,plain,(
% 3.81/0.85    ( ! [X0] : (~sP4(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~m1_subset_1(X0,u1_struct_0(sK14)) | ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14)) ) | spl22_6),
% 3.81/0.85    inference(resolution,[],[f1707,f149])).
% 3.81/0.85  fof(f1707,plain,(
% 3.81/0.85    ( ! [X0] : (~sP5(X0,sK14,sK15) | ~sP4(sK15,sK14,X0) | ~m1_subset_1(X0,u1_struct_0(sK14))) ) | spl22_6),
% 3.81/0.85    inference(superposition,[],[f1701,f106])).
% 3.81/0.85  fof(f1701,plain,(
% 3.81/0.85    ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | spl22_6),
% 3.81/0.85    inference(avatar_component_clause,[],[f1699])).
% 3.81/0.85  fof(f2320,plain,(
% 3.81/0.85    ( ! [X24,X25] : (sP3(k16_lattice3(X24,a_2_2_lattice3(X24,X25)),X24,X25) | ~v4_lattice3(X24) | ~v10_lattices(X24) | v2_struct_0(X24) | ~l3_lattices(X24)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f2319,f225])).
% 3.81/0.85  fof(f225,plain,(
% 3.81/0.85    ( ! [X0,X1] : (sP2(k16_lattice3(X0,X1),X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f218])).
% 3.81/0.85  fof(f218,plain,(
% 3.81/0.85    ( ! [X0,X1] : (sP2(k16_lattice3(X0,X1),X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.81/0.85    inference(resolution,[],[f104,f130])).
% 3.81/0.85  fof(f104,plain,(
% 3.81/0.85    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP2(X1,X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f32])).
% 3.81/0.85  fof(f32,plain,(
% 3.81/0.85    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.81/0.85    inference(definition_folding,[],[f14,f31,f30,f29])).
% 3.81/0.85  fof(f29,plain,(
% 3.81/0.85    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 3.81/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.81/0.85  fof(f30,plain,(
% 3.81/0.85    ! [X2,X0,X1] : (sP1(X2,X0,X1) <=> (sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)))),
% 3.81/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 3.81/0.85  fof(f31,plain,(
% 3.81/0.85    ! [X1,X0] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> sP1(X2,X0,X1)) | ~sP2(X1,X0))),
% 3.81/0.85    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 3.81/0.85  fof(f14,plain,(
% 3.81/0.85    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 3.81/0.85    inference(flattening,[],[f13])).
% 3.81/0.85  fof(f13,plain,(
% 3.81/0.85    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 3.81/0.85    inference(ennf_transformation,[],[f8])).
% 3.81/0.85  fof(f8,axiom,(
% 3.81/0.85    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 3.81/0.85    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_lattice3)).
% 3.81/0.85  fof(f2319,plain,(
% 3.81/0.85    ( ! [X24,X25] : (~l3_lattices(X24) | ~v4_lattice3(X24) | ~v10_lattices(X24) | v2_struct_0(X24) | sP3(k16_lattice3(X24,a_2_2_lattice3(X24,X25)),X24,X25) | ~sP2(k16_lattice3(X24,a_2_2_lattice3(X24,X25)),X24)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f2302,f165])).
% 3.81/0.85  fof(f165,plain,(
% 3.81/0.85    ( ! [X0,X1] : (sP9(X0,k16_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f160])).
% 3.81/0.85  fof(f160,plain,(
% 3.81/0.85    ( ! [X0,X1] : (sP9(X0,k16_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 3.81/0.85    inference(resolution,[],[f129,f130])).
% 3.81/0.85  fof(f2302,plain,(
% 3.81/0.85    ( ! [X24,X25] : (~sP9(X24,k16_lattice3(X24,a_2_2_lattice3(X24,X25))) | ~l3_lattices(X24) | ~v4_lattice3(X24) | ~v10_lattices(X24) | v2_struct_0(X24) | sP3(k16_lattice3(X24,a_2_2_lattice3(X24,X25)),X24,X25) | ~sP2(k16_lattice3(X24,a_2_2_lattice3(X24,X25)),X24)) )),
% 3.81/0.85    inference(resolution,[],[f2289,f179])).
% 3.81/0.85  fof(f179,plain,(
% 3.81/0.85    ( ! [X2,X3] : (r3_lattice3(X2,k16_lattice3(X2,X3),X3) | ~sP2(k16_lattice3(X2,X3),X2)) )),
% 3.81/0.85    inference(resolution,[],[f145,f97])).
% 3.81/0.85  fof(f97,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | r3_lattice3(X1,X2,X0)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f56])).
% 3.81/0.85  fof(f56,plain,(
% 3.81/0.85    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) & ((sP0(X2,X1,X0) & r3_lattice3(X1,X2,X0)) | ~sP1(X0,X1,X2)))),
% 3.81/0.85    inference(rectify,[],[f55])).
% 3.81/0.85  fof(f55,plain,(
% 3.81/0.85    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | ~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2)) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP1(X2,X0,X1)))),
% 3.81/0.85    inference(flattening,[],[f54])).
% 3.81/0.85  fof(f54,plain,(
% 3.81/0.85    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | (~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP1(X2,X0,X1)))),
% 3.81/0.85    inference(nnf_transformation,[],[f30])).
% 3.81/0.85  fof(f145,plain,(
% 3.81/0.85    ( ! [X2,X1] : (sP1(X2,X1,k16_lattice3(X1,X2)) | ~sP2(k16_lattice3(X1,X2),X1)) )),
% 3.81/0.85    inference(equality_resolution,[],[f95])).
% 3.81/0.85  fof(f95,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | k16_lattice3(X1,X2) != X0 | ~sP2(X0,X1)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f53])).
% 3.81/0.85  fof(f53,plain,(
% 3.81/0.85    ! [X0,X1] : (! [X2] : ((k16_lattice3(X1,X2) = X0 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k16_lattice3(X1,X2) != X0)) | ~sP2(X0,X1))),
% 3.81/0.85    inference(rectify,[],[f52])).
% 3.81/0.85  fof(f52,plain,(
% 3.81/0.85    ! [X1,X0] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ~sP1(X2,X0,X1)) & (sP1(X2,X0,X1) | k16_lattice3(X0,X2) != X1)) | ~sP2(X1,X0))),
% 3.81/0.85    inference(nnf_transformation,[],[f31])).
% 3.81/0.85  fof(f2289,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~r3_lattice3(X0,X1,a_2_2_lattice3(X0,X2)) | ~sP9(X0,X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP3(X1,X0,X2)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f2288,f111])).
% 3.81/0.85  fof(f2288,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~sP9(X0,X1) | ~r3_lattice3(X0,X1,a_2_2_lattice3(X0,X2)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP3(X1,X0,X2) | ~m1_subset_1(sK17(X1,X0,X2),u1_struct_0(X0))) )),
% 3.81/0.85    inference(duplicate_literal_removal,[],[f2277])).
% 3.81/0.85  fof(f2277,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (~sP9(X0,X1) | ~r3_lattice3(X0,X1,a_2_2_lattice3(X0,X2)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP3(X1,X0,X2) | ~m1_subset_1(sK17(X1,X0,X2),u1_struct_0(X0)) | sP3(X1,X0,X2)) )),
% 3.81/0.85    inference(resolution,[],[f836,f112])).
% 3.81/0.85  fof(f836,plain,(
% 3.81/0.85    ( ! [X4,X2,X0,X3,X1] : (~r4_lattice3(X3,sK17(X0,X1,X2),X4) | ~sP9(X1,X0) | ~r3_lattice3(X1,X0,a_2_2_lattice3(X3,X4)) | ~l3_lattices(X3) | ~v4_lattice3(X3) | ~v10_lattices(X3) | v2_struct_0(X3) | sP3(X0,X1,X2) | ~m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X3))) )),
% 3.81/0.85    inference(resolution,[],[f636,f147])).
% 3.81/0.85  fof(f147,plain,(
% 3.81/0.85    ( ! [X0,X3,X1] : (sP10(X0,X1,X3) | ~r4_lattice3(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 3.81/0.85    inference(equality_resolution,[],[f136])).
% 3.81/0.85  fof(f136,plain,(
% 3.81/0.85    ( ! [X2,X0,X3,X1] : (sP10(X0,X1,X2) | ~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 3.81/0.85    inference(cnf_transformation,[],[f84])).
% 3.81/0.85  fof(f636,plain,(
% 3.81/0.85    ( ! [X4,X2,X0,X3,X1] : (~sP10(X3,X4,sK17(X1,X0,X2)) | sP3(X1,X0,X2) | ~sP9(X0,X1) | ~r3_lattice3(X0,X1,a_2_2_lattice3(X4,X3)) | ~l3_lattices(X4) | ~v4_lattice3(X4) | ~v10_lattices(X4) | v2_struct_0(X4)) )),
% 3.81/0.85    inference(resolution,[],[f268,f137])).
% 3.81/0.85  fof(f268,plain,(
% 3.81/0.85    ( ! [X4,X2,X0,X3,X1] : (~sP11(sK17(X1,X0,X4),X2,X3) | ~sP9(X0,X1) | sP3(X1,X0,X4) | ~sP10(X3,X2,sK17(X1,X0,X4)) | ~r3_lattice3(X0,X1,a_2_2_lattice3(X2,X3))) )),
% 3.81/0.85    inference(resolution,[],[f266,f132])).
% 3.81/0.85  fof(f132,plain,(
% 3.81/0.85    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~sP10(X2,X1,X0) | ~sP11(X0,X1,X2)) )),
% 3.81/0.85    inference(cnf_transformation,[],[f80])).
% 3.81/0.85  fof(f266,plain,(
% 3.81/0.85    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK17(X0,X1,X2),X3) | ~r3_lattice3(X1,X0,X3) | ~sP9(X1,X0) | sP3(X0,X1,X2)) )),
% 3.81/0.85    inference(subsumption_resolution,[],[f263,f111])).
% 3.81/0.85  fof(f263,plain,(
% 3.81/0.85    ( ! [X2,X0,X3,X1] : (~m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) | ~r2_hidden(sK17(X0,X1,X2),X3) | ~r3_lattice3(X1,X0,X3) | ~sP9(X1,X0) | sP3(X0,X1,X2)) )),
% 3.81/0.85    inference(resolution,[],[f240,f113])).
% 3.81/0.85  fof(f1706,plain,(
% 3.81/0.85    ~spl22_6 | ~spl22_7 | spl22_5),
% 3.81/0.85    inference(avatar_split_clause,[],[f1696,f1677,f1703,f1699])).
% 3.81/0.85  fof(f1677,plain,(
% 3.81/0.85    spl22_5 <=> sP10(sK15,sK14,k15_lattice3(sK14,sK15))),
% 3.81/0.85    introduced(avatar_definition,[new_symbols(naming,[spl22_5])])).
% 3.81/0.85  fof(f1696,plain,(
% 3.81/0.85    ~r4_lattice3(sK14,k15_lattice3(sK14,sK15),sK15) | ~m1_subset_1(k15_lattice3(sK14,sK15),u1_struct_0(sK14)) | spl22_5),
% 3.81/0.85    inference(resolution,[],[f1679,f147])).
% 3.81/0.85  fof(f1679,plain,(
% 3.81/0.85    ~sP10(sK15,sK14,k15_lattice3(sK14,sK15)) | spl22_5),
% 3.81/0.85    inference(avatar_component_clause,[],[f1677])).
% 3.81/0.85  fof(f1687,plain,(
% 3.81/0.85    spl22_4),
% 3.81/0.85    inference(avatar_contradiction_clause,[],[f1686])).
% 3.81/0.85  fof(f1686,plain,(
% 3.81/0.85    $false | spl22_4),
% 3.81/0.85    inference(subsumption_resolution,[],[f1685,f90])).
% 3.81/0.85  fof(f1685,plain,(
% 3.81/0.85    v2_struct_0(sK14) | spl22_4),
% 3.81/0.85    inference(subsumption_resolution,[],[f1684,f91])).
% 3.81/0.85  fof(f1684,plain,(
% 3.81/0.85    ~v10_lattices(sK14) | v2_struct_0(sK14) | spl22_4),
% 3.81/0.85    inference(subsumption_resolution,[],[f1683,f92])).
% 3.81/0.85  fof(f1683,plain,(
% 3.81/0.85    ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | spl22_4),
% 3.81/0.85    inference(subsumption_resolution,[],[f1681,f93])).
% 3.81/0.85  fof(f1681,plain,(
% 3.81/0.85    ~l3_lattices(sK14) | ~v4_lattice3(sK14) | ~v10_lattices(sK14) | v2_struct_0(sK14) | spl22_4),
% 3.81/0.85    inference(resolution,[],[f1675,f137])).
% 3.81/0.85  fof(f1675,plain,(
% 3.81/0.85    ~sP11(k15_lattice3(sK14,sK15),sK14,sK15) | spl22_4),
% 3.81/0.85    inference(avatar_component_clause,[],[f1673])).
% 3.81/0.85  fof(f1673,plain,(
% 3.81/0.85    spl22_4 <=> sP11(k15_lattice3(sK14,sK15),sK14,sK15)),
% 3.81/0.85    introduced(avatar_definition,[new_symbols(naming,[spl22_4])])).
% 3.81/0.85  fof(f1680,plain,(
% 3.81/0.85    ~spl22_4 | ~spl22_5 | spl22_2),
% 3.81/0.85    inference(avatar_split_clause,[],[f1670,f1659,f1677,f1673])).
% 3.81/0.85  fof(f1670,plain,(
% 3.81/0.85    ~sP10(sK15,sK14,k15_lattice3(sK14,sK15)) | ~sP11(k15_lattice3(sK14,sK15),sK14,sK15) | spl22_2),
% 3.81/0.85    inference(resolution,[],[f1661,f132])).
% 3.81/0.85  fof(f1661,plain,(
% 3.81/0.85    ~r2_hidden(k15_lattice3(sK14,sK15),a_2_2_lattice3(sK14,sK15)) | spl22_2),
% 3.81/0.85    inference(avatar_component_clause,[],[f1659])).
% 3.81/0.85  % SZS output end Proof for theBenchmark
% 3.81/0.85  % (26721)------------------------------
% 3.81/0.85  % (26721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.81/0.85  % (26721)Termination reason: Refutation
% 3.81/0.85  
% 3.81/0.85  % (26721)Memory used [KB]: 7419
% 3.81/0.85  % (26721)Time elapsed: 0.394 s
% 3.81/0.85  % (26721)------------------------------
% 3.81/0.85  % (26721)------------------------------
% 3.81/0.85  % (26716)Success in time 0.486 s
%------------------------------------------------------------------------------
