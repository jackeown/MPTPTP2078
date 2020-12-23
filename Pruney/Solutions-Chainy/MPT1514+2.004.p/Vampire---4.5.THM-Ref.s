%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:47 EST 2020

% Result     : Theorem 2.84s
% Output     : Refutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :  278 ( 902 expanded)
%              Number of leaves         :   46 ( 313 expanded)
%              Depth                    :   26
%              Number of atoms          : 1293 (5972 expanded)
%              Number of equality atoms :   89 ( 167 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4048,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f735,f739,f757,f763,f2675,f2679,f2714,f2724,f2753,f2758,f3768,f4047])).

fof(f4047,plain,
    ( ~ spl25_5
    | spl25_8
    | ~ spl25_20
    | ~ spl25_22
    | ~ spl25_24
    | ~ spl25_25
    | ~ spl25_28 ),
    inference(avatar_contradiction_clause,[],[f4046])).

fof(f4046,plain,
    ( $false
    | ~ spl25_5
    | spl25_8
    | ~ spl25_20
    | ~ spl25_22
    | ~ spl25_24
    | ~ spl25_25
    | ~ spl25_28 ),
    inference(subsumption_resolution,[],[f4045,f729])).

fof(f729,plain,
    ( m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15))
    | ~ spl25_5 ),
    inference(avatar_component_clause,[],[f728])).

fof(f728,plain,
    ( spl25_5
  <=> m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_5])])).

fof(f4045,plain,
    ( ~ m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15))
    | ~ spl25_5
    | spl25_8
    | ~ spl25_20
    | ~ spl25_22
    | ~ spl25_24
    | ~ spl25_25
    | ~ spl25_28 ),
    inference(subsumption_resolution,[],[f4043,f756])).

fof(f756,plain,
    ( ~ sP10(sK16,sK15,k15_lattice3(sK15,sK17))
    | spl25_8 ),
    inference(avatar_component_clause,[],[f754])).

fof(f754,plain,
    ( spl25_8
  <=> sP10(sK16,sK15,k15_lattice3(sK15,sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_8])])).

fof(f4043,plain,
    ( sP10(sK16,sK15,k15_lattice3(sK15,sK17))
    | ~ m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15))
    | ~ spl25_5
    | ~ spl25_20
    | ~ spl25_22
    | ~ spl25_24
    | ~ spl25_25
    | ~ spl25_28 ),
    inference(resolution,[],[f4042,f167])).

fof(f167,plain,(
    ! [X0,X3,X1] :
      ( ~ r4_lattice3(X1,X3,X0)
      | sP10(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f154])).

fof(f154,plain,(
    ! [X2,X0,X3,X1] :
      ( sP10(X0,X1,X2)
      | ~ r4_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( ( sP10(X0,X1,X2)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r4_lattice3(X1,sK22(X0,X1,X2),X0)
          & sK22(X0,X1,X2) = X2
          & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP10(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f92,f93])).

fof(f93,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK22(X0,X1,X2),X0)
        & sK22(X0,X1,X2) = X2
        & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f92,plain,(
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
    inference(rectify,[],[f91])).

fof(f91,plain,(
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
    inference(nnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( sP10(X2,X1,X0)
    <=> ? [X3] :
          ( r4_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

fof(f4042,plain,
    ( r4_lattice3(sK15,k15_lattice3(sK15,sK17),sK16)
    | ~ spl25_5
    | ~ spl25_20
    | ~ spl25_22
    | ~ spl25_24
    | ~ spl25_25
    | ~ spl25_28 ),
    inference(subsumption_resolution,[],[f4041,f2673])).

fof(f2673,plain,
    ( sP5(sK15,k15_lattice3(sK15,sK17))
    | ~ spl25_20 ),
    inference(avatar_component_clause,[],[f2672])).

fof(f2672,plain,
    ( spl25_20
  <=> sP5(sK15,k15_lattice3(sK15,sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_20])])).

fof(f4041,plain,
    ( r4_lattice3(sK15,k15_lattice3(sK15,sK17),sK16)
    | ~ sP5(sK15,k15_lattice3(sK15,sK17))
    | ~ spl25_5
    | ~ spl25_22
    | ~ spl25_24
    | ~ spl25_25
    | ~ spl25_28 ),
    inference(resolution,[],[f4039,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP4(X1,X0,X2) )
          & ( sP4(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP5(X0,X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP4(X1,X0,X2) )
      | ~ sP5(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f4039,plain,
    ( sP4(k15_lattice3(sK15,sK17),sK15,sK16)
    | ~ spl25_5
    | ~ spl25_22
    | ~ spl25_24
    | ~ spl25_25
    | ~ spl25_28 ),
    inference(resolution,[],[f4029,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK19(X0,X1,X2),X0)
      | sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK19(X0,X1,X2),X0)
          & r2_hidden(sK19(X0,X1,X2),X2)
          & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f77,f78])).

fof(f78,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK19(X0,X1,X2),X0)
        & r2_hidden(sK19(X0,X1,X2),X2)
        & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X1,X0,X2] :
      ( ( sP4(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X3,X1)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X3,X1)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP4(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X1,X0,X2] :
      ( sP4(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f4029,plain,
    ( r1_lattices(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16),k15_lattice3(sK15,sK17))
    | ~ spl25_5
    | ~ spl25_22
    | ~ spl25_24
    | ~ spl25_25
    | ~ spl25_28 ),
    inference(subsumption_resolution,[],[f4021,f729])).

fof(f4021,plain,
    ( r1_lattices(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16),k15_lattice3(sK15,sK17))
    | ~ m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15))
    | ~ spl25_22
    | ~ spl25_24
    | ~ spl25_25
    | ~ spl25_28 ),
    inference(resolution,[],[f4020,f3746])).

fof(f3746,plain,
    ( sP8(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,k15_lattice3(sK15,sK17))
    | ~ spl25_28 ),
    inference(avatar_component_clause,[],[f3745])).

fof(f3745,plain,
    ( spl25_28
  <=> sP8(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,k15_lattice3(sK15,sK17)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_28])])).

fof(f4020,plain,
    ( ! [X0] :
        ( ~ sP8(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,X0)
        | r1_lattices(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK15)) )
    | ~ spl25_22
    | ~ spl25_24
    | ~ spl25_25 ),
    inference(subsumption_resolution,[],[f4015,f2781])).

fof(f2781,plain,
    ( ! [X2] : sP9(X2,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_25 ),
    inference(subsumption_resolution,[],[f2780,f104])).

fof(f104,plain,(
    ~ v2_struct_0(sK15) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ~ r3_lattices(sK15,k15_lattice3(sK15,sK16),k15_lattice3(sK15,sK17))
    & ! [X3] :
        ( sP0(sK17,X3,sK15)
        | ~ r2_hidden(X3,sK16)
        | ~ m1_subset_1(X3,u1_struct_0(sK15)) )
    & l3_lattices(sK15)
    & v4_lattice3(sK15)
    & v10_lattices(sK15)
    & ~ v2_struct_0(sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f39,f64,f63])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
            & ! [X3] :
                ( sP0(X2,X3,X0)
                | ~ r2_hidden(X3,X1)
                | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X2,X1] :
          ( ~ r3_lattices(sK15,k15_lattice3(sK15,X1),k15_lattice3(sK15,X2))
          & ! [X3] :
              ( sP0(X2,X3,sK15)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(sK15)) ) )
      & l3_lattices(sK15)
      & v4_lattice3(sK15)
      & v10_lattices(sK15)
      & ~ v2_struct_0(sK15) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X2,X1] :
        ( ~ r3_lattices(sK15,k15_lattice3(sK15,X1),k15_lattice3(sK15,X2))
        & ! [X3] :
            ( sP0(X2,X3,sK15)
            | ~ r2_hidden(X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(sK15)) ) )
   => ( ~ r3_lattices(sK15,k15_lattice3(sK15,sK16),k15_lattice3(sK15,sK17))
      & ! [X3] :
          ( sP0(sK17,X3,sK15)
          | ~ r2_hidden(X3,sK16)
          | ~ m1_subset_1(X3,u1_struct_0(sK15)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( sP0(X2,X3,X0)
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f38])).

fof(f38,plain,(
    ! [X2,X3,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X2)
          & r3_lattices(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ sP0(X2,X3,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ~ r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          & ! [X3] :
              ( ? [X4] :
                  ( r2_hidden(X4,X2)
                  & r3_lattices(X0,X3,X4)
                  & m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ r2_hidden(X3,X1)
              | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1,X2] :
            ( ! [X3] :
                ( m1_subset_1(X3,u1_struct_0(X0))
               => ~ ( ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ~ ( r2_hidden(X4,X2)
                            & r3_lattices(X0,X3,X4) ) )
                    & r2_hidden(X3,X1) ) )
           => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1,X2] :
          ( ! [X3] :
              ( m1_subset_1(X3,u1_struct_0(X0))
             => ~ ( ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ~ ( r2_hidden(X4,X2)
                          & r3_lattices(X0,X3,X4) ) )
                  & r2_hidden(X3,X1) ) )
         => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).

fof(f2780,plain,
    ( ! [X2] :
        ( sP9(X2,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
        | v2_struct_0(sK15) )
    | ~ spl25_25 ),
    inference(subsumption_resolution,[],[f2779,f105])).

fof(f105,plain,(
    v10_lattices(sK15) ),
    inference(cnf_transformation,[],[f65])).

fof(f2779,plain,
    ( ! [X2] :
        ( sP9(X2,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
        | ~ v10_lattices(sK15)
        | v2_struct_0(sK15) )
    | ~ spl25_25 ),
    inference(subsumption_resolution,[],[f2778,f106])).

fof(f106,plain,(
    v4_lattice3(sK15) ),
    inference(cnf_transformation,[],[f65])).

fof(f2778,plain,
    ( ! [X2] :
        ( sP9(X2,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
        | ~ v4_lattice3(sK15)
        | ~ v10_lattices(sK15)
        | v2_struct_0(sK15) )
    | ~ spl25_25 ),
    inference(subsumption_resolution,[],[f2765,f107])).

fof(f107,plain,(
    l3_lattices(sK15) ),
    inference(cnf_transformation,[],[f65])).

fof(f2765,plain,
    ( ! [X2] :
        ( sP9(X2,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
        | ~ l3_lattices(sK15)
        | ~ v4_lattice3(sK15)
        | ~ v10_lattices(sK15)
        | v2_struct_0(sK15) )
    | ~ spl25_25 ),
    inference(resolution,[],[f2757,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | sP9(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( sP9(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f33,f51,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( sP8(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattices(X1,X2,X3)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      <=> sP8(X2,X1,X0) )
      | ~ sP9(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_4_lattice3)).

fof(f2757,plain,
    ( m1_subset_1(sK19(k15_lattice3(sK15,sK17),sK15,sK16),u1_struct_0(sK15))
    | ~ spl25_25 ),
    inference(avatar_component_clause,[],[f2755])).

fof(f2755,plain,
    ( spl25_25
  <=> m1_subset_1(sK19(k15_lattice3(sK15,sK17),sK15,sK16),u1_struct_0(sK15)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_25])])).

fof(f4015,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK15))
        | r1_lattices(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16),X0)
        | ~ sP8(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,X0)
        | ~ sP9(X0,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) )
    | ~ spl25_22
    | ~ spl25_24
    | ~ spl25_25 ),
    inference(resolution,[],[f2908,f143])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
      | ~ sP8(X2,X1,X0)
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_4_lattice3(X1,X2))
          | ~ sP8(X2,X1,X0) )
        & ( sP8(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_4_lattice3(X1,X2)) ) )
      | ~ sP9(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f2908,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)))
        | ~ m1_subset_1(X0,u1_struct_0(sK15))
        | r1_lattices(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16),X0) )
    | ~ spl25_22
    | ~ spl25_24
    | ~ spl25_25 ),
    inference(resolution,[],[f2889,f136])).

fof(f136,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP6(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
    ! [X0,X1,X2] :
      ( ( sP6(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK20(X0,X1,X2))
          & r2_hidden(sK20(X0,X1,X2),X2)
          & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP6(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f82,f83])).

fof(f83,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK20(X0,X1,X2))
        & r2_hidden(sK20(X0,X1,X2),X2)
        & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0,X1,X2] :
      ( ( sP6(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP6(X0,X1,X2) ) ) ),
    inference(rectify,[],[f81])).

fof(f81,plain,(
    ! [X1,X0,X2] :
      ( ( sP6(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X1,X3)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP6(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X1,X0,X2] :
      ( sP6(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f2889,plain,
    ( sP6(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)))
    | ~ spl25_22
    | ~ spl25_24
    | ~ spl25_25 ),
    inference(subsumption_resolution,[],[f2888,f2713])).

fof(f2713,plain,
    ( sP7(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_22 ),
    inference(avatar_component_clause,[],[f2711])).

fof(f2711,plain,
    ( spl25_22
  <=> sP7(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_22])])).

fof(f2888,plain,
    ( sP6(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)))
    | ~ sP7(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_24
    | ~ spl25_25 ),
    inference(subsumption_resolution,[],[f2843,f2752])).

fof(f2752,plain,
    ( sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15)
    | ~ spl25_24 ),
    inference(avatar_component_clause,[],[f2750])).

fof(f2750,plain,
    ( spl25_24
  <=> sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_24])])).

fof(f2843,plain,
    ( sP6(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)))
    | ~ sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15)
    | ~ sP7(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_25 ),
    inference(superposition,[],[f204,f2773])).

fof(f2773,plain,
    ( sK19(k15_lattice3(sK15,sK17),sK15,sK16) = k16_lattice3(sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)))
    | ~ spl25_25 ),
    inference(subsumption_resolution,[],[f2772,f104])).

fof(f2772,plain,
    ( sK19(k15_lattice3(sK15,sK17),sK15,sK16) = k16_lattice3(sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)))
    | v2_struct_0(sK15)
    | ~ spl25_25 ),
    inference(subsumption_resolution,[],[f2771,f105])).

fof(f2771,plain,
    ( sK19(k15_lattice3(sK15,sK17),sK15,sK16) = k16_lattice3(sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)))
    | ~ v10_lattices(sK15)
    | v2_struct_0(sK15)
    | ~ spl25_25 ),
    inference(subsumption_resolution,[],[f2770,f106])).

fof(f2770,plain,
    ( sK19(k15_lattice3(sK15,sK17),sK15,sK16) = k16_lattice3(sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)))
    | ~ v4_lattice3(sK15)
    | ~ v10_lattices(sK15)
    | v2_struct_0(sK15)
    | ~ spl25_25 ),
    inference(subsumption_resolution,[],[f2763,f107])).

fof(f2763,plain,
    ( sK19(k15_lattice3(sK15,sK17),sK15,sK16) = k16_lattice3(sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)))
    | ~ l3_lattices(sK15)
    | ~ v4_lattice3(sK15)
    | ~ v10_lattices(sK15)
    | v2_struct_0(sK15)
    | ~ spl25_25 ),
    inference(resolution,[],[f2757,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).

fof(f204,plain,(
    ! [X0,X1] :
      ( sP6(k16_lattice3(X0,X1),X0,X1)
      | ~ sP3(k16_lattice3(X0,X1),X0)
      | ~ sP7(X0,k16_lattice3(X0,X1)) ) ),
    inference(resolution,[],[f203,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattice3(X0,X1,X2)
      | sP6(X1,X0,X2)
      | ~ sP7(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP6(X1,X0,X2) )
          & ( sP6(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP7(X0,X1) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP6(X1,X0,X2) )
      | ~ sP7(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f203,plain,(
    ! [X2,X3] :
      ( r3_lattice3(X2,k16_lattice3(X2,X3),X3)
      | ~ sP3(k16_lattice3(X2,X3),X2) ) ),
    inference(resolution,[],[f165,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | r3_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ sP1(X2,X1,X0)
        | ~ r3_lattice3(X1,X2,X0) )
      & ( ( sP1(X2,X1,X0)
          & r3_lattice3(X1,X2,X0) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ~ sP1(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP1(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ~ sP1(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP1(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ( sP1(X1,X0,X2)
        & r3_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f165,plain,(
    ! [X2,X1] :
      ( sP2(X2,X1,k16_lattice3(X1,X2))
      | ~ sP3(k16_lattice3(X1,X2),X1) ) ),
    inference(equality_resolution,[],[f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X1,X0)
      | k16_lattice3(X1,X2) != X0
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k16_lattice3(X1,X2) = X0
            | ~ sP2(X2,X1,X0) )
          & ( sP2(X2,X1,X0)
            | k16_lattice3(X1,X2) != X0 ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( ( k16_lattice3(X0,X2) = X1
            | ~ sP2(X2,X0,X1) )
          & ( sP2(X2,X0,X1)
            | k16_lattice3(X0,X2) != X1 ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( k16_lattice3(X0,X2) = X1
        <=> sP2(X2,X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f3768,plain,
    ( ~ spl25_21
    | ~ spl25_25
    | spl25_28 ),
    inference(avatar_contradiction_clause,[],[f3767])).

fof(f3767,plain,
    ( $false
    | ~ spl25_21
    | ~ spl25_25
    | spl25_28 ),
    inference(subsumption_resolution,[],[f3766,f104])).

fof(f3766,plain,
    ( v2_struct_0(sK15)
    | ~ spl25_21
    | ~ spl25_25
    | spl25_28 ),
    inference(subsumption_resolution,[],[f3765,f105])).

fof(f3765,plain,
    ( ~ v10_lattices(sK15)
    | v2_struct_0(sK15)
    | ~ spl25_21
    | ~ spl25_25
    | spl25_28 ),
    inference(subsumption_resolution,[],[f3764,f106])).

fof(f3764,plain,
    ( ~ v4_lattice3(sK15)
    | ~ v10_lattices(sK15)
    | v2_struct_0(sK15)
    | ~ spl25_21
    | ~ spl25_25
    | spl25_28 ),
    inference(subsumption_resolution,[],[f3763,f107])).

fof(f3763,plain,
    ( ~ l3_lattices(sK15)
    | ~ v4_lattice3(sK15)
    | ~ v10_lattices(sK15)
    | v2_struct_0(sK15)
    | ~ spl25_21
    | ~ spl25_25
    | spl25_28 ),
    inference(resolution,[],[f3762,f164])).

fof(f164,plain,(
    ! [X2,X0,X1] :
      ( sP13(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( sP13(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f37,f57,f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( sP12(X2,X1,X0)
    <=> ? [X3] :
          ( ? [X4] :
              ( r2_hidden(X4,X2)
              & r3_lattices(X1,X3,X4)
              & m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP12])])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> sP12(X2,X1,X0) )
      | ~ sP13(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP13])])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
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
     => ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      <=> ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).

fof(f3762,plain,
    ( ~ sP13(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,sK17)
    | ~ spl25_21
    | ~ spl25_25
    | spl25_28 ),
    inference(subsumption_resolution,[],[f3761,f2708])).

fof(f2708,plain,
    ( sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_21 ),
    inference(avatar_component_clause,[],[f2707])).

fof(f2707,plain,
    ( spl25_21
  <=> sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_21])])).

fof(f3761,plain,
    ( ~ sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ sP13(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,sK17)
    | ~ spl25_25
    | spl25_28 ),
    inference(resolution,[],[f3755,f157])).

fof(f157,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
      | ~ sP12(X2,X1,X0)
      | ~ sP13(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f95])).

fof(f95,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_5_lattice3(X1,X2))
          | ~ sP12(X2,X1,X0) )
        & ( sP12(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_5_lattice3(X1,X2)) ) )
      | ~ sP13(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f3755,plain,
    ( ~ r2_hidden(sK19(k15_lattice3(sK15,sK17),sK15,sK16),a_2_5_lattice3(sK15,sK17))
    | ~ spl25_25
    | spl25_28 ),
    inference(subsumption_resolution,[],[f3753,f2757])).

fof(f3753,plain,
    ( ~ m1_subset_1(sK19(k15_lattice3(sK15,sK17),sK15,sK16),u1_struct_0(sK15))
    | ~ r2_hidden(sK19(k15_lattice3(sK15,sK17),sK15,sK16),a_2_5_lattice3(sK15,sK17))
    | spl25_28 ),
    inference(resolution,[],[f3747,f988])).

fof(f988,plain,(
    ! [X0,X1] :
      ( sP8(X1,sK15,k15_lattice3(sK15,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK15))
      | ~ r2_hidden(X1,a_2_5_lattice3(sK15,X0)) ) ),
    inference(subsumption_resolution,[],[f987,f104])).

fof(f987,plain,(
    ! [X0,X1] :
      ( sP8(X1,sK15,k15_lattice3(sK15,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK15))
      | v2_struct_0(sK15)
      | ~ r2_hidden(X1,a_2_5_lattice3(sK15,X0)) ) ),
    inference(subsumption_resolution,[],[f986,f105])).

fof(f986,plain,(
    ! [X0,X1] :
      ( sP8(X1,sK15,k15_lattice3(sK15,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK15))
      | ~ v10_lattices(sK15)
      | v2_struct_0(sK15)
      | ~ r2_hidden(X1,a_2_5_lattice3(sK15,X0)) ) ),
    inference(subsumption_resolution,[],[f985,f106])).

fof(f985,plain,(
    ! [X0,X1] :
      ( sP8(X1,sK15,k15_lattice3(sK15,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK15))
      | ~ v4_lattice3(sK15)
      | ~ v10_lattices(sK15)
      | v2_struct_0(sK15)
      | ~ r2_hidden(X1,a_2_5_lattice3(sK15,X0)) ) ),
    inference(subsumption_resolution,[],[f983,f107])).

fof(f983,plain,(
    ! [X0,X1] :
      ( sP8(X1,sK15,k15_lattice3(sK15,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK15))
      | ~ l3_lattices(sK15)
      | ~ v4_lattice3(sK15)
      | ~ v10_lattices(sK15)
      | v2_struct_0(sK15)
      | ~ r2_hidden(X1,a_2_5_lattice3(sK15,X0)) ) ),
    inference(superposition,[],[f587,f296])).

fof(f296,plain,(
    ! [X0] : k15_lattice3(sK15,X0) = k15_lattice3(sK15,a_2_5_lattice3(sK15,X0)) ),
    inference(subsumption_resolution,[],[f295,f104])).

fof(f295,plain,(
    ! [X0] :
      ( k15_lattice3(sK15,X0) = k15_lattice3(sK15,a_2_5_lattice3(sK15,X0))
      | v2_struct_0(sK15) ) ),
    inference(subsumption_resolution,[],[f294,f105])).

fof(f294,plain,(
    ! [X0] :
      ( k15_lattice3(sK15,X0) = k15_lattice3(sK15,a_2_5_lattice3(sK15,X0))
      | ~ v10_lattices(sK15)
      | v2_struct_0(sK15) ) ),
    inference(subsumption_resolution,[],[f293,f107])).

fof(f293,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK15)
      | k15_lattice3(sK15,X0) = k15_lattice3(sK15,a_2_5_lattice3(sK15,X0))
      | ~ v10_lattices(sK15)
      | v2_struct_0(sK15) ) ),
    inference(resolution,[],[f111,f106])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1))
          & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).

fof(f587,plain,(
    ! [X8,X7,X9] :
      ( sP8(X7,X9,k15_lattice3(X9,X8))
      | ~ m1_subset_1(X7,u1_struct_0(X9))
      | ~ l3_lattices(X9)
      | ~ v4_lattice3(X9)
      | ~ v10_lattices(X9)
      | v2_struct_0(X9)
      | ~ r2_hidden(X7,X8) ) ),
    inference(subsumption_resolution,[],[f578,f141])).

fof(f141,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f578,plain,(
    ! [X8,X7,X9] :
      ( ~ r2_hidden(X7,X8)
      | ~ m1_subset_1(X7,u1_struct_0(X9))
      | ~ l3_lattices(X9)
      | ~ v4_lattice3(X9)
      | ~ v10_lattices(X9)
      | v2_struct_0(X9)
      | sP8(X7,X9,k15_lattice3(X9,X8))
      | ~ m1_subset_1(k15_lattice3(X9,X8),u1_struct_0(X9)) ) ),
    inference(resolution,[],[f115,f166])).

fof(f166,plain,(
    ! [X0,X3,X1] :
      ( ~ r3_lattices(X1,X0,X3)
      | sP8(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f147])).

fof(f147,plain,(
    ! [X2,X0,X3,X1] :
      ( sP8(X0,X1,X2)
      | ~ r3_lattices(X1,X0,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( ( sP8(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattices(X1,X0,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r3_lattices(X1,X0,sK21(X0,X1,X2))
          & sK21(X0,X1,X2) = X2
          & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP8(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f87,f88])).

fof(f88,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattices(X1,X0,X4)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattices(X1,X0,sK21(X0,X1,X2))
        & sK21(X0,X1,X2) = X2
        & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X0,X1,X2] :
      ( ( sP8(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattices(X1,X0,X3)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattices(X1,X0,X4)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP8(X0,X1,X2) ) ) ),
    inference(rectify,[],[f86])).

fof(f86,plain,(
    ! [X2,X1,X0] :
      ( ( sP8(X2,X1,X0)
        | ! [X3] :
            ( ~ r3_lattices(X1,X2,X3)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r3_lattices(X1,X2,X3)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP8(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).

fof(f3747,plain,
    ( ~ sP8(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,k15_lattice3(sK15,sK17))
    | spl25_28 ),
    inference(avatar_component_clause,[],[f3745])).

fof(f2758,plain,
    ( ~ spl25_21
    | spl25_25
    | ~ spl25_19 ),
    inference(avatar_split_clause,[],[f2686,f2668,f2755,f2707])).

fof(f2668,plain,
    ( spl25_19
  <=> sK19(k15_lattice3(sK15,sK17),sK15,sK16) = sK23(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_19])])).

fof(f2686,plain,
    ( m1_subset_1(sK19(k15_lattice3(sK15,sK17),sK15,sK16),u1_struct_0(sK15))
    | ~ sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_19 ),
    inference(superposition,[],[f158,f2670])).

fof(f2670,plain,
    ( sK19(k15_lattice3(sK15,sK17),sK15,sK16) = sK23(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_19 ),
    inference(avatar_component_clause,[],[f2668])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1))
      | ~ sP12(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f100,plain,(
    ! [X0,X1,X2] :
      ( ( sP12(X0,X1,X2)
        | ! [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r3_lattices(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r2_hidden(sK24(X0,X1,X2),X0)
          & r3_lattices(X1,sK23(X0,X1,X2),sK24(X0,X1,X2))
          & m1_subset_1(sK24(X0,X1,X2),u1_struct_0(X1))
          & sK23(X0,X1,X2) = X2
          & m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP12(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23,sK24])],[f97,f99,f98])).

fof(f98,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ? [X6] :
              ( r2_hidden(X6,X0)
              & r3_lattices(X1,X5,X6)
              & m1_subset_1(X6,u1_struct_0(X1)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ? [X6] :
            ( r2_hidden(X6,X0)
            & r3_lattices(X1,sK23(X0,X1,X2),X6)
            & m1_subset_1(X6,u1_struct_0(X1)) )
        & sK23(X0,X1,X2) = X2
        & m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f99,plain,(
    ! [X2,X1,X0] :
      ( ? [X6] :
          ( r2_hidden(X6,X0)
          & r3_lattices(X1,sK23(X0,X1,X2),X6)
          & m1_subset_1(X6,u1_struct_0(X1)) )
     => ( r2_hidden(sK24(X0,X1,X2),X0)
        & r3_lattices(X1,sK23(X0,X1,X2),sK24(X0,X1,X2))
        & m1_subset_1(sK24(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X0,X1,X2] :
      ( ( sP12(X0,X1,X2)
        | ! [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(X4,X0)
                | ~ r3_lattices(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X5] :
            ( ? [X6] :
                ( r2_hidden(X6,X0)
                & r3_lattices(X1,X5,X6)
                & m1_subset_1(X6,u1_struct_0(X1)) )
            & X2 = X5
            & m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP12(X0,X1,X2) ) ) ),
    inference(rectify,[],[f96])).

fof(f96,plain,(
    ! [X2,X1,X0] :
      ( ( sP12(X2,X1,X0)
        | ! [X3] :
            ( ! [X4] :
                ( ~ r2_hidden(X4,X2)
                | ~ r3_lattices(X1,X3,X4)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( ? [X4] :
                ( r2_hidden(X4,X2)
                & r3_lattices(X1,X3,X4)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP12(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f56])).

fof(f2753,plain,
    ( ~ spl25_21
    | spl25_24
    | ~ spl25_19 ),
    inference(avatar_split_clause,[],[f2701,f2668,f2750,f2707])).

fof(f2701,plain,
    ( sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15)
    | ~ sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_19 ),
    inference(subsumption_resolution,[],[f2700,f104])).

fof(f2700,plain,
    ( sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15)
    | v2_struct_0(sK15)
    | ~ sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_19 ),
    inference(subsumption_resolution,[],[f2699,f105])).

fof(f2699,plain,
    ( sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15)
    | ~ v10_lattices(sK15)
    | v2_struct_0(sK15)
    | ~ sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_19 ),
    inference(subsumption_resolution,[],[f2698,f106])).

fof(f2698,plain,
    ( sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15)
    | ~ v4_lattice3(sK15)
    | ~ v10_lattices(sK15)
    | v2_struct_0(sK15)
    | ~ sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_19 ),
    inference(subsumption_resolution,[],[f2691,f107])).

fof(f2691,plain,
    ( sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15)
    | ~ l3_lattices(sK15)
    | ~ v4_lattice3(sK15)
    | ~ v10_lattices(sK15)
    | v2_struct_0(sK15)
    | ~ sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_19 ),
    inference(superposition,[],[f245,f2670])).

fof(f245,plain,(
    ! [X21,X22,X20] :
      ( sP3(sK23(X20,X21,X22),X21)
      | ~ l3_lattices(X21)
      | ~ v4_lattice3(X21)
      | ~ v10_lattices(X21)
      | v2_struct_0(X21)
      | ~ sP12(X20,X21,X22) ) ),
    inference(resolution,[],[f126,f158])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP3(X1,X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f25,f42,f41,f40])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r3_lattices(X0,X3,X1)
          | ~ r3_lattice3(X0,X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(f2724,plain,
    ( ~ spl25_5
    | spl25_8
    | ~ spl25_20
    | spl25_21 ),
    inference(avatar_contradiction_clause,[],[f2723])).

fof(f2723,plain,
    ( $false
    | ~ spl25_5
    | spl25_8
    | ~ spl25_20
    | spl25_21 ),
    inference(subsumption_resolution,[],[f2722,f729])).

fof(f2722,plain,
    ( ~ m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15))
    | spl25_8
    | ~ spl25_20
    | spl25_21 ),
    inference(subsumption_resolution,[],[f2720,f756])).

fof(f2720,plain,
    ( sP10(sK16,sK15,k15_lattice3(sK15,sK17))
    | ~ m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15))
    | ~ spl25_20
    | spl25_21 ),
    inference(resolution,[],[f2719,f167])).

fof(f2719,plain,
    ( r4_lattice3(sK15,k15_lattice3(sK15,sK17),sK16)
    | ~ spl25_20
    | spl25_21 ),
    inference(subsumption_resolution,[],[f2718,f2673])).

fof(f2718,plain,
    ( r4_lattice3(sK15,k15_lattice3(sK15,sK17),sK16)
    | ~ sP5(sK15,k15_lattice3(sK15,sK17))
    | spl25_21 ),
    inference(resolution,[],[f2716,f128])).

fof(f2716,plain,
    ( sP4(k15_lattice3(sK15,sK17),sK15,sK16)
    | spl25_21 ),
    inference(subsumption_resolution,[],[f2715,f131])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK19(X0,X1,X2),X2)
      | sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f2715,plain,
    ( ~ r2_hidden(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK16)
    | sP4(k15_lattice3(sK15,sK17),sK15,sK16)
    | spl25_21 ),
    inference(resolution,[],[f2709,f551])).

fof(f551,plain,(
    ! [X6,X5] :
      ( sP12(sK17,sK15,sK19(X5,sK15,X6))
      | ~ r2_hidden(sK19(X5,sK15,X6),sK16)
      | sP4(X5,sK15,X6) ) ),
    inference(subsumption_resolution,[],[f543,f130])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1))
      | sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f543,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(sK19(X5,sK15,X6),u1_struct_0(sK15))
      | sP12(sK17,sK15,sK19(X5,sK15,X6))
      | ~ r2_hidden(sK19(X5,sK15,X6),sK16)
      | sP4(X5,sK15,X6) ) ),
    inference(resolution,[],[f539,f174])).

fof(f174,plain,(
    ! [X0,X1] :
      ( sP0(sK17,sK19(X0,sK15,X1),sK15)
      | ~ r2_hidden(sK19(X0,sK15,X1),sK16)
      | sP4(X0,sK15,X1) ) ),
    inference(resolution,[],[f130,f108])).

fof(f108,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,u1_struct_0(sK15))
      | ~ r2_hidden(X3,sK16)
      | sP0(sK17,X3,sK15) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f539,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | sP12(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f535])).

fof(f535,plain,(
    ! [X2,X0,X1] :
      ( sP12(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ sP0(X0,X2,X1)
      | ~ sP0(X0,X2,X1) ) ),
    inference(resolution,[],[f530,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK14(X0,X1,X2),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(sK14(X0,X1,X2),X0)
        & r3_lattices(X2,X1,sK14(X0,X1,X2))
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X0)
          & r3_lattices(X2,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
     => ( r2_hidden(sK14(X0,X1,X2),X0)
        & r3_lattices(X2,X1,sK14(X0,X1,X2))
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r2_hidden(X3,X0)
          & r3_lattices(X2,X1,X3)
          & m1_subset_1(X3,u1_struct_0(X2)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X2,X3,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X2)
          & r3_lattices(X0,X3,X4)
          & m1_subset_1(X4,u1_struct_0(X0)) )
      | ~ sP0(X2,X3,X0) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f530,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK14(X0,X1,X2),X3)
      | sP12(X3,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f527,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f527,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(sK14(X0,X1,X2),X3)
      | sP12(X3,X2,X1)
      | ~ m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f168,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X2,X1,sK14(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f168,plain,(
    ! [X4,X0,X3,X1] :
      ( ~ r3_lattices(X1,X3,X4)
      | ~ r2_hidden(X4,X0)
      | sP12(X0,X1,X3)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f163])).

fof(f163,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP12(X0,X1,X2)
      | ~ r2_hidden(X4,X0)
      | ~ r3_lattices(X1,X3,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f100])).

fof(f2709,plain,
    ( ~ sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | spl25_21 ),
    inference(avatar_component_clause,[],[f2707])).

fof(f2714,plain,
    ( ~ spl25_21
    | spl25_22
    | ~ spl25_19 ),
    inference(avatar_split_clause,[],[f2695,f2668,f2711,f2707])).

fof(f2695,plain,
    ( sP7(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_19 ),
    inference(subsumption_resolution,[],[f2694,f104])).

fof(f2694,plain,
    ( sP7(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | v2_struct_0(sK15)
    | ~ spl25_19 ),
    inference(subsumption_resolution,[],[f2688,f107])).

fof(f2688,plain,
    ( sP7(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ l3_lattices(sK15)
    | v2_struct_0(sK15)
    | ~ spl25_19 ),
    inference(superposition,[],[f197,f2670])).

fof(f197,plain,(
    ! [X4,X2,X3] :
      ( sP7(X3,sK23(X2,X3,X4))
      | ~ sP12(X2,X3,X4)
      | ~ l3_lattices(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f158,f140])).

fof(f140,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP7(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP7(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f29,f48,f47])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f2679,plain,(
    spl25_20 ),
    inference(avatar_contradiction_clause,[],[f2678])).

fof(f2678,plain,
    ( $false
    | spl25_20 ),
    inference(subsumption_resolution,[],[f2677,f104])).

fof(f2677,plain,
    ( v2_struct_0(sK15)
    | spl25_20 ),
    inference(subsumption_resolution,[],[f2676,f107])).

fof(f2676,plain,
    ( ~ l3_lattices(sK15)
    | v2_struct_0(sK15)
    | spl25_20 ),
    inference(resolution,[],[f2674,f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( sP5(X0,k15_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f175])).

fof(f175,plain,(
    ! [X0,X1] :
      ( sP5(X0,k15_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f133,f141])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP5(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP5(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f27,f45,f44])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f2674,plain,
    ( ~ sP5(sK15,k15_lattice3(sK15,sK17))
    | spl25_20 ),
    inference(avatar_component_clause,[],[f2672])).

fof(f2675,plain,
    ( spl25_19
    | ~ spl25_20
    | ~ spl25_5
    | spl25_8 ),
    inference(avatar_split_clause,[],[f2664,f754,f728,f2672,f2668])).

fof(f2664,plain,
    ( ~ sP5(sK15,k15_lattice3(sK15,sK17))
    | sK19(k15_lattice3(sK15,sK17),sK15,sK16) = sK23(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_5
    | spl25_8 ),
    inference(subsumption_resolution,[],[f2654,f756])).

fof(f2654,plain,
    ( ~ sP5(sK15,k15_lattice3(sK15,sK17))
    | sP10(sK16,sK15,k15_lattice3(sK15,sK17))
    | sK19(k15_lattice3(sK15,sK17),sK15,sK16) = sK23(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))
    | ~ spl25_5 ),
    inference(resolution,[],[f1492,f729])).

fof(f1492,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK15))
      | ~ sP5(sK15,X0)
      | sP10(sK16,sK15,X0)
      | sK19(X0,sK15,sK16) = sK23(sK17,sK15,sK19(X0,sK15,sK16)) ) ),
    inference(resolution,[],[f1491,f167])).

fof(f1491,plain,(
    ! [X2] :
      ( r4_lattice3(sK15,X2,sK16)
      | sK19(X2,sK15,sK16) = sK23(sK17,sK15,sK19(X2,sK15,sK16))
      | ~ sP5(sK15,X2) ) ),
    inference(resolution,[],[f1489,f128])).

fof(f1489,plain,(
    ! [X0] :
      ( sP4(X0,sK15,sK16)
      | sK19(X0,sK15,sK16) = sK23(sK17,sK15,sK19(X0,sK15,sK16)) ) ),
    inference(duplicate_literal_removal,[],[f1488])).

fof(f1488,plain,(
    ! [X0] :
      ( sP4(X0,sK15,sK16)
      | sK19(X0,sK15,sK16) = sK23(sK17,sK15,sK19(X0,sK15,sK16))
      | sP4(X0,sK15,sK16) ) ),
    inference(resolution,[],[f566,f131])).

fof(f566,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK19(X0,sK15,X1),sK16)
      | sP4(X0,sK15,X1)
      | sK19(X0,sK15,X1) = sK23(sK17,sK15,sK19(X0,sK15,X1)) ) ),
    inference(resolution,[],[f551,f159])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( ~ sP12(X0,X1,X2)
      | sK23(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f100])).

fof(f763,plain,(
    spl25_7 ),
    inference(avatar_contradiction_clause,[],[f762])).

fof(f762,plain,
    ( $false
    | spl25_7 ),
    inference(subsumption_resolution,[],[f761,f104])).

fof(f761,plain,
    ( v2_struct_0(sK15)
    | spl25_7 ),
    inference(subsumption_resolution,[],[f760,f105])).

fof(f760,plain,
    ( ~ v10_lattices(sK15)
    | v2_struct_0(sK15)
    | spl25_7 ),
    inference(subsumption_resolution,[],[f759,f106])).

fof(f759,plain,
    ( ~ v4_lattice3(sK15)
    | ~ v10_lattices(sK15)
    | v2_struct_0(sK15)
    | spl25_7 ),
    inference(subsumption_resolution,[],[f758,f107])).

fof(f758,plain,
    ( ~ l3_lattices(sK15)
    | ~ v4_lattice3(sK15)
    | ~ v10_lattices(sK15)
    | v2_struct_0(sK15)
    | spl25_7 ),
    inference(resolution,[],[f752,f155])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( sP11(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( sP11(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f35,f54,f53])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> sP10(X2,X1,X0) )
      | ~ sP11(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).

fof(f752,plain,
    ( ~ sP11(k15_lattice3(sK15,sK17),sK15,sK16)
    | spl25_7 ),
    inference(avatar_component_clause,[],[f750])).

fof(f750,plain,
    ( spl25_7
  <=> sP11(k15_lattice3(sK15,sK17),sK15,sK16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_7])])).

fof(f757,plain,
    ( ~ spl25_7
    | ~ spl25_8
    | spl25_6 ),
    inference(avatar_split_clause,[],[f748,f732,f754,f750])).

fof(f732,plain,
    ( spl25_6
  <=> r2_hidden(k15_lattice3(sK15,sK17),a_2_2_lattice3(sK15,sK16)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl25_6])])).

fof(f748,plain,
    ( ~ sP10(sK16,sK15,k15_lattice3(sK15,sK17))
    | ~ sP11(k15_lattice3(sK15,sK17),sK15,sK16)
    | spl25_6 ),
    inference(resolution,[],[f734,f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ sP10(X2,X1,X0)
      | ~ sP11(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ~ sP10(X2,X1,X0) )
        & ( sP10(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ sP11(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f734,plain,
    ( ~ r2_hidden(k15_lattice3(sK15,sK17),a_2_2_lattice3(sK15,sK16))
    | spl25_6 ),
    inference(avatar_component_clause,[],[f732])).

fof(f739,plain,(
    spl25_5 ),
    inference(avatar_contradiction_clause,[],[f738])).

fof(f738,plain,
    ( $false
    | spl25_5 ),
    inference(subsumption_resolution,[],[f737,f104])).

fof(f737,plain,
    ( v2_struct_0(sK15)
    | spl25_5 ),
    inference(subsumption_resolution,[],[f736,f107])).

fof(f736,plain,
    ( ~ l3_lattices(sK15)
    | v2_struct_0(sK15)
    | spl25_5 ),
    inference(resolution,[],[f730,f141])).

fof(f730,plain,
    ( ~ m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15))
    | spl25_5 ),
    inference(avatar_component_clause,[],[f728])).

fof(f735,plain,
    ( ~ spl25_5
    | ~ spl25_6 ),
    inference(avatar_split_clause,[],[f720,f732,f728])).

fof(f720,plain,
    ( ~ r2_hidden(k15_lattice3(sK15,sK17),a_2_2_lattice3(sK15,sK16))
    | ~ m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15)) ),
    inference(resolution,[],[f662,f109])).

fof(f109,plain,(
    ~ r3_lattices(sK15,k15_lattice3(sK15,sK16),k15_lattice3(sK15,sK17)) ),
    inference(cnf_transformation,[],[f65])).

fof(f662,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK15,k15_lattice3(sK15,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK15,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK15)) ) ),
    inference(subsumption_resolution,[],[f661,f104])).

fof(f661,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK15,k15_lattice3(sK15,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK15,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK15))
      | v2_struct_0(sK15) ) ),
    inference(subsumption_resolution,[],[f660,f105])).

fof(f660,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK15,k15_lattice3(sK15,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK15,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK15))
      | ~ v10_lattices(sK15)
      | v2_struct_0(sK15) ) ),
    inference(subsumption_resolution,[],[f659,f106])).

fof(f659,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK15,k15_lattice3(sK15,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK15,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK15))
      | ~ v4_lattice3(sK15)
      | ~ v10_lattices(sK15)
      | v2_struct_0(sK15) ) ),
    inference(subsumption_resolution,[],[f655,f107])).

fof(f655,plain,(
    ! [X0,X1] :
      ( r3_lattices(sK15,k15_lattice3(sK15,X0),X1)
      | ~ r2_hidden(X1,a_2_2_lattice3(sK15,X0))
      | ~ m1_subset_1(X1,u1_struct_0(sK15))
      | ~ l3_lattices(sK15)
      | ~ v4_lattice3(sK15)
      | ~ v10_lattices(sK15)
      | v2_struct_0(sK15) ) ),
    inference(superposition,[],[f116,f278])).

fof(f278,plain,(
    ! [X0] : k15_lattice3(sK15,X0) = k16_lattice3(sK15,a_2_2_lattice3(sK15,X0)) ),
    inference(subsumption_resolution,[],[f277,f104])).

fof(f277,plain,(
    ! [X0] :
      ( k15_lattice3(sK15,X0) = k16_lattice3(sK15,a_2_2_lattice3(sK15,X0))
      | v2_struct_0(sK15) ) ),
    inference(subsumption_resolution,[],[f276,f105])).

fof(f276,plain,(
    ! [X0] :
      ( k15_lattice3(sK15,X0) = k16_lattice3(sK15,a_2_2_lattice3(sK15,X0))
      | ~ v10_lattices(sK15)
      | v2_struct_0(sK15) ) ),
    inference(subsumption_resolution,[],[f275,f107])).

fof(f275,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK15)
      | k15_lattice3(sK15,X0) = k16_lattice3(sK15,a_2_2_lattice3(sK15,X0))
      | ~ v10_lattices(sK15)
      | v2_struct_0(sK15) ) ),
    inference(resolution,[],[f110,f106])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
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
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : run_vampire %s %d
% 0.14/0.32  % Computer   : n006.cluster.edu
% 0.14/0.32  % Model      : x86_64 x86_64
% 0.14/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.32  % Memory     : 8042.1875MB
% 0.14/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.32  % CPULimit   : 60
% 0.14/0.32  % WCLimit    : 600
% 0.14/0.32  % DateTime   : Tue Dec  1 19:53:22 EST 2020
% 0.14/0.32  % CPUTime    : 
% 0.18/0.41  % (8323)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.18/0.45  % (8321)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.18/0.46  % (8346)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.18/0.46  % (8331)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.18/0.47  % (8341)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.18/0.47  % (8337)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.18/0.47  % (8329)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.18/0.47  % (8340)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.18/0.48  % (8330)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.18/0.48  % (8325)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.18/0.48  % (8330)Refutation not found, incomplete strategy% (8330)------------------------------
% 0.18/0.48  % (8330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (8330)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.48  
% 0.18/0.48  % (8330)Memory used [KB]: 10618
% 0.18/0.48  % (8330)Time elapsed: 0.105 s
% 0.18/0.48  % (8330)------------------------------
% 0.18/0.48  % (8330)------------------------------
% 0.18/0.48  % (8325)Refutation not found, incomplete strategy% (8325)------------------------------
% 0.18/0.48  % (8325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.48  % (8325)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.48  
% 0.18/0.48  % (8325)Memory used [KB]: 10618
% 0.18/0.48  % (8325)Time elapsed: 0.091 s
% 0.18/0.48  % (8325)------------------------------
% 0.18/0.48  % (8325)------------------------------
% 0.18/0.48  % (8327)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.18/0.48  % (8320)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.18/0.48  % (8322)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.18/0.48  % (8342)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.18/0.48  % (8344)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.18/0.49  % (8334)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.49  % (8319)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.18/0.49  % (8319)Refutation not found, incomplete strategy% (8319)------------------------------
% 0.18/0.49  % (8319)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (8319)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (8319)Memory used [KB]: 10618
% 0.18/0.49  % (8319)Time elapsed: 0.102 s
% 0.18/0.49  % (8319)------------------------------
% 0.18/0.49  % (8319)------------------------------
% 0.18/0.49  % (8326)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.18/0.49  % (8339)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.18/0.50  % (8345)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.18/0.50  % (8335)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.18/0.50  % (8324)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.18/0.50  % (8324)Refutation not found, incomplete strategy% (8324)------------------------------
% 0.18/0.50  % (8324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.50  % (8324)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.50  
% 0.18/0.50  % (8324)Memory used [KB]: 6012
% 0.18/0.50  % (8324)Time elapsed: 0.115 s
% 0.18/0.50  % (8324)------------------------------
% 0.18/0.50  % (8324)------------------------------
% 0.18/0.50  % (8328)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.18/0.50  % (8333)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.18/0.51  % (8333)Refutation not found, incomplete strategy% (8333)------------------------------
% 0.18/0.51  % (8333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.51  % (8336)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.34/0.51  % (8333)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.51  
% 1.34/0.51  % (8333)Memory used [KB]: 6140
% 1.34/0.51  % (8333)Time elapsed: 0.120 s
% 1.34/0.51  % (8333)------------------------------
% 1.34/0.51  % (8333)------------------------------
% 1.34/0.51  % (8338)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.50/0.61  % (8328)Refutation not found, incomplete strategy% (8328)------------------------------
% 1.50/0.61  % (8328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.62  % (8328)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.62  
% 1.50/0.62  % (8328)Memory used [KB]: 6140
% 1.50/0.62  % (8328)Time elapsed: 0.221 s
% 1.50/0.62  % (8328)------------------------------
% 1.50/0.62  % (8328)------------------------------
% 2.84/0.73  % (8346)Refutation found. Thanks to Tanya!
% 2.84/0.73  % SZS status Theorem for theBenchmark
% 2.84/0.73  % SZS output start Proof for theBenchmark
% 2.84/0.75  fof(f4048,plain,(
% 2.84/0.75    $false),
% 2.84/0.75    inference(avatar_sat_refutation,[],[f735,f739,f757,f763,f2675,f2679,f2714,f2724,f2753,f2758,f3768,f4047])).
% 2.84/0.75  fof(f4047,plain,(
% 2.84/0.75    ~spl25_5 | spl25_8 | ~spl25_20 | ~spl25_22 | ~spl25_24 | ~spl25_25 | ~spl25_28),
% 2.84/0.75    inference(avatar_contradiction_clause,[],[f4046])).
% 2.84/0.75  fof(f4046,plain,(
% 2.84/0.75    $false | (~spl25_5 | spl25_8 | ~spl25_20 | ~spl25_22 | ~spl25_24 | ~spl25_25 | ~spl25_28)),
% 2.84/0.75    inference(subsumption_resolution,[],[f4045,f729])).
% 2.84/0.75  fof(f729,plain,(
% 2.84/0.75    m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15)) | ~spl25_5),
% 2.84/0.75    inference(avatar_component_clause,[],[f728])).
% 2.84/0.75  fof(f728,plain,(
% 2.84/0.75    spl25_5 <=> m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15))),
% 2.84/0.75    introduced(avatar_definition,[new_symbols(naming,[spl25_5])])).
% 2.84/0.75  fof(f4045,plain,(
% 2.84/0.75    ~m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15)) | (~spl25_5 | spl25_8 | ~spl25_20 | ~spl25_22 | ~spl25_24 | ~spl25_25 | ~spl25_28)),
% 2.84/0.75    inference(subsumption_resolution,[],[f4043,f756])).
% 2.84/0.75  fof(f756,plain,(
% 2.84/0.75    ~sP10(sK16,sK15,k15_lattice3(sK15,sK17)) | spl25_8),
% 2.84/0.75    inference(avatar_component_clause,[],[f754])).
% 2.84/0.75  fof(f754,plain,(
% 2.84/0.75    spl25_8 <=> sP10(sK16,sK15,k15_lattice3(sK15,sK17))),
% 2.84/0.75    introduced(avatar_definition,[new_symbols(naming,[spl25_8])])).
% 2.84/0.75  fof(f4043,plain,(
% 2.84/0.75    sP10(sK16,sK15,k15_lattice3(sK15,sK17)) | ~m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15)) | (~spl25_5 | ~spl25_20 | ~spl25_22 | ~spl25_24 | ~spl25_25 | ~spl25_28)),
% 2.84/0.75    inference(resolution,[],[f4042,f167])).
% 2.84/0.75  fof(f167,plain,(
% 2.84/0.75    ( ! [X0,X3,X1] : (~r4_lattice3(X1,X3,X0) | sP10(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.84/0.75    inference(equality_resolution,[],[f154])).
% 2.84/0.75  fof(f154,plain,(
% 2.84/0.75    ( ! [X2,X0,X3,X1] : (sP10(X0,X1,X2) | ~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.84/0.75    inference(cnf_transformation,[],[f94])).
% 2.84/0.75  fof(f94,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((sP10(X0,X1,X2) | ! [X3] : (~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK22(X0,X1,X2),X0) & sK22(X0,X1,X2) = X2 & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1))) | ~sP10(X0,X1,X2)))),
% 2.84/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK22])],[f92,f93])).
% 2.84/0.75  fof(f93,plain,(
% 2.84/0.75    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK22(X0,X1,X2),X0) & sK22(X0,X1,X2) = X2 & m1_subset_1(sK22(X0,X1,X2),u1_struct_0(X1))))),
% 2.84/0.75    introduced(choice_axiom,[])).
% 2.84/0.75  fof(f92,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((sP10(X0,X1,X2) | ! [X3] : (~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP10(X0,X1,X2)))),
% 2.84/0.75    inference(rectify,[],[f91])).
% 2.84/0.75  fof(f91,plain,(
% 2.84/0.75    ! [X2,X1,X0] : ((sP10(X2,X1,X0) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP10(X2,X1,X0)))),
% 2.84/0.75    inference(nnf_transformation,[],[f53])).
% 2.84/0.75  fof(f53,plain,(
% 2.84/0.75    ! [X2,X1,X0] : (sP10(X2,X1,X0) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 2.84/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).
% 2.84/0.75  fof(f4042,plain,(
% 2.84/0.75    r4_lattice3(sK15,k15_lattice3(sK15,sK17),sK16) | (~spl25_5 | ~spl25_20 | ~spl25_22 | ~spl25_24 | ~spl25_25 | ~spl25_28)),
% 2.84/0.75    inference(subsumption_resolution,[],[f4041,f2673])).
% 2.84/0.75  fof(f2673,plain,(
% 2.84/0.75    sP5(sK15,k15_lattice3(sK15,sK17)) | ~spl25_20),
% 2.84/0.75    inference(avatar_component_clause,[],[f2672])).
% 2.84/0.75  fof(f2672,plain,(
% 2.84/0.75    spl25_20 <=> sP5(sK15,k15_lattice3(sK15,sK17))),
% 2.84/0.75    introduced(avatar_definition,[new_symbols(naming,[spl25_20])])).
% 2.84/0.75  fof(f4041,plain,(
% 2.84/0.75    r4_lattice3(sK15,k15_lattice3(sK15,sK17),sK16) | ~sP5(sK15,k15_lattice3(sK15,sK17)) | (~spl25_5 | ~spl25_22 | ~spl25_24 | ~spl25_25 | ~spl25_28)),
% 2.84/0.75    inference(resolution,[],[f4039,f128])).
% 2.84/0.75  fof(f128,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (~sP4(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP5(X0,X1)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f75])).
% 2.84/0.75  fof(f75,plain,(
% 2.84/0.75    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP4(X1,X0,X2)) & (sP4(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP5(X0,X1))),
% 2.84/0.75    inference(nnf_transformation,[],[f45])).
% 2.84/0.75  fof(f45,plain,(
% 2.84/0.75    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP4(X1,X0,X2)) | ~sP5(X0,X1))),
% 2.84/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 2.84/0.75  fof(f4039,plain,(
% 2.84/0.75    sP4(k15_lattice3(sK15,sK17),sK15,sK16) | (~spl25_5 | ~spl25_22 | ~spl25_24 | ~spl25_25 | ~spl25_28)),
% 2.84/0.75    inference(resolution,[],[f4029,f132])).
% 2.84/0.75  fof(f132,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK19(X0,X1,X2),X0) | sP4(X0,X1,X2)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f79])).
% 2.84/0.75  fof(f79,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | (~r1_lattices(X1,sK19(X0,X1,X2),X0) & r2_hidden(sK19(X0,X1,X2),X2) & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 2.84/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK19])],[f77,f78])).
% 2.84/0.75  fof(f78,plain,(
% 2.84/0.75    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK19(X0,X1,X2),X0) & r2_hidden(sK19(X0,X1,X2),X2) & m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1))))),
% 2.84/0.75    introduced(choice_axiom,[])).
% 2.84/0.75  fof(f77,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 2.84/0.75    inference(rectify,[],[f76])).
% 2.84/0.75  fof(f76,plain,(
% 2.84/0.75    ! [X1,X0,X2] : ((sP4(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP4(X1,X0,X2)))),
% 2.84/0.75    inference(nnf_transformation,[],[f44])).
% 2.84/0.75  fof(f44,plain,(
% 2.84/0.75    ! [X1,X0,X2] : (sP4(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 2.84/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 2.84/0.75  fof(f4029,plain,(
% 2.84/0.75    r1_lattices(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16),k15_lattice3(sK15,sK17)) | (~spl25_5 | ~spl25_22 | ~spl25_24 | ~spl25_25 | ~spl25_28)),
% 2.84/0.75    inference(subsumption_resolution,[],[f4021,f729])).
% 2.84/0.75  fof(f4021,plain,(
% 2.84/0.75    r1_lattices(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16),k15_lattice3(sK15,sK17)) | ~m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15)) | (~spl25_22 | ~spl25_24 | ~spl25_25 | ~spl25_28)),
% 2.84/0.75    inference(resolution,[],[f4020,f3746])).
% 2.84/0.75  fof(f3746,plain,(
% 2.84/0.75    sP8(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,k15_lattice3(sK15,sK17)) | ~spl25_28),
% 2.84/0.75    inference(avatar_component_clause,[],[f3745])).
% 2.84/0.75  fof(f3745,plain,(
% 2.84/0.75    spl25_28 <=> sP8(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,k15_lattice3(sK15,sK17))),
% 2.84/0.75    introduced(avatar_definition,[new_symbols(naming,[spl25_28])])).
% 2.84/0.75  fof(f4020,plain,(
% 2.84/0.75    ( ! [X0] : (~sP8(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,X0) | r1_lattices(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16),X0) | ~m1_subset_1(X0,u1_struct_0(sK15))) ) | (~spl25_22 | ~spl25_24 | ~spl25_25)),
% 2.84/0.75    inference(subsumption_resolution,[],[f4015,f2781])).
% 2.84/0.75  fof(f2781,plain,(
% 2.84/0.75    ( ! [X2] : (sP9(X2,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))) ) | ~spl25_25),
% 2.84/0.75    inference(subsumption_resolution,[],[f2780,f104])).
% 2.84/0.75  fof(f104,plain,(
% 2.84/0.75    ~v2_struct_0(sK15)),
% 2.84/0.75    inference(cnf_transformation,[],[f65])).
% 2.84/0.75  fof(f65,plain,(
% 2.84/0.75    (~r3_lattices(sK15,k15_lattice3(sK15,sK16),k15_lattice3(sK15,sK17)) & ! [X3] : (sP0(sK17,X3,sK15) | ~r2_hidden(X3,sK16) | ~m1_subset_1(X3,u1_struct_0(sK15)))) & l3_lattices(sK15) & v4_lattice3(sK15) & v10_lattices(sK15) & ~v2_struct_0(sK15)),
% 2.84/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15,sK16,sK17])],[f39,f64,f63])).
% 2.84/0.75  fof(f63,plain,(
% 2.84/0.75    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (sP0(X2,X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X2,X1] : (~r3_lattices(sK15,k15_lattice3(sK15,X1),k15_lattice3(sK15,X2)) & ! [X3] : (sP0(X2,X3,sK15) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(sK15)))) & l3_lattices(sK15) & v4_lattice3(sK15) & v10_lattices(sK15) & ~v2_struct_0(sK15))),
% 2.84/0.75    introduced(choice_axiom,[])).
% 2.84/0.75  fof(f64,plain,(
% 2.84/0.75    ? [X2,X1] : (~r3_lattices(sK15,k15_lattice3(sK15,X1),k15_lattice3(sK15,X2)) & ! [X3] : (sP0(X2,X3,sK15) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(sK15)))) => (~r3_lattices(sK15,k15_lattice3(sK15,sK16),k15_lattice3(sK15,sK17)) & ! [X3] : (sP0(sK17,X3,sK15) | ~r2_hidden(X3,sK16) | ~m1_subset_1(X3,u1_struct_0(sK15))))),
% 2.84/0.75    introduced(choice_axiom,[])).
% 2.84/0.75  fof(f39,plain,(
% 2.84/0.75    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (sP0(X2,X3,X0) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.84/0.75    inference(definition_folding,[],[f15,f38])).
% 2.84/0.75  fof(f38,plain,(
% 2.84/0.75    ! [X2,X3,X0] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~sP0(X2,X3,X0))),
% 2.84/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.84/0.75  fof(f15,plain,(
% 2.84/0.75    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.84/0.75    inference(flattening,[],[f14])).
% 2.84/0.75  fof(f14,plain,(
% 2.84/0.75    ? [X0] : (? [X1,X2] : (~r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) & ! [X3] : ((? [X4] : ((r2_hidden(X4,X2) & r3_lattices(X0,X3,X4)) & m1_subset_1(X4,u1_struct_0(X0))) | ~r2_hidden(X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.84/0.75    inference(ennf_transformation,[],[f13])).
% 2.84/0.75  fof(f13,negated_conjecture,(
% 2.84/0.75    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 2.84/0.75    inference(negated_conjecture,[],[f12])).
% 2.84/0.75  fof(f12,conjecture,(
% 2.84/0.75    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).
% 2.84/0.75  fof(f2780,plain,(
% 2.84/0.75    ( ! [X2] : (sP9(X2,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | v2_struct_0(sK15)) ) | ~spl25_25),
% 2.84/0.75    inference(subsumption_resolution,[],[f2779,f105])).
% 2.84/0.75  fof(f105,plain,(
% 2.84/0.75    v10_lattices(sK15)),
% 2.84/0.75    inference(cnf_transformation,[],[f65])).
% 2.84/0.75  fof(f2779,plain,(
% 2.84/0.75    ( ! [X2] : (sP9(X2,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~v10_lattices(sK15) | v2_struct_0(sK15)) ) | ~spl25_25),
% 2.84/0.75    inference(subsumption_resolution,[],[f2778,f106])).
% 2.84/0.75  fof(f106,plain,(
% 2.84/0.75    v4_lattice3(sK15)),
% 2.84/0.75    inference(cnf_transformation,[],[f65])).
% 2.84/0.75  fof(f2778,plain,(
% 2.84/0.75    ( ! [X2] : (sP9(X2,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~v4_lattice3(sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15)) ) | ~spl25_25),
% 2.84/0.75    inference(subsumption_resolution,[],[f2765,f107])).
% 2.84/0.75  fof(f107,plain,(
% 2.84/0.75    l3_lattices(sK15)),
% 2.84/0.75    inference(cnf_transformation,[],[f65])).
% 2.84/0.75  fof(f2765,plain,(
% 2.84/0.75    ( ! [X2] : (sP9(X2,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~l3_lattices(sK15) | ~v4_lattice3(sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15)) ) | ~spl25_25),
% 2.84/0.75    inference(resolution,[],[f2757,f148])).
% 2.84/0.75  fof(f148,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | sP9(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f52])).
% 2.84/0.75  fof(f52,plain,(
% 2.84/0.75    ! [X0,X1,X2] : (sP9(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 2.84/0.75    inference(definition_folding,[],[f33,f51,f50])).
% 2.84/0.75  fof(f50,plain,(
% 2.84/0.75    ! [X2,X1,X0] : (sP8(X2,X1,X0) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 2.84/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 2.84/0.75  fof(f51,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> sP8(X2,X1,X0)) | ~sP9(X0,X1,X2))),
% 2.84/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 2.84/0.75  fof(f33,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 2.84/0.75    inference(flattening,[],[f32])).
% 2.84/0.75  fof(f32,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 2.84/0.75    inference(ennf_transformation,[],[f5])).
% 2.84/0.75  fof(f5,axiom,(
% 2.84/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X1)) & l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_4_lattice3(X1,X2)) <=> ? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_4_lattice3)).
% 2.84/0.75  fof(f2757,plain,(
% 2.84/0.75    m1_subset_1(sK19(k15_lattice3(sK15,sK17),sK15,sK16),u1_struct_0(sK15)) | ~spl25_25),
% 2.84/0.75    inference(avatar_component_clause,[],[f2755])).
% 2.84/0.75  fof(f2755,plain,(
% 2.84/0.75    spl25_25 <=> m1_subset_1(sK19(k15_lattice3(sK15,sK17),sK15,sK16),u1_struct_0(sK15))),
% 2.84/0.75    introduced(avatar_definition,[new_symbols(naming,[spl25_25])])).
% 2.84/0.75  fof(f4015,plain,(
% 2.84/0.75    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK15)) | r1_lattices(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16),X0) | ~sP8(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,X0) | ~sP9(X0,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))) ) | (~spl25_22 | ~spl25_24 | ~spl25_25)),
% 2.84/0.75    inference(resolution,[],[f2908,f143])).
% 2.84/0.75  fof(f143,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ~sP8(X2,X1,X0) | ~sP9(X0,X1,X2)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f85])).
% 2.84/0.75  fof(f85,plain,(
% 2.84/0.75    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_4_lattice3(X1,X2)) | ~sP8(X2,X1,X0)) & (sP8(X2,X1,X0) | ~r2_hidden(X0,a_2_4_lattice3(X1,X2)))) | ~sP9(X0,X1,X2))),
% 2.84/0.75    inference(nnf_transformation,[],[f51])).
% 2.84/0.75  fof(f2908,plain,(
% 2.84/0.75    ( ! [X0] : (~r2_hidden(X0,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))) | ~m1_subset_1(X0,u1_struct_0(sK15)) | r1_lattices(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16),X0)) ) | (~spl25_22 | ~spl25_24 | ~spl25_25)),
% 2.84/0.75    inference(resolution,[],[f2889,f136])).
% 2.84/0.75  fof(f136,plain,(
% 2.84/0.75    ( ! [X4,X2,X0,X1] : (~sP6(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f84])).
% 2.84/0.75  fof(f84,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((sP6(X0,X1,X2) | (~r1_lattices(X1,X0,sK20(X0,X1,X2)) & r2_hidden(sK20(X0,X1,X2),X2) & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP6(X0,X1,X2)))),
% 2.84/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK20])],[f82,f83])).
% 2.84/0.75  fof(f83,plain,(
% 2.84/0.75    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK20(X0,X1,X2)) & r2_hidden(sK20(X0,X1,X2),X2) & m1_subset_1(sK20(X0,X1,X2),u1_struct_0(X1))))),
% 2.84/0.75    introduced(choice_axiom,[])).
% 2.84/0.75  fof(f82,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((sP6(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP6(X0,X1,X2)))),
% 2.84/0.75    inference(rectify,[],[f81])).
% 2.84/0.75  fof(f81,plain,(
% 2.84/0.75    ! [X1,X0,X2] : ((sP6(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP6(X1,X0,X2)))),
% 2.84/0.75    inference(nnf_transformation,[],[f47])).
% 2.84/0.75  fof(f47,plain,(
% 2.84/0.75    ! [X1,X0,X2] : (sP6(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 2.84/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 2.84/0.75  fof(f2889,plain,(
% 2.84/0.75    sP6(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))) | (~spl25_22 | ~spl25_24 | ~spl25_25)),
% 2.84/0.75    inference(subsumption_resolution,[],[f2888,f2713])).
% 2.84/0.75  fof(f2713,plain,(
% 2.84/0.75    sP7(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~spl25_22),
% 2.84/0.75    inference(avatar_component_clause,[],[f2711])).
% 2.84/0.75  fof(f2711,plain,(
% 2.84/0.75    spl25_22 <=> sP7(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))),
% 2.84/0.75    introduced(avatar_definition,[new_symbols(naming,[spl25_22])])).
% 2.84/0.75  fof(f2888,plain,(
% 2.84/0.75    sP6(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))) | ~sP7(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | (~spl25_24 | ~spl25_25)),
% 2.84/0.75    inference(subsumption_resolution,[],[f2843,f2752])).
% 2.84/0.75  fof(f2752,plain,(
% 2.84/0.75    sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15) | ~spl25_24),
% 2.84/0.75    inference(avatar_component_clause,[],[f2750])).
% 2.84/0.75  fof(f2750,plain,(
% 2.84/0.75    spl25_24 <=> sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15)),
% 2.84/0.75    introduced(avatar_definition,[new_symbols(naming,[spl25_24])])).
% 2.84/0.75  fof(f2843,plain,(
% 2.84/0.75    sP6(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))) | ~sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15) | ~sP7(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~spl25_25),
% 2.84/0.75    inference(superposition,[],[f204,f2773])).
% 2.84/0.75  fof(f2773,plain,(
% 2.84/0.75    sK19(k15_lattice3(sK15,sK17),sK15,sK16) = k16_lattice3(sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))) | ~spl25_25),
% 2.84/0.75    inference(subsumption_resolution,[],[f2772,f104])).
% 2.84/0.75  fof(f2772,plain,(
% 2.84/0.75    sK19(k15_lattice3(sK15,sK17),sK15,sK16) = k16_lattice3(sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))) | v2_struct_0(sK15) | ~spl25_25),
% 2.84/0.75    inference(subsumption_resolution,[],[f2771,f105])).
% 2.84/0.75  fof(f2771,plain,(
% 2.84/0.75    sK19(k15_lattice3(sK15,sK17),sK15,sK16) = k16_lattice3(sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))) | ~v10_lattices(sK15) | v2_struct_0(sK15) | ~spl25_25),
% 2.84/0.75    inference(subsumption_resolution,[],[f2770,f106])).
% 2.84/0.75  fof(f2770,plain,(
% 2.84/0.75    sK19(k15_lattice3(sK15,sK17),sK15,sK16) = k16_lattice3(sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))) | ~v4_lattice3(sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15) | ~spl25_25),
% 2.84/0.75    inference(subsumption_resolution,[],[f2763,f107])).
% 2.84/0.75  fof(f2763,plain,(
% 2.84/0.75    sK19(k15_lattice3(sK15,sK17),sK15,sK16) = k16_lattice3(sK15,a_2_4_lattice3(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))) | ~l3_lattices(sK15) | ~v4_lattice3(sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15) | ~spl25_25),
% 2.84/0.75    inference(resolution,[],[f2757,f114])).
% 2.84/0.75  fof(f114,plain,(
% 2.84/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f21])).
% 2.84/0.75  fof(f21,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.84/0.75    inference(flattening,[],[f20])).
% 2.84/0.75  fof(f20,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.84/0.75    inference(ennf_transformation,[],[f10])).
% 2.84/0.75  fof(f10,axiom,(
% 2.84/0.75    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).
% 2.84/0.75  fof(f204,plain,(
% 2.84/0.75    ( ! [X0,X1] : (sP6(k16_lattice3(X0,X1),X0,X1) | ~sP3(k16_lattice3(X0,X1),X0) | ~sP7(X0,k16_lattice3(X0,X1))) )),
% 2.84/0.75    inference(resolution,[],[f203,f134])).
% 2.84/0.75  fof(f134,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (~r3_lattice3(X0,X1,X2) | sP6(X1,X0,X2) | ~sP7(X0,X1)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f80])).
% 2.84/0.75  fof(f80,plain,(
% 2.84/0.75    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP6(X1,X0,X2)) & (sP6(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP7(X0,X1))),
% 2.84/0.75    inference(nnf_transformation,[],[f48])).
% 2.84/0.75  fof(f48,plain,(
% 2.84/0.75    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP6(X1,X0,X2)) | ~sP7(X0,X1))),
% 2.84/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 2.84/0.75  fof(f203,plain,(
% 2.84/0.75    ( ! [X2,X3] : (r3_lattice3(X2,k16_lattice3(X2,X3),X3) | ~sP3(k16_lattice3(X2,X3),X2)) )),
% 2.84/0.75    inference(resolution,[],[f165,f119])).
% 2.84/0.75  fof(f119,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | r3_lattice3(X1,X2,X0)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f70])).
% 2.84/0.75  fof(f70,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ~sP1(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) & ((sP1(X2,X1,X0) & r3_lattice3(X1,X2,X0)) | ~sP2(X0,X1,X2)))),
% 2.84/0.75    inference(rectify,[],[f69])).
% 2.84/0.75  fof(f69,plain,(
% 2.84/0.75    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ~sP1(X1,X0,X2) | ~r3_lattice3(X0,X1,X2)) & ((sP1(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP2(X2,X0,X1)))),
% 2.84/0.75    inference(flattening,[],[f68])).
% 2.84/0.75  fof(f68,plain,(
% 2.84/0.75    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | (~sP1(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) & ((sP1(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP2(X2,X0,X1)))),
% 2.84/0.75    inference(nnf_transformation,[],[f41])).
% 2.84/0.75  fof(f41,plain,(
% 2.84/0.75    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> (sP1(X1,X0,X2) & r3_lattice3(X0,X1,X2)))),
% 2.84/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.84/0.75  fof(f165,plain,(
% 2.84/0.75    ( ! [X2,X1] : (sP2(X2,X1,k16_lattice3(X1,X2)) | ~sP3(k16_lattice3(X1,X2),X1)) )),
% 2.84/0.75    inference(equality_resolution,[],[f117])).
% 2.84/0.75  fof(f117,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (sP2(X2,X1,X0) | k16_lattice3(X1,X2) != X0 | ~sP3(X0,X1)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f67])).
% 2.84/0.75  fof(f67,plain,(
% 2.84/0.75    ! [X0,X1] : (! [X2] : ((k16_lattice3(X1,X2) = X0 | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | k16_lattice3(X1,X2) != X0)) | ~sP3(X0,X1))),
% 2.84/0.75    inference(rectify,[],[f66])).
% 2.84/0.75  fof(f66,plain,(
% 2.84/0.75    ! [X1,X0] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | k16_lattice3(X0,X2) != X1)) | ~sP3(X1,X0))),
% 2.84/0.75    inference(nnf_transformation,[],[f42])).
% 2.84/0.75  fof(f42,plain,(
% 2.84/0.75    ! [X1,X0] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> sP2(X2,X0,X1)) | ~sP3(X1,X0))),
% 2.84/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.84/0.75  fof(f3768,plain,(
% 2.84/0.75    ~spl25_21 | ~spl25_25 | spl25_28),
% 2.84/0.75    inference(avatar_contradiction_clause,[],[f3767])).
% 2.84/0.75  fof(f3767,plain,(
% 2.84/0.75    $false | (~spl25_21 | ~spl25_25 | spl25_28)),
% 2.84/0.75    inference(subsumption_resolution,[],[f3766,f104])).
% 2.84/0.75  fof(f3766,plain,(
% 2.84/0.75    v2_struct_0(sK15) | (~spl25_21 | ~spl25_25 | spl25_28)),
% 2.84/0.75    inference(subsumption_resolution,[],[f3765,f105])).
% 2.84/0.75  fof(f3765,plain,(
% 2.84/0.75    ~v10_lattices(sK15) | v2_struct_0(sK15) | (~spl25_21 | ~spl25_25 | spl25_28)),
% 2.84/0.75    inference(subsumption_resolution,[],[f3764,f106])).
% 2.84/0.75  fof(f3764,plain,(
% 2.84/0.75    ~v4_lattice3(sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15) | (~spl25_21 | ~spl25_25 | spl25_28)),
% 2.84/0.75    inference(subsumption_resolution,[],[f3763,f107])).
% 2.84/0.75  fof(f3763,plain,(
% 2.84/0.75    ~l3_lattices(sK15) | ~v4_lattice3(sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15) | (~spl25_21 | ~spl25_25 | spl25_28)),
% 2.84/0.75    inference(resolution,[],[f3762,f164])).
% 2.84/0.75  fof(f164,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (sP13(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f58])).
% 2.84/0.75  fof(f58,plain,(
% 2.84/0.75    ! [X0,X1,X2] : (sP13(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 2.84/0.75    inference(definition_folding,[],[f37,f57,f56])).
% 2.84/0.75  fof(f56,plain,(
% 2.84/0.75    ! [X2,X1,X0] : (sP12(X2,X1,X0) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 2.84/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP12])])).
% 2.84/0.75  fof(f57,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> sP12(X2,X1,X0)) | ~sP13(X0,X1,X2))),
% 2.84/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP13])])).
% 2.84/0.75  fof(f37,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 2.84/0.75    inference(flattening,[],[f36])).
% 2.84/0.75  fof(f36,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 2.84/0.75    inference(ennf_transformation,[],[f6])).
% 2.84/0.75  fof(f6,axiom,(
% 2.84/0.75    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_5_lattice3(X1,X2)) <=> ? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_5_lattice3)).
% 2.84/0.75  fof(f3762,plain,(
% 2.84/0.75    ~sP13(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,sK17) | (~spl25_21 | ~spl25_25 | spl25_28)),
% 2.84/0.75    inference(subsumption_resolution,[],[f3761,f2708])).
% 2.84/0.75  fof(f2708,plain,(
% 2.84/0.75    sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~spl25_21),
% 2.84/0.75    inference(avatar_component_clause,[],[f2707])).
% 2.84/0.75  fof(f2707,plain,(
% 2.84/0.75    spl25_21 <=> sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))),
% 2.84/0.75    introduced(avatar_definition,[new_symbols(naming,[spl25_21])])).
% 2.84/0.75  fof(f3761,plain,(
% 2.84/0.75    ~sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~sP13(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,sK17) | (~spl25_25 | spl25_28)),
% 2.84/0.75    inference(resolution,[],[f3755,f157])).
% 2.84/0.75  fof(f157,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ~sP12(X2,X1,X0) | ~sP13(X0,X1,X2)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f95])).
% 2.84/0.75  fof(f95,plain,(
% 2.84/0.75    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_5_lattice3(X1,X2)) | ~sP12(X2,X1,X0)) & (sP12(X2,X1,X0) | ~r2_hidden(X0,a_2_5_lattice3(X1,X2)))) | ~sP13(X0,X1,X2))),
% 2.84/0.75    inference(nnf_transformation,[],[f57])).
% 2.84/0.75  fof(f3755,plain,(
% 2.84/0.75    ~r2_hidden(sK19(k15_lattice3(sK15,sK17),sK15,sK16),a_2_5_lattice3(sK15,sK17)) | (~spl25_25 | spl25_28)),
% 2.84/0.75    inference(subsumption_resolution,[],[f3753,f2757])).
% 2.84/0.75  fof(f3753,plain,(
% 2.84/0.75    ~m1_subset_1(sK19(k15_lattice3(sK15,sK17),sK15,sK16),u1_struct_0(sK15)) | ~r2_hidden(sK19(k15_lattice3(sK15,sK17),sK15,sK16),a_2_5_lattice3(sK15,sK17)) | spl25_28),
% 2.84/0.75    inference(resolution,[],[f3747,f988])).
% 2.84/0.75  fof(f988,plain,(
% 2.84/0.75    ( ! [X0,X1] : (sP8(X1,sK15,k15_lattice3(sK15,X0)) | ~m1_subset_1(X1,u1_struct_0(sK15)) | ~r2_hidden(X1,a_2_5_lattice3(sK15,X0))) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f987,f104])).
% 2.84/0.75  fof(f987,plain,(
% 2.84/0.75    ( ! [X0,X1] : (sP8(X1,sK15,k15_lattice3(sK15,X0)) | ~m1_subset_1(X1,u1_struct_0(sK15)) | v2_struct_0(sK15) | ~r2_hidden(X1,a_2_5_lattice3(sK15,X0))) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f986,f105])).
% 2.84/0.75  fof(f986,plain,(
% 2.84/0.75    ( ! [X0,X1] : (sP8(X1,sK15,k15_lattice3(sK15,X0)) | ~m1_subset_1(X1,u1_struct_0(sK15)) | ~v10_lattices(sK15) | v2_struct_0(sK15) | ~r2_hidden(X1,a_2_5_lattice3(sK15,X0))) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f985,f106])).
% 2.84/0.75  fof(f985,plain,(
% 2.84/0.75    ( ! [X0,X1] : (sP8(X1,sK15,k15_lattice3(sK15,X0)) | ~m1_subset_1(X1,u1_struct_0(sK15)) | ~v4_lattice3(sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15) | ~r2_hidden(X1,a_2_5_lattice3(sK15,X0))) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f983,f107])).
% 2.84/0.75  fof(f983,plain,(
% 2.84/0.75    ( ! [X0,X1] : (sP8(X1,sK15,k15_lattice3(sK15,X0)) | ~m1_subset_1(X1,u1_struct_0(sK15)) | ~l3_lattices(sK15) | ~v4_lattice3(sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15) | ~r2_hidden(X1,a_2_5_lattice3(sK15,X0))) )),
% 2.84/0.75    inference(superposition,[],[f587,f296])).
% 2.84/0.75  fof(f296,plain,(
% 2.84/0.75    ( ! [X0] : (k15_lattice3(sK15,X0) = k15_lattice3(sK15,a_2_5_lattice3(sK15,X0))) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f295,f104])).
% 2.84/0.75  fof(f295,plain,(
% 2.84/0.75    ( ! [X0] : (k15_lattice3(sK15,X0) = k15_lattice3(sK15,a_2_5_lattice3(sK15,X0)) | v2_struct_0(sK15)) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f294,f105])).
% 2.84/0.75  fof(f294,plain,(
% 2.84/0.75    ( ! [X0] : (k15_lattice3(sK15,X0) = k15_lattice3(sK15,a_2_5_lattice3(sK15,X0)) | ~v10_lattices(sK15) | v2_struct_0(sK15)) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f293,f107])).
% 2.84/0.75  fof(f293,plain,(
% 2.84/0.75    ( ! [X0] : (~l3_lattices(sK15) | k15_lattice3(sK15,X0) = k15_lattice3(sK15,a_2_5_lattice3(sK15,X0)) | ~v10_lattices(sK15) | v2_struct_0(sK15)) )),
% 2.84/0.75    inference(resolution,[],[f111,f106])).
% 2.84/0.75  fof(f111,plain,(
% 2.84/0.75    ( ! [X0,X1] : (~v4_lattice3(X0) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f19])).
% 2.84/0.75  fof(f19,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.84/0.75    inference(flattening,[],[f18])).
% 2.84/0.75  fof(f18,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.84/0.75    inference(ennf_transformation,[],[f11])).
% 2.84/0.75  fof(f11,axiom,(
% 2.84/0.75    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (k16_lattice3(X0,X1) = k16_lattice3(X0,a_2_6_lattice3(X0,X1)) & k15_lattice3(X0,X1) = k15_lattice3(X0,a_2_5_lattice3(X0,X1))))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_lattice3)).
% 2.84/0.75  fof(f587,plain,(
% 2.84/0.75    ( ! [X8,X7,X9] : (sP8(X7,X9,k15_lattice3(X9,X8)) | ~m1_subset_1(X7,u1_struct_0(X9)) | ~l3_lattices(X9) | ~v4_lattice3(X9) | ~v10_lattices(X9) | v2_struct_0(X9) | ~r2_hidden(X7,X8)) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f578,f141])).
% 2.84/0.75  fof(f141,plain,(
% 2.84/0.75    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f31])).
% 2.84/0.75  fof(f31,plain,(
% 2.84/0.75    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.84/0.75    inference(flattening,[],[f30])).
% 2.84/0.75  fof(f30,plain,(
% 2.84/0.75    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.84/0.75    inference(ennf_transformation,[],[f3])).
% 2.84/0.75  fof(f3,axiom,(
% 2.84/0.75    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 2.84/0.75  fof(f578,plain,(
% 2.84/0.75    ( ! [X8,X7,X9] : (~r2_hidden(X7,X8) | ~m1_subset_1(X7,u1_struct_0(X9)) | ~l3_lattices(X9) | ~v4_lattice3(X9) | ~v10_lattices(X9) | v2_struct_0(X9) | sP8(X7,X9,k15_lattice3(X9,X8)) | ~m1_subset_1(k15_lattice3(X9,X8),u1_struct_0(X9))) )),
% 2.84/0.75    inference(resolution,[],[f115,f166])).
% 2.84/0.75  fof(f166,plain,(
% 2.84/0.75    ( ! [X0,X3,X1] : (~r3_lattices(X1,X0,X3) | sP8(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.84/0.75    inference(equality_resolution,[],[f147])).
% 2.84/0.75  fof(f147,plain,(
% 2.84/0.75    ( ! [X2,X0,X3,X1] : (sP8(X0,X1,X2) | ~r3_lattices(X1,X0,X3) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.84/0.75    inference(cnf_transformation,[],[f89])).
% 2.84/0.75  fof(f89,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((sP8(X0,X1,X2) | ! [X3] : (~r3_lattices(X1,X0,X3) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattices(X1,X0,sK21(X0,X1,X2)) & sK21(X0,X1,X2) = X2 & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1))) | ~sP8(X0,X1,X2)))),
% 2.84/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK21])],[f87,f88])).
% 2.84/0.75  fof(f88,plain,(
% 2.84/0.75    ! [X2,X1,X0] : (? [X4] : (r3_lattices(X1,X0,X4) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattices(X1,X0,sK21(X0,X1,X2)) & sK21(X0,X1,X2) = X2 & m1_subset_1(sK21(X0,X1,X2),u1_struct_0(X1))))),
% 2.84/0.75    introduced(choice_axiom,[])).
% 2.84/0.75  fof(f87,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((sP8(X0,X1,X2) | ! [X3] : (~r3_lattices(X1,X0,X3) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattices(X1,X0,X4) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP8(X0,X1,X2)))),
% 2.84/0.75    inference(rectify,[],[f86])).
% 2.84/0.75  fof(f86,plain,(
% 2.84/0.75    ! [X2,X1,X0] : ((sP8(X2,X1,X0) | ! [X3] : (~r3_lattices(X1,X2,X3) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattices(X1,X2,X3) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP8(X2,X1,X0)))),
% 2.84/0.75    inference(nnf_transformation,[],[f50])).
% 2.84/0.75  fof(f115,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k15_lattice3(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f23])).
% 2.84/0.75  fof(f23,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.84/0.75    inference(flattening,[],[f22])).
% 2.84/0.75  fof(f22,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : (! [X2] : ((r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.84/0.75    inference(ennf_transformation,[],[f9])).
% 2.84/0.75  fof(f9,axiom,(
% 2.84/0.75    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r2_hidden(X1,X2) => (r3_lattices(X0,k16_lattice3(X0,X2),X1) & r3_lattices(X0,X1,k15_lattice3(X0,X2))))))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_lattice3)).
% 2.84/0.75  fof(f3747,plain,(
% 2.84/0.75    ~sP8(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15,k15_lattice3(sK15,sK17)) | spl25_28),
% 2.84/0.75    inference(avatar_component_clause,[],[f3745])).
% 2.84/0.75  fof(f2758,plain,(
% 2.84/0.75    ~spl25_21 | spl25_25 | ~spl25_19),
% 2.84/0.75    inference(avatar_split_clause,[],[f2686,f2668,f2755,f2707])).
% 2.84/0.75  fof(f2668,plain,(
% 2.84/0.75    spl25_19 <=> sK19(k15_lattice3(sK15,sK17),sK15,sK16) = sK23(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16))),
% 2.84/0.75    introduced(avatar_definition,[new_symbols(naming,[spl25_19])])).
% 2.84/0.75  fof(f2686,plain,(
% 2.84/0.75    m1_subset_1(sK19(k15_lattice3(sK15,sK17),sK15,sK16),u1_struct_0(sK15)) | ~sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~spl25_19),
% 2.84/0.75    inference(superposition,[],[f158,f2670])).
% 2.84/0.75  fof(f2670,plain,(
% 2.84/0.75    sK19(k15_lattice3(sK15,sK17),sK15,sK16) = sK23(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~spl25_19),
% 2.84/0.75    inference(avatar_component_clause,[],[f2668])).
% 2.84/0.75  fof(f158,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1)) | ~sP12(X0,X1,X2)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f100])).
% 2.84/0.75  fof(f100,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((sP12(X0,X1,X2) | ! [X3] : (! [X4] : (~r2_hidden(X4,X0) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (((r2_hidden(sK24(X0,X1,X2),X0) & r3_lattices(X1,sK23(X0,X1,X2),sK24(X0,X1,X2)) & m1_subset_1(sK24(X0,X1,X2),u1_struct_0(X1))) & sK23(X0,X1,X2) = X2 & m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1))) | ~sP12(X0,X1,X2)))),
% 2.84/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK23,sK24])],[f97,f99,f98])).
% 2.84/0.75  fof(f98,plain,(
% 2.84/0.75    ! [X2,X1,X0] : (? [X5] : (? [X6] : (r2_hidden(X6,X0) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X1))) => (? [X6] : (r2_hidden(X6,X0) & r3_lattices(X1,sK23(X0,X1,X2),X6) & m1_subset_1(X6,u1_struct_0(X1))) & sK23(X0,X1,X2) = X2 & m1_subset_1(sK23(X0,X1,X2),u1_struct_0(X1))))),
% 2.84/0.75    introduced(choice_axiom,[])).
% 2.84/0.75  fof(f99,plain,(
% 2.84/0.75    ! [X2,X1,X0] : (? [X6] : (r2_hidden(X6,X0) & r3_lattices(X1,sK23(X0,X1,X2),X6) & m1_subset_1(X6,u1_struct_0(X1))) => (r2_hidden(sK24(X0,X1,X2),X0) & r3_lattices(X1,sK23(X0,X1,X2),sK24(X0,X1,X2)) & m1_subset_1(sK24(X0,X1,X2),u1_struct_0(X1))))),
% 2.84/0.75    introduced(choice_axiom,[])).
% 2.84/0.75  fof(f97,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((sP12(X0,X1,X2) | ! [X3] : (! [X4] : (~r2_hidden(X4,X0) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X5] : (? [X6] : (r2_hidden(X6,X0) & r3_lattices(X1,X5,X6) & m1_subset_1(X6,u1_struct_0(X1))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X1))) | ~sP12(X0,X1,X2)))),
% 2.84/0.75    inference(rectify,[],[f96])).
% 2.84/0.75  fof(f96,plain,(
% 2.84/0.75    ! [X2,X1,X0] : ((sP12(X2,X1,X0) | ! [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X1,X3,X4) & m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP12(X2,X1,X0)))),
% 2.84/0.75    inference(nnf_transformation,[],[f56])).
% 2.84/0.75  fof(f2753,plain,(
% 2.84/0.75    ~spl25_21 | spl25_24 | ~spl25_19),
% 2.84/0.75    inference(avatar_split_clause,[],[f2701,f2668,f2750,f2707])).
% 2.84/0.75  fof(f2701,plain,(
% 2.84/0.75    sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15) | ~sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~spl25_19),
% 2.84/0.75    inference(subsumption_resolution,[],[f2700,f104])).
% 2.84/0.75  fof(f2700,plain,(
% 2.84/0.75    sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15) | v2_struct_0(sK15) | ~sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~spl25_19),
% 2.84/0.75    inference(subsumption_resolution,[],[f2699,f105])).
% 2.84/0.75  fof(f2699,plain,(
% 2.84/0.75    sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15) | ~sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~spl25_19),
% 2.84/0.75    inference(subsumption_resolution,[],[f2698,f106])).
% 2.84/0.75  fof(f2698,plain,(
% 2.84/0.75    sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15) | ~v4_lattice3(sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15) | ~sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~spl25_19),
% 2.84/0.75    inference(subsumption_resolution,[],[f2691,f107])).
% 2.84/0.75  fof(f2691,plain,(
% 2.84/0.75    sP3(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK15) | ~l3_lattices(sK15) | ~v4_lattice3(sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15) | ~sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~spl25_19),
% 2.84/0.75    inference(superposition,[],[f245,f2670])).
% 2.84/0.75  fof(f245,plain,(
% 2.84/0.75    ( ! [X21,X22,X20] : (sP3(sK23(X20,X21,X22),X21) | ~l3_lattices(X21) | ~v4_lattice3(X21) | ~v10_lattices(X21) | v2_struct_0(X21) | ~sP12(X20,X21,X22)) )),
% 2.84/0.75    inference(resolution,[],[f126,f158])).
% 2.84/0.75  fof(f126,plain,(
% 2.84/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP3(X1,X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f43])).
% 2.84/0.75  fof(f43,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : (sP3(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.84/0.75    inference(definition_folding,[],[f25,f42,f41,f40])).
% 2.84/0.75  fof(f40,plain,(
% 2.84/0.75    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 2.84/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.84/0.75  fof(f25,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.84/0.75    inference(flattening,[],[f24])).
% 2.84/0.75  fof(f24,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.84/0.75    inference(ennf_transformation,[],[f7])).
% 2.84/0.75  fof(f7,axiom,(
% 2.84/0.75    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 2.84/0.75  fof(f2724,plain,(
% 2.84/0.75    ~spl25_5 | spl25_8 | ~spl25_20 | spl25_21),
% 2.84/0.75    inference(avatar_contradiction_clause,[],[f2723])).
% 2.84/0.75  fof(f2723,plain,(
% 2.84/0.75    $false | (~spl25_5 | spl25_8 | ~spl25_20 | spl25_21)),
% 2.84/0.75    inference(subsumption_resolution,[],[f2722,f729])).
% 2.84/0.75  fof(f2722,plain,(
% 2.84/0.75    ~m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15)) | (spl25_8 | ~spl25_20 | spl25_21)),
% 2.84/0.75    inference(subsumption_resolution,[],[f2720,f756])).
% 2.84/0.75  fof(f2720,plain,(
% 2.84/0.75    sP10(sK16,sK15,k15_lattice3(sK15,sK17)) | ~m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15)) | (~spl25_20 | spl25_21)),
% 2.84/0.75    inference(resolution,[],[f2719,f167])).
% 2.84/0.75  fof(f2719,plain,(
% 2.84/0.75    r4_lattice3(sK15,k15_lattice3(sK15,sK17),sK16) | (~spl25_20 | spl25_21)),
% 2.84/0.75    inference(subsumption_resolution,[],[f2718,f2673])).
% 2.84/0.75  fof(f2718,plain,(
% 2.84/0.75    r4_lattice3(sK15,k15_lattice3(sK15,sK17),sK16) | ~sP5(sK15,k15_lattice3(sK15,sK17)) | spl25_21),
% 2.84/0.75    inference(resolution,[],[f2716,f128])).
% 2.84/0.75  fof(f2716,plain,(
% 2.84/0.75    sP4(k15_lattice3(sK15,sK17),sK15,sK16) | spl25_21),
% 2.84/0.75    inference(subsumption_resolution,[],[f2715,f131])).
% 2.84/0.75  fof(f131,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (r2_hidden(sK19(X0,X1,X2),X2) | sP4(X0,X1,X2)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f79])).
% 2.84/0.75  fof(f2715,plain,(
% 2.84/0.75    ~r2_hidden(sK19(k15_lattice3(sK15,sK17),sK15,sK16),sK16) | sP4(k15_lattice3(sK15,sK17),sK15,sK16) | spl25_21),
% 2.84/0.75    inference(resolution,[],[f2709,f551])).
% 2.84/0.75  fof(f551,plain,(
% 2.84/0.75    ( ! [X6,X5] : (sP12(sK17,sK15,sK19(X5,sK15,X6)) | ~r2_hidden(sK19(X5,sK15,X6),sK16) | sP4(X5,sK15,X6)) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f543,f130])).
% 2.84/0.75  fof(f130,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (m1_subset_1(sK19(X0,X1,X2),u1_struct_0(X1)) | sP4(X0,X1,X2)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f79])).
% 2.84/0.75  fof(f543,plain,(
% 2.84/0.75    ( ! [X6,X5] : (~m1_subset_1(sK19(X5,sK15,X6),u1_struct_0(sK15)) | sP12(sK17,sK15,sK19(X5,sK15,X6)) | ~r2_hidden(sK19(X5,sK15,X6),sK16) | sP4(X5,sK15,X6)) )),
% 2.84/0.75    inference(resolution,[],[f539,f174])).
% 2.84/0.75  fof(f174,plain,(
% 2.84/0.75    ( ! [X0,X1] : (sP0(sK17,sK19(X0,sK15,X1),sK15) | ~r2_hidden(sK19(X0,sK15,X1),sK16) | sP4(X0,sK15,X1)) )),
% 2.84/0.75    inference(resolution,[],[f130,f108])).
% 2.84/0.75  fof(f108,plain,(
% 2.84/0.75    ( ! [X3] : (~m1_subset_1(X3,u1_struct_0(sK15)) | ~r2_hidden(X3,sK16) | sP0(sK17,X3,sK15)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f65])).
% 2.84/0.75  fof(f539,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (~sP0(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | sP12(X0,X1,X2)) )),
% 2.84/0.75    inference(duplicate_literal_removal,[],[f535])).
% 2.84/0.75  fof(f535,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (sP12(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~sP0(X0,X2,X1) | ~sP0(X0,X2,X1)) )),
% 2.84/0.75    inference(resolution,[],[f530,f103])).
% 2.84/0.75  fof(f103,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (r2_hidden(sK14(X0,X1,X2),X0) | ~sP0(X0,X1,X2)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f62])).
% 2.84/0.75  fof(f62,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((r2_hidden(sK14(X0,X1,X2),X0) & r3_lattices(X2,X1,sK14(X0,X1,X2)) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X2))) | ~sP0(X0,X1,X2))),
% 2.84/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f60,f61])).
% 2.84/0.75  fof(f61,plain,(
% 2.84/0.75    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X3,X0) & r3_lattices(X2,X1,X3) & m1_subset_1(X3,u1_struct_0(X2))) => (r2_hidden(sK14(X0,X1,X2),X0) & r3_lattices(X2,X1,sK14(X0,X1,X2)) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X2))))),
% 2.84/0.75    introduced(choice_axiom,[])).
% 2.84/0.75  fof(f60,plain,(
% 2.84/0.75    ! [X0,X1,X2] : (? [X3] : (r2_hidden(X3,X0) & r3_lattices(X2,X1,X3) & m1_subset_1(X3,u1_struct_0(X2))) | ~sP0(X0,X1,X2))),
% 2.84/0.75    inference(rectify,[],[f59])).
% 2.84/0.75  fof(f59,plain,(
% 2.84/0.75    ! [X2,X3,X0] : (? [X4] : (r2_hidden(X4,X2) & r3_lattices(X0,X3,X4) & m1_subset_1(X4,u1_struct_0(X0))) | ~sP0(X2,X3,X0))),
% 2.84/0.75    inference(nnf_transformation,[],[f38])).
% 2.84/0.75  fof(f530,plain,(
% 2.84/0.75    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK14(X0,X1,X2),X3) | sP12(X3,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f527,f101])).
% 2.84/0.75  fof(f101,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f62])).
% 2.84/0.75  fof(f527,plain,(
% 2.84/0.75    ( ! [X2,X0,X3,X1] : (~r2_hidden(sK14(X0,X1,X2),X3) | sP12(X3,X2,X1) | ~m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 2.84/0.75    inference(resolution,[],[f168,f102])).
% 2.84/0.75  fof(f102,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (r3_lattices(X2,X1,sK14(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f62])).
% 2.84/0.75  fof(f168,plain,(
% 2.84/0.75    ( ! [X4,X0,X3,X1] : (~r3_lattices(X1,X3,X4) | ~r2_hidden(X4,X0) | sP12(X0,X1,X3) | ~m1_subset_1(X4,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.84/0.75    inference(equality_resolution,[],[f163])).
% 2.84/0.75  fof(f163,plain,(
% 2.84/0.75    ( ! [X4,X2,X0,X3,X1] : (sP12(X0,X1,X2) | ~r2_hidden(X4,X0) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.84/0.75    inference(cnf_transformation,[],[f100])).
% 2.84/0.75  fof(f2709,plain,(
% 2.84/0.75    ~sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | spl25_21),
% 2.84/0.75    inference(avatar_component_clause,[],[f2707])).
% 2.84/0.75  fof(f2714,plain,(
% 2.84/0.75    ~spl25_21 | spl25_22 | ~spl25_19),
% 2.84/0.75    inference(avatar_split_clause,[],[f2695,f2668,f2711,f2707])).
% 2.84/0.75  fof(f2695,plain,(
% 2.84/0.75    sP7(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~spl25_19),
% 2.84/0.75    inference(subsumption_resolution,[],[f2694,f104])).
% 2.84/0.75  fof(f2694,plain,(
% 2.84/0.75    sP7(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | v2_struct_0(sK15) | ~spl25_19),
% 2.84/0.75    inference(subsumption_resolution,[],[f2688,f107])).
% 2.84/0.75  fof(f2688,plain,(
% 2.84/0.75    sP7(sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~sP12(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~l3_lattices(sK15) | v2_struct_0(sK15) | ~spl25_19),
% 2.84/0.75    inference(superposition,[],[f197,f2670])).
% 2.84/0.75  fof(f197,plain,(
% 2.84/0.75    ( ! [X4,X2,X3] : (sP7(X3,sK23(X2,X3,X4)) | ~sP12(X2,X3,X4) | ~l3_lattices(X3) | v2_struct_0(X3)) )),
% 2.84/0.75    inference(resolution,[],[f158,f140])).
% 2.84/0.75  fof(f140,plain,(
% 2.84/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP7(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f49])).
% 2.84/0.75  fof(f49,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : (sP7(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.84/0.75    inference(definition_folding,[],[f29,f48,f47])).
% 2.84/0.75  fof(f29,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.84/0.75    inference(flattening,[],[f28])).
% 2.84/0.75  fof(f28,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.84/0.75    inference(ennf_transformation,[],[f1])).
% 2.84/0.75  fof(f1,axiom,(
% 2.84/0.75    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 2.84/0.75  fof(f2679,plain,(
% 2.84/0.75    spl25_20),
% 2.84/0.75    inference(avatar_contradiction_clause,[],[f2678])).
% 2.84/0.75  fof(f2678,plain,(
% 2.84/0.75    $false | spl25_20),
% 2.84/0.75    inference(subsumption_resolution,[],[f2677,f104])).
% 2.84/0.75  fof(f2677,plain,(
% 2.84/0.75    v2_struct_0(sK15) | spl25_20),
% 2.84/0.75    inference(subsumption_resolution,[],[f2676,f107])).
% 2.84/0.75  fof(f2676,plain,(
% 2.84/0.75    ~l3_lattices(sK15) | v2_struct_0(sK15) | spl25_20),
% 2.84/0.75    inference(resolution,[],[f2674,f179])).
% 2.84/0.75  fof(f179,plain,(
% 2.84/0.75    ( ! [X0,X1] : (sP5(X0,k15_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.84/0.75    inference(duplicate_literal_removal,[],[f175])).
% 2.84/0.75  fof(f175,plain,(
% 2.84/0.75    ( ! [X0,X1] : (sP5(X0,k15_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.84/0.75    inference(resolution,[],[f133,f141])).
% 2.84/0.75  fof(f133,plain,(
% 2.84/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP5(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f46])).
% 2.84/0.75  fof(f46,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : (sP5(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.84/0.75    inference(definition_folding,[],[f27,f45,f44])).
% 2.84/0.75  fof(f27,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.84/0.75    inference(flattening,[],[f26])).
% 2.84/0.75  fof(f26,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.84/0.75    inference(ennf_transformation,[],[f2])).
% 2.84/0.75  fof(f2,axiom,(
% 2.84/0.75    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 2.84/0.75  fof(f2674,plain,(
% 2.84/0.75    ~sP5(sK15,k15_lattice3(sK15,sK17)) | spl25_20),
% 2.84/0.75    inference(avatar_component_clause,[],[f2672])).
% 2.84/0.75  fof(f2675,plain,(
% 2.84/0.75    spl25_19 | ~spl25_20 | ~spl25_5 | spl25_8),
% 2.84/0.75    inference(avatar_split_clause,[],[f2664,f754,f728,f2672,f2668])).
% 2.84/0.75  fof(f2664,plain,(
% 2.84/0.75    ~sP5(sK15,k15_lattice3(sK15,sK17)) | sK19(k15_lattice3(sK15,sK17),sK15,sK16) = sK23(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | (~spl25_5 | spl25_8)),
% 2.84/0.75    inference(subsumption_resolution,[],[f2654,f756])).
% 2.84/0.75  fof(f2654,plain,(
% 2.84/0.75    ~sP5(sK15,k15_lattice3(sK15,sK17)) | sP10(sK16,sK15,k15_lattice3(sK15,sK17)) | sK19(k15_lattice3(sK15,sK17),sK15,sK16) = sK23(sK17,sK15,sK19(k15_lattice3(sK15,sK17),sK15,sK16)) | ~spl25_5),
% 2.84/0.75    inference(resolution,[],[f1492,f729])).
% 2.84/0.75  fof(f1492,plain,(
% 2.84/0.75    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK15)) | ~sP5(sK15,X0) | sP10(sK16,sK15,X0) | sK19(X0,sK15,sK16) = sK23(sK17,sK15,sK19(X0,sK15,sK16))) )),
% 2.84/0.75    inference(resolution,[],[f1491,f167])).
% 2.84/0.75  fof(f1491,plain,(
% 2.84/0.75    ( ! [X2] : (r4_lattice3(sK15,X2,sK16) | sK19(X2,sK15,sK16) = sK23(sK17,sK15,sK19(X2,sK15,sK16)) | ~sP5(sK15,X2)) )),
% 2.84/0.75    inference(resolution,[],[f1489,f128])).
% 2.84/0.75  fof(f1489,plain,(
% 2.84/0.75    ( ! [X0] : (sP4(X0,sK15,sK16) | sK19(X0,sK15,sK16) = sK23(sK17,sK15,sK19(X0,sK15,sK16))) )),
% 2.84/0.75    inference(duplicate_literal_removal,[],[f1488])).
% 2.84/0.75  fof(f1488,plain,(
% 2.84/0.75    ( ! [X0] : (sP4(X0,sK15,sK16) | sK19(X0,sK15,sK16) = sK23(sK17,sK15,sK19(X0,sK15,sK16)) | sP4(X0,sK15,sK16)) )),
% 2.84/0.75    inference(resolution,[],[f566,f131])).
% 2.84/0.75  fof(f566,plain,(
% 2.84/0.75    ( ! [X0,X1] : (~r2_hidden(sK19(X0,sK15,X1),sK16) | sP4(X0,sK15,X1) | sK19(X0,sK15,X1) = sK23(sK17,sK15,sK19(X0,sK15,X1))) )),
% 2.84/0.75    inference(resolution,[],[f551,f159])).
% 2.84/0.75  fof(f159,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (~sP12(X0,X1,X2) | sK23(X0,X1,X2) = X2) )),
% 2.84/0.75    inference(cnf_transformation,[],[f100])).
% 2.84/0.75  fof(f763,plain,(
% 2.84/0.75    spl25_7),
% 2.84/0.75    inference(avatar_contradiction_clause,[],[f762])).
% 2.84/0.75  fof(f762,plain,(
% 2.84/0.75    $false | spl25_7),
% 2.84/0.75    inference(subsumption_resolution,[],[f761,f104])).
% 2.84/0.75  fof(f761,plain,(
% 2.84/0.75    v2_struct_0(sK15) | spl25_7),
% 2.84/0.75    inference(subsumption_resolution,[],[f760,f105])).
% 2.84/0.75  fof(f760,plain,(
% 2.84/0.75    ~v10_lattices(sK15) | v2_struct_0(sK15) | spl25_7),
% 2.84/0.75    inference(subsumption_resolution,[],[f759,f106])).
% 2.84/0.75  fof(f759,plain,(
% 2.84/0.75    ~v4_lattice3(sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15) | spl25_7),
% 2.84/0.75    inference(subsumption_resolution,[],[f758,f107])).
% 2.84/0.75  fof(f758,plain,(
% 2.84/0.75    ~l3_lattices(sK15) | ~v4_lattice3(sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15) | spl25_7),
% 2.84/0.75    inference(resolution,[],[f752,f155])).
% 2.84/0.75  fof(f155,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (sP11(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f55])).
% 2.84/0.75  fof(f55,plain,(
% 2.84/0.75    ! [X0,X1,X2] : (sP11(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 2.84/0.75    inference(definition_folding,[],[f35,f54,f53])).
% 2.84/0.75  fof(f54,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> sP10(X2,X1,X0)) | ~sP11(X0,X1,X2))),
% 2.84/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP11])])).
% 2.84/0.75  fof(f35,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 2.84/0.75    inference(flattening,[],[f34])).
% 2.84/0.75  fof(f34,plain,(
% 2.84/0.75    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 2.84/0.75    inference(ennf_transformation,[],[f4])).
% 2.84/0.75  fof(f4,axiom,(
% 2.84/0.75    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 2.84/0.75  fof(f752,plain,(
% 2.84/0.75    ~sP11(k15_lattice3(sK15,sK17),sK15,sK16) | spl25_7),
% 2.84/0.75    inference(avatar_component_clause,[],[f750])).
% 2.84/0.75  fof(f750,plain,(
% 2.84/0.75    spl25_7 <=> sP11(k15_lattice3(sK15,sK17),sK15,sK16)),
% 2.84/0.75    introduced(avatar_definition,[new_symbols(naming,[spl25_7])])).
% 2.84/0.75  fof(f757,plain,(
% 2.84/0.75    ~spl25_7 | ~spl25_8 | spl25_6),
% 2.84/0.75    inference(avatar_split_clause,[],[f748,f732,f754,f750])).
% 2.84/0.75  fof(f732,plain,(
% 2.84/0.75    spl25_6 <=> r2_hidden(k15_lattice3(sK15,sK17),a_2_2_lattice3(sK15,sK16))),
% 2.84/0.75    introduced(avatar_definition,[new_symbols(naming,[spl25_6])])).
% 2.84/0.75  fof(f748,plain,(
% 2.84/0.75    ~sP10(sK16,sK15,k15_lattice3(sK15,sK17)) | ~sP11(k15_lattice3(sK15,sK17),sK15,sK16) | spl25_6),
% 2.84/0.75    inference(resolution,[],[f734,f150])).
% 2.84/0.75  fof(f150,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~sP10(X2,X1,X0) | ~sP11(X0,X1,X2)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f90])).
% 2.84/0.75  fof(f90,plain,(
% 2.84/0.75    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~sP10(X2,X1,X0)) & (sP10(X2,X1,X0) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~sP11(X0,X1,X2))),
% 2.84/0.75    inference(nnf_transformation,[],[f54])).
% 2.84/0.75  fof(f734,plain,(
% 2.84/0.75    ~r2_hidden(k15_lattice3(sK15,sK17),a_2_2_lattice3(sK15,sK16)) | spl25_6),
% 2.84/0.75    inference(avatar_component_clause,[],[f732])).
% 2.84/0.75  fof(f739,plain,(
% 2.84/0.75    spl25_5),
% 2.84/0.75    inference(avatar_contradiction_clause,[],[f738])).
% 2.84/0.75  fof(f738,plain,(
% 2.84/0.75    $false | spl25_5),
% 2.84/0.75    inference(subsumption_resolution,[],[f737,f104])).
% 2.84/0.75  fof(f737,plain,(
% 2.84/0.75    v2_struct_0(sK15) | spl25_5),
% 2.84/0.75    inference(subsumption_resolution,[],[f736,f107])).
% 2.84/0.75  fof(f736,plain,(
% 2.84/0.75    ~l3_lattices(sK15) | v2_struct_0(sK15) | spl25_5),
% 2.84/0.75    inference(resolution,[],[f730,f141])).
% 2.84/0.75  fof(f730,plain,(
% 2.84/0.75    ~m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15)) | spl25_5),
% 2.84/0.75    inference(avatar_component_clause,[],[f728])).
% 2.84/0.75  fof(f735,plain,(
% 2.84/0.75    ~spl25_5 | ~spl25_6),
% 2.84/0.75    inference(avatar_split_clause,[],[f720,f732,f728])).
% 2.84/0.75  fof(f720,plain,(
% 2.84/0.75    ~r2_hidden(k15_lattice3(sK15,sK17),a_2_2_lattice3(sK15,sK16)) | ~m1_subset_1(k15_lattice3(sK15,sK17),u1_struct_0(sK15))),
% 2.84/0.75    inference(resolution,[],[f662,f109])).
% 2.84/0.75  fof(f109,plain,(
% 2.84/0.75    ~r3_lattices(sK15,k15_lattice3(sK15,sK16),k15_lattice3(sK15,sK17))),
% 2.84/0.75    inference(cnf_transformation,[],[f65])).
% 2.84/0.75  fof(f662,plain,(
% 2.84/0.75    ( ! [X0,X1] : (r3_lattices(sK15,k15_lattice3(sK15,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK15,X0)) | ~m1_subset_1(X1,u1_struct_0(sK15))) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f661,f104])).
% 2.84/0.75  fof(f661,plain,(
% 2.84/0.75    ( ! [X0,X1] : (r3_lattices(sK15,k15_lattice3(sK15,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK15,X0)) | ~m1_subset_1(X1,u1_struct_0(sK15)) | v2_struct_0(sK15)) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f660,f105])).
% 2.84/0.75  fof(f660,plain,(
% 2.84/0.75    ( ! [X0,X1] : (r3_lattices(sK15,k15_lattice3(sK15,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK15,X0)) | ~m1_subset_1(X1,u1_struct_0(sK15)) | ~v10_lattices(sK15) | v2_struct_0(sK15)) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f659,f106])).
% 2.84/0.75  fof(f659,plain,(
% 2.84/0.75    ( ! [X0,X1] : (r3_lattices(sK15,k15_lattice3(sK15,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK15,X0)) | ~m1_subset_1(X1,u1_struct_0(sK15)) | ~v4_lattice3(sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15)) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f655,f107])).
% 2.84/0.75  fof(f655,plain,(
% 2.84/0.75    ( ! [X0,X1] : (r3_lattices(sK15,k15_lattice3(sK15,X0),X1) | ~r2_hidden(X1,a_2_2_lattice3(sK15,X0)) | ~m1_subset_1(X1,u1_struct_0(sK15)) | ~l3_lattices(sK15) | ~v4_lattice3(sK15) | ~v10_lattices(sK15) | v2_struct_0(sK15)) )),
% 2.84/0.75    inference(superposition,[],[f116,f278])).
% 2.84/0.75  fof(f278,plain,(
% 2.84/0.75    ( ! [X0] : (k15_lattice3(sK15,X0) = k16_lattice3(sK15,a_2_2_lattice3(sK15,X0))) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f277,f104])).
% 2.84/0.75  fof(f277,plain,(
% 2.84/0.75    ( ! [X0] : (k15_lattice3(sK15,X0) = k16_lattice3(sK15,a_2_2_lattice3(sK15,X0)) | v2_struct_0(sK15)) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f276,f105])).
% 2.84/0.75  fof(f276,plain,(
% 2.84/0.75    ( ! [X0] : (k15_lattice3(sK15,X0) = k16_lattice3(sK15,a_2_2_lattice3(sK15,X0)) | ~v10_lattices(sK15) | v2_struct_0(sK15)) )),
% 2.84/0.75    inference(subsumption_resolution,[],[f275,f107])).
% 2.84/0.75  fof(f275,plain,(
% 2.84/0.75    ( ! [X0] : (~l3_lattices(sK15) | k15_lattice3(sK15,X0) = k16_lattice3(sK15,a_2_2_lattice3(sK15,X0)) | ~v10_lattices(sK15) | v2_struct_0(sK15)) )),
% 2.84/0.75    inference(resolution,[],[f110,f106])).
% 2.84/0.75  fof(f110,plain,(
% 2.84/0.75    ( ! [X0,X1] : (~v4_lattice3(X0) | ~l3_lattices(X0) | k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f17])).
% 2.84/0.75  fof(f17,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.84/0.75    inference(flattening,[],[f16])).
% 2.84/0.75  fof(f16,plain,(
% 2.84/0.75    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.84/0.75    inference(ennf_transformation,[],[f8])).
% 2.84/0.75  fof(f8,axiom,(
% 2.84/0.75    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).
% 2.84/0.75  fof(f116,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (r3_lattices(X0,k16_lattice3(X0,X2),X1) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f23])).
% 2.84/0.75  % SZS output end Proof for theBenchmark
% 2.84/0.75  % (8346)------------------------------
% 2.84/0.75  % (8346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.84/0.75  % (8346)Termination reason: Refutation
% 2.84/0.75  
% 2.84/0.75  % (8346)Memory used [KB]: 14200
% 2.84/0.75  % (8346)Time elapsed: 0.359 s
% 2.84/0.75  % (8346)------------------------------
% 2.84/0.75  % (8346)------------------------------
% 2.84/0.75  % (8315)Success in time 0.419 s
%------------------------------------------------------------------------------
