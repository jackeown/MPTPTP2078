%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:53 EST 2020

% Result     : Theorem 2.10s
% Output     : Refutation 2.29s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 582 expanded)
%              Number of leaves         :   32 ( 204 expanded)
%              Depth                    :   30
%              Number of atoms          : 1183 (4836 expanded)
%              Number of equality atoms :   64 ( 427 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f886,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f286,f295,f307,f317,f325,f351,f885])).

fof(f885,plain,
    ( ~ spl18_2
    | ~ spl18_6
    | ~ spl18_7 ),
    inference(avatar_contradiction_clause,[],[f884])).

fof(f884,plain,
    ( $false
    | ~ spl18_2
    | ~ spl18_6
    | ~ spl18_7 ),
    inference(subsumption_resolution,[],[f883,f344])).

fof(f344,plain,
    ( sP1(k4_filter_0(sK11,sK12,sK13),sK11,sK13,sK12)
    | ~ spl18_7 ),
    inference(avatar_component_clause,[],[f343])).

fof(f343,plain,
    ( spl18_7
  <=> sP1(k4_filter_0(sK11,sK12,sK13),sK11,sK13,sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_7])])).

fof(f883,plain,
    ( ~ sP1(k4_filter_0(sK11,sK12,sK13),sK11,sK13,sK12)
    | ~ spl18_2
    | ~ spl18_6 ),
    inference(subsumption_resolution,[],[f872,f305])).

fof(f305,plain,
    ( m1_subset_1(k4_filter_0(sK11,sK12,sK13),u1_struct_0(sK11))
    | ~ spl18_6 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl18_6
  <=> m1_subset_1(k4_filter_0(sK11,sK12,sK13),u1_struct_0(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).

fof(f872,plain,
    ( ~ m1_subset_1(k4_filter_0(sK11,sK12,sK13),u1_struct_0(sK11))
    | ~ sP1(k4_filter_0(sK11,sK12,sK13),sK11,sK13,sK12)
    | ~ spl18_2 ),
    inference(trivial_inequality_removal,[],[f871])).

fof(f871,plain,
    ( ~ m1_subset_1(k4_filter_0(sK11,sK12,sK13),u1_struct_0(sK11))
    | ~ sP1(k4_filter_0(sK11,sK12,sK13),sK11,sK13,sK12)
    | k4_filter_0(sK11,sK12,sK13) != k4_filter_0(sK11,sK12,sK13)
    | ~ spl18_2 ),
    inference(resolution,[],[f866,f269])).

fof(f269,plain,
    ( r2_hidden(k4_filter_0(sK11,sK12,sK13),a_3_6_lattice3(sK11,sK12,sK13))
    | ~ spl18_2 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl18_2
  <=> r2_hidden(k4_filter_0(sK11,sK12,sK13),a_3_6_lattice3(sK11,sK12,sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).

fof(f866,plain,(
    ! [X34] :
      ( ~ r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13))
      | ~ m1_subset_1(X34,u1_struct_0(sK11))
      | ~ sP1(X34,sK11,sK13,sK12)
      | k4_filter_0(sK11,sK12,sK13) != X34 ) ),
    inference(subsumption_resolution,[],[f865,f80])).

fof(f80,plain,(
    m1_subset_1(sK12,u1_struct_0(sK11)) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( k4_filter_0(sK11,sK12,sK13) != k15_lattice3(sK11,a_3_6_lattice3(sK11,sK12,sK13))
    & l3_lattices(sK11)
    & v3_filter_0(sK11)
    & v10_lattices(sK11)
    & ~ v2_struct_0(sK11)
    & m1_subset_1(sK13,u1_struct_0(sK11))
    & m1_subset_1(sK12,u1_struct_0(sK11))
    & l3_lattices(sK11)
    & v4_lattice3(sK11)
    & v10_lattices(sK11)
    & ~ v2_struct_0(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f11,f44,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))
                & l3_lattices(X0)
                & v3_filter_0(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0)
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k4_filter_0(sK11,X1,X2) != k15_lattice3(sK11,a_3_6_lattice3(sK11,X1,X2))
              & l3_lattices(sK11)
              & v3_filter_0(sK11)
              & v10_lattices(sK11)
              & ~ v2_struct_0(sK11)
              & m1_subset_1(X2,u1_struct_0(sK11)) )
          & m1_subset_1(X1,u1_struct_0(sK11)) )
      & l3_lattices(sK11)
      & v4_lattice3(sK11)
      & v10_lattices(sK11)
      & ~ v2_struct_0(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k4_filter_0(sK11,X1,X2) != k15_lattice3(sK11,a_3_6_lattice3(sK11,X1,X2))
            & l3_lattices(sK11)
            & v3_filter_0(sK11)
            & v10_lattices(sK11)
            & ~ v2_struct_0(sK11)
            & m1_subset_1(X2,u1_struct_0(sK11)) )
        & m1_subset_1(X1,u1_struct_0(sK11)) )
   => ( ? [X2] :
          ( k4_filter_0(sK11,sK12,X2) != k15_lattice3(sK11,a_3_6_lattice3(sK11,sK12,X2))
          & l3_lattices(sK11)
          & v3_filter_0(sK11)
          & v10_lattices(sK11)
          & ~ v2_struct_0(sK11)
          & m1_subset_1(X2,u1_struct_0(sK11)) )
      & m1_subset_1(sK12,u1_struct_0(sK11)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( k4_filter_0(sK11,sK12,X2) != k15_lattice3(sK11,a_3_6_lattice3(sK11,sK12,X2))
        & l3_lattices(sK11)
        & v3_filter_0(sK11)
        & v10_lattices(sK11)
        & ~ v2_struct_0(sK11)
        & m1_subset_1(X2,u1_struct_0(sK11)) )
   => ( k4_filter_0(sK11,sK12,sK13) != k15_lattice3(sK11,a_3_6_lattice3(sK11,sK12,sK13))
      & l3_lattices(sK11)
      & v3_filter_0(sK11)
      & v10_lattices(sK11)
      & ~ v2_struct_0(sK11)
      & m1_subset_1(sK13,u1_struct_0(sK11)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))
              & l3_lattices(X0)
              & v3_filter_0(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
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
              ( k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))
              & l3_lattices(X0)
              & v3_filter_0(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0)
              & m1_subset_1(X2,u1_struct_0(X0)) )
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
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( ( l3_lattices(X0)
                    & v3_filter_0(X0)
                    & v10_lattices(X0)
                    & ~ v2_struct_0(X0) )
                 => k4_filter_0(X0,X1,X2) = k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) ) ) ) ) ),
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
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( l3_lattices(X0)
                  & v3_filter_0(X0)
                  & v10_lattices(X0)
                  & ~ v2_struct_0(X0) )
               => k4_filter_0(X0,X1,X2) = k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_lattice3)).

fof(f865,plain,(
    ! [X34] :
      ( ~ sP1(X34,sK11,sK13,sK12)
      | ~ m1_subset_1(X34,u1_struct_0(sK11))
      | ~ m1_subset_1(sK12,u1_struct_0(sK11))
      | ~ r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13))
      | k4_filter_0(sK11,sK12,sK13) != X34 ) ),
    inference(subsumption_resolution,[],[f864,f81])).

fof(f81,plain,(
    m1_subset_1(sK13,u1_struct_0(sK11)) ),
    inference(cnf_transformation,[],[f45])).

fof(f864,plain,(
    ! [X34] :
      ( ~ sP1(X34,sK11,sK13,sK12)
      | ~ m1_subset_1(sK13,u1_struct_0(sK11))
      | ~ m1_subset_1(X34,u1_struct_0(sK11))
      | ~ m1_subset_1(sK12,u1_struct_0(sK11))
      | ~ r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13))
      | k4_filter_0(sK11,sK12,sK13) != X34 ) ),
    inference(subsumption_resolution,[],[f863,f76])).

fof(f76,plain,(
    ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f45])).

fof(f863,plain,(
    ! [X34] :
      ( v2_struct_0(sK11)
      | ~ sP1(X34,sK11,sK13,sK12)
      | ~ m1_subset_1(sK13,u1_struct_0(sK11))
      | ~ m1_subset_1(X34,u1_struct_0(sK11))
      | ~ m1_subset_1(sK12,u1_struct_0(sK11))
      | ~ r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13))
      | k4_filter_0(sK11,sK12,sK13) != X34 ) ),
    inference(subsumption_resolution,[],[f862,f77])).

fof(f77,plain,(
    v10_lattices(sK11) ),
    inference(cnf_transformation,[],[f45])).

fof(f862,plain,(
    ! [X34] :
      ( ~ v10_lattices(sK11)
      | v2_struct_0(sK11)
      | ~ sP1(X34,sK11,sK13,sK12)
      | ~ m1_subset_1(sK13,u1_struct_0(sK11))
      | ~ m1_subset_1(X34,u1_struct_0(sK11))
      | ~ m1_subset_1(sK12,u1_struct_0(sK11))
      | ~ r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13))
      | k4_filter_0(sK11,sK12,sK13) != X34 ) ),
    inference(subsumption_resolution,[],[f861,f78])).

fof(f78,plain,(
    v4_lattice3(sK11) ),
    inference(cnf_transformation,[],[f45])).

fof(f861,plain,(
    ! [X34] :
      ( ~ v4_lattice3(sK11)
      | ~ v10_lattices(sK11)
      | v2_struct_0(sK11)
      | ~ sP1(X34,sK11,sK13,sK12)
      | ~ m1_subset_1(sK13,u1_struct_0(sK11))
      | ~ m1_subset_1(X34,u1_struct_0(sK11))
      | ~ m1_subset_1(sK12,u1_struct_0(sK11))
      | ~ r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13))
      | k4_filter_0(sK11,sK12,sK13) != X34 ) ),
    inference(subsumption_resolution,[],[f851,f79])).

fof(f79,plain,(
    l3_lattices(sK11) ),
    inference(cnf_transformation,[],[f45])).

fof(f851,plain,(
    ! [X34] :
      ( ~ l3_lattices(sK11)
      | ~ v4_lattice3(sK11)
      | ~ v10_lattices(sK11)
      | v2_struct_0(sK11)
      | ~ sP1(X34,sK11,sK13,sK12)
      | ~ m1_subset_1(sK13,u1_struct_0(sK11))
      | ~ m1_subset_1(X34,u1_struct_0(sK11))
      | ~ m1_subset_1(sK12,u1_struct_0(sK11))
      | ~ r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13))
      | k4_filter_0(sK11,sK12,sK13) != X34 ) ),
    inference(duplicate_literal_removal,[],[f850])).

fof(f850,plain,(
    ! [X34] :
      ( ~ l3_lattices(sK11)
      | ~ v4_lattice3(sK11)
      | ~ v10_lattices(sK11)
      | v2_struct_0(sK11)
      | ~ sP1(X34,sK11,sK13,sK12)
      | ~ m1_subset_1(sK13,u1_struct_0(sK11))
      | ~ m1_subset_1(X34,u1_struct_0(sK11))
      | ~ m1_subset_1(sK12,u1_struct_0(sK11))
      | ~ r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13))
      | k4_filter_0(sK11,sK12,sK13) != X34
      | ~ m1_subset_1(X34,u1_struct_0(sK11)) ) ),
    inference(resolution,[],[f827,f258])).

fof(f258,plain,(
    ! [X4] :
      ( ~ r4_lattice3(sK11,X4,a_3_6_lattice3(sK11,sK12,sK13))
      | ~ r2_hidden(X4,a_3_6_lattice3(sK11,sK12,sK13))
      | k4_filter_0(sK11,sK12,sK13) != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK11)) ) ),
    inference(subsumption_resolution,[],[f257,f76])).

fof(f257,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK11))
      | ~ r2_hidden(X4,a_3_6_lattice3(sK11,sK12,sK13))
      | v2_struct_0(sK11)
      | k4_filter_0(sK11,sK12,sK13) != X4
      | ~ r4_lattice3(sK11,X4,a_3_6_lattice3(sK11,sK12,sK13)) ) ),
    inference(subsumption_resolution,[],[f256,f79])).

fof(f256,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK11))
      | ~ r2_hidden(X4,a_3_6_lattice3(sK11,sK12,sK13))
      | ~ l3_lattices(sK11)
      | v2_struct_0(sK11)
      | k4_filter_0(sK11,sK12,sK13) != X4
      | ~ r4_lattice3(sK11,X4,a_3_6_lattice3(sK11,sK12,sK13)) ) ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK11))
      | ~ r2_hidden(X4,a_3_6_lattice3(sK11,sK12,sK13))
      | ~ l3_lattices(sK11)
      | v2_struct_0(sK11)
      | k4_filter_0(sK11,sK12,sK13) != X4
      | ~ m1_subset_1(X4,u1_struct_0(sK11))
      | ~ r4_lattice3(sK11,X4,a_3_6_lattice3(sK11,sK12,sK13)) ) ),
    inference(resolution,[],[f253,f190])).

fof(f190,plain,(
    ! [X0] :
      ( ~ sP4(X0,sK11,a_3_6_lattice3(sK11,sK12,sK13))
      | k4_filter_0(sK11,sK12,sK13) != X0
      | ~ m1_subset_1(X0,u1_struct_0(sK11))
      | ~ r4_lattice3(sK11,X0,a_3_6_lattice3(sK11,sK12,sK13)) ) ),
    inference(resolution,[],[f189,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( sP5(X0,X1,X2)
      | ~ sP4(X2,X1,X0)
      | ~ r4_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ~ sP4(X2,X1,X0)
        | ~ r4_lattice3(X1,X2,X0) )
      & ( ( sP4(X2,X1,X0)
          & r4_lattice3(X1,X2,X0) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X1,X0,X2] :
      ( ( sP5(X1,X0,X2)
        | ~ sP4(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP4(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP5(X1,X0,X2) ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X1,X0,X2] :
      ( ( sP5(X1,X0,X2)
        | ~ sP4(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP4(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP5(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( sP5(X1,X0,X2)
    <=> ( sP4(X2,X0,X1)
        & r4_lattice3(X0,X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f189,plain,(
    ! [X2] :
      ( ~ sP5(a_3_6_lattice3(sK11,sK12,sK13),sK11,X2)
      | ~ m1_subset_1(X2,u1_struct_0(sK11))
      | k4_filter_0(sK11,sK12,sK13) != X2 ) ),
    inference(subsumption_resolution,[],[f188,f76])).

fof(f188,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK11))
      | v2_struct_0(sK11)
      | ~ sP5(a_3_6_lattice3(sK11,sK12,sK13),sK11,X2)
      | k4_filter_0(sK11,sK12,sK13) != X2 ) ),
    inference(subsumption_resolution,[],[f187,f77])).

fof(f187,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK11))
      | ~ v10_lattices(sK11)
      | v2_struct_0(sK11)
      | ~ sP5(a_3_6_lattice3(sK11,sK12,sK13),sK11,X2)
      | k4_filter_0(sK11,sK12,sK13) != X2 ) ),
    inference(subsumption_resolution,[],[f186,f78])).

fof(f186,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK11))
      | ~ v4_lattice3(sK11)
      | ~ v10_lattices(sK11)
      | v2_struct_0(sK11)
      | ~ sP5(a_3_6_lattice3(sK11,sK12,sK13),sK11,X2)
      | k4_filter_0(sK11,sK12,sK13) != X2 ) ),
    inference(subsumption_resolution,[],[f185,f79])).

fof(f185,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK11))
      | ~ l3_lattices(sK11)
      | ~ v4_lattice3(sK11)
      | ~ v10_lattices(sK11)
      | v2_struct_0(sK11)
      | ~ sP5(a_3_6_lattice3(sK11,sK12,sK13),sK11,X2)
      | k4_filter_0(sK11,sK12,sK13) != X2 ) ),
    inference(resolution,[],[f135,f158])).

fof(f158,plain,(
    ! [X0] :
      ( ~ sP6(X0,sK11,a_3_6_lattice3(sK11,sK12,sK13))
      | ~ sP5(a_3_6_lattice3(sK11,sK12,sK13),sK11,X0)
      | k4_filter_0(sK11,sK12,sK13) != X0 ) ),
    inference(superposition,[],[f86,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X1,X2) = X0
      | ~ sP5(X2,X1,X0)
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( ( k15_lattice3(X1,X2) = X0
          | ~ sP5(X2,X1,X0) )
        & ( sP5(X2,X1,X0)
          | k15_lattice3(X1,X2) != X0 ) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f56])).

fof(f56,plain,(
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

fof(f86,plain,(
    k4_filter_0(sK11,sK12,sK13) != k15_lattice3(sK11,a_3_6_lattice3(sK11,sK12,sK13)) ),
    inference(cnf_transformation,[],[f45])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f114])).

fof(f114,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f253,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f252])).

fof(f252,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | sP4(X0,X2,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP4(X0,X2,X1) ) ),
    inference(resolution,[],[f250,f148])).

fof(f148,plain,(
    ! [X2,X0,X1] :
      ( sP8(X0,sK15(X1,X0,X2))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | sP4(X1,X0,X2) ) ),
    inference(resolution,[],[f121,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))
      | sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK15(X0,X1,X2))
          & r4_lattice3(X1,sK15(X0,X1,X2),X2)
          & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f62,f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r4_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK15(X0,X1,X2))
        & r4_lattice3(X1,sK15(X0,X1,X2),X2)
        & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
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
    inference(rectify,[],[f61])).

fof(f61,plain,(
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

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP8(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP8(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f37,f36])).

fof(f36,plain,(
    ! [X1,X0,X2] :
      ( sP7(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP7(X1,X0,X2) )
      | ~ sP8(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f250,plain,(
    ! [X2,X0,X1] :
      ( ~ sP8(X1,sK15(X0,X1,X2))
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | sP4(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f248])).

fof(f248,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ sP8(X1,sK15(X0,X1,X2))
      | sP4(X0,X1,X2)
      | sP4(X0,X1,X2) ) ),
    inference(resolution,[],[f213,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK15(X0,X1,X2))
      | sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f213,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X1,X0,sK15(X2,X1,X3))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X3)
      | ~ sP8(X1,sK15(X2,X1,X3))
      | sP4(X2,X1,X3) ) ),
    inference(resolution,[],[f164,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK15(X0,X1,X2),X2)
      | sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f164,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_lattice3(X2,X3,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | r1_lattices(X2,X0,X3)
      | ~ r2_hidden(X0,X1)
      | ~ sP8(X2,X3) ) ),
    inference(resolution,[],[f117,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( sP7(X1,X0,X2)
      | ~ r4_lattice3(X0,X1,X2)
      | ~ sP8(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP7(X1,X0,X2) )
          & ( sP7(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP8(X0,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f117,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK16(X0,X1,X2),X0)
          & r2_hidden(sK16(X0,X1,X2),X2)
          & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK16(X0,X1,X2),X0)
        & r2_hidden(sK16(X0,X1,X2),X2)
        & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X1,X0,X2] :
      ( ( sP7(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X3,X1)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X3,X1)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP7(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f827,plain,(
    ! [X6,X8,X7,X5] :
      ( r4_lattice3(X6,X7,a_3_6_lattice3(X6,X5,X8))
      | ~ l3_lattices(X6)
      | ~ v4_lattice3(X6)
      | ~ v10_lattices(X6)
      | v2_struct_0(X6)
      | ~ sP1(X7,X6,X8,X5)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(X5,u1_struct_0(X6)) ) ),
    inference(subsumption_resolution,[],[f826,f121])).

fof(f826,plain,(
    ! [X6,X8,X7,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(X6))
      | ~ l3_lattices(X6)
      | ~ v4_lattice3(X6)
      | ~ v10_lattices(X6)
      | v2_struct_0(X6)
      | ~ sP1(X7,X6,X8,X5)
      | ~ m1_subset_1(X8,u1_struct_0(X6))
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | r4_lattice3(X6,X7,a_3_6_lattice3(X6,X5,X8))
      | ~ sP8(X6,X7) ) ),
    inference(resolution,[],[f769,f116])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP8(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f769,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X3,X1,a_3_6_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP1(X3,X1,X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f768,f140])).

fof(f140,plain,(
    ! [X3] :
      ( v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3) ) ),
    inference(resolution,[],[f94,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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

fof(f94,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f768,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP1(X3,X1,X0,X2)
      | sP7(X3,X1,a_3_6_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v6_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f767,f142])).

fof(f142,plain,(
    ! [X5] :
      ( v8_lattices(X5)
      | v2_struct_0(X5)
      | ~ l3_lattices(X5)
      | ~ v10_lattices(X5) ) ),
    inference(resolution,[],[f94,f92])).

fof(f92,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f767,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP1(X3,X1,X0,X2)
      | sP7(X3,X1,a_3_6_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f766,f143])).

fof(f143,plain,(
    ! [X6] :
      ( v9_lattices(X6)
      | v2_struct_0(X6)
      | ~ l3_lattices(X6)
      | ~ v10_lattices(X6) ) ),
    inference(resolution,[],[f94,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f766,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP1(X3,X1,X0,X2)
      | sP7(X3,X1,a_3_6_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f763])).

fof(f763,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP1(X3,X1,X0,X2)
      | sP7(X3,X1,a_3_6_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | sP7(X3,X1,a_3_6_lattice3(X1,X2,X0)) ) ),
    inference(resolution,[],[f493,f275])).

fof(f275,plain,(
    ! [X4,X5,X3] :
      ( ~ r3_lattices(X3,sK16(X4,X3,X5),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ v8_lattices(X3)
      | ~ v6_lattices(X3)
      | v2_struct_0(X3)
      | sP7(X4,X3,X5) ) ),
    inference(subsumption_resolution,[],[f273,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f273,plain,(
    ! [X4,X5,X3] :
      ( ~ r3_lattices(X3,sK16(X4,X3,X5),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ m1_subset_1(sK16(X4,X3,X5),u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ v8_lattices(X3)
      | ~ v6_lattices(X3)
      | v2_struct_0(X3)
      | sP7(X4,X3,X5) ) ),
    inference(resolution,[],[f122,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK16(X0,X1,X2),X0)
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f493,plain,(
    ! [X6,X10,X8,X7,X5,X9] :
      ( r3_lattices(X7,sK16(X5,X6,a_3_6_lattice3(X7,X8,X9)),X10)
      | ~ m1_subset_1(X9,u1_struct_0(X7))
      | ~ m1_subset_1(X8,u1_struct_0(X7))
      | ~ l3_lattices(X7)
      | ~ v4_lattice3(X7)
      | ~ v10_lattices(X7)
      | v2_struct_0(X7)
      | ~ sP1(X10,X7,X9,X8)
      | sP7(X5,X6,a_3_6_lattice3(X7,X8,X9)) ) ),
    inference(resolution,[],[f408,f204])).

fof(f204,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP9(X3,X4,X0,X1)
      | ~ sP1(X2,X0,X3,X4)
      | r3_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f200,f163])).

fof(f163,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP9(X0,X1,X2,X3)
      | m1_subset_1(X3,u1_struct_0(X2)) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,u1_struct_0(X2))
      | ~ sP9(X0,X1,X2,X3)
      | ~ sP9(X0,X1,X2,X3) ) ),
    inference(superposition,[],[f127,f128])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( sK17(X0,X1,X2,X3) = X3
      | ~ sP9(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP9(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r3_lattices(X2,k4_lattices(X2,X1,X4),X0)
            | X3 != X4
            | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
      & ( ( r3_lattices(X2,k4_lattices(X2,X1,sK17(X0,X1,X2,X3)),X0)
          & sK17(X0,X1,X2,X3) = X3
          & m1_subset_1(sK17(X0,X1,X2,X3),u1_struct_0(X2)) )
        | ~ sP9(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f73,f74])).

fof(f74,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r3_lattices(X2,k4_lattices(X2,X1,X5),X0)
          & X3 = X5
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( r3_lattices(X2,k4_lattices(X2,X1,sK17(X0,X1,X2,X3)),X0)
        & sK17(X0,X1,X2,X3) = X3
        & m1_subset_1(sK17(X0,X1,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP9(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r3_lattices(X2,k4_lattices(X2,X1,X4),X0)
            | X3 != X4
            | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
      & ( ? [X5] :
            ( r3_lattices(X2,k4_lattices(X2,X1,X5),X0)
            & X3 = X5
            & m1_subset_1(X5,u1_struct_0(X2)) )
        | ~ sP9(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f72])).

fof(f72,plain,(
    ! [X3,X2,X1,X0] :
      ( ( sP9(X3,X2,X1,X0)
        | ! [X4] :
            ( ~ r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
            | X0 != X4
            | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP9(X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X3,X2,X1,X0] :
      ( sP9(X3,X2,X1,X0)
    <=> ? [X4] :
          ( r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f127,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK17(X0,X1,X2,X3),u1_struct_0(X2))
      | ~ sP9(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f200,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ sP1(X2,X0,X3,X4)
      | ~ sP9(X3,X4,X0,X1) ) ),
    inference(resolution,[],[f100,f170])).

fof(f170,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X2,k4_lattices(X2,X1,X3),X0)
      | ~ sP9(X0,X1,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f169])).

fof(f169,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X2,k4_lattices(X2,X1,X3),X0)
      | ~ sP9(X0,X1,X2,X3)
      | ~ sP9(X0,X1,X2,X3) ) ),
    inference(superposition,[],[f129,f128])).

fof(f129,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X2,k4_lattices(X2,X1,sK17(X0,X1,X2,X3)),X0)
      | ~ sP9(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f100,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r3_lattices(X1,k4_lattices(X1,X3,X5),X2)
      | r3_lattices(X1,X5,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ~ r3_lattices(X1,sK14(X0,X1,X2,X3),X0)
          & r3_lattices(X1,k4_lattices(X1,X3,sK14(X0,X1,X2,X3)),X2)
          & m1_subset_1(sK14(X0,X1,X2,X3),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( r3_lattices(X1,X5,X0)
            | ~ r3_lattices(X1,k4_lattices(X1,X3,X5),X2)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f53,f54])).

fof(f54,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r3_lattices(X1,X4,X0)
          & r3_lattices(X1,k4_lattices(X1,X3,X4),X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r3_lattices(X1,sK14(X0,X1,X2,X3),X0)
        & r3_lattices(X1,k4_lattices(X1,X3,sK14(X0,X1,X2,X3)),X2)
        & m1_subset_1(sK14(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ~ r3_lattices(X1,X4,X0)
            & r3_lattices(X1,k4_lattices(X1,X3,X4),X2)
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( r3_lattices(X1,X5,X0)
            | ~ r3_lattices(X1,k4_lattices(X1,X3,X5),X2)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X3,X0,X2,X1] :
      ( ( sP1(X3,X0,X2,X1)
        | ? [X4] :
            ( ~ r3_lattices(X0,X4,X3)
            & r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
            & m1_subset_1(X4,u1_struct_0(X0)) ) )
      & ( ! [X4] :
            ( r3_lattices(X0,X4,X3)
            | ~ r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        | ~ sP1(X3,X0,X2,X1) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X3,X0,X2,X1] :
      ( sP1(X3,X0,X2,X1)
    <=> ! [X4] :
          ( r3_lattices(X0,X4,X3)
          | ~ r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
          | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f408,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP9(X0,X1,X2,sK16(X3,X4,a_3_6_lattice3(X2,X1,X0)))
      | sP7(X3,X4,a_3_6_lattice3(X2,X1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f166,f131])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( sP10(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( sP10(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f25,f40,f39])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      <=> sP9(X3,X2,X1,X0) )
      | ~ sP10(X0,X1,X2,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,u1_struct_0(X1))
        & m1_subset_1(X2,u1_struct_0(X1))
        & l3_lattices(X1)
        & v4_lattice3(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      <=> ? [X4] :
            ( r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_6_lattice3)).

fof(f166,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP10(sK16(X3,X4,a_3_6_lattice3(X2,X1,X0)),X2,X1,X0)
      | sP9(X0,X1,X2,sK16(X3,X4,a_3_6_lattice3(X2,X1,X0)))
      | sP7(X3,X4,a_3_6_lattice3(X2,X1,X0)) ) ),
    inference(resolution,[],[f125,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK16(X0,X1,X2),X2)
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f125,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      | sP9(X3,X2,X1,X0)
      | ~ sP10(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
          | ~ sP9(X3,X2,X1,X0) )
        & ( sP9(X3,X2,X1,X0)
          | ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) ) )
      | ~ sP10(X0,X1,X2,X3) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f351,plain,
    ( spl18_7
    | ~ spl18_5 ),
    inference(avatar_split_clause,[],[f348,f300,f343])).

fof(f300,plain,
    ( spl18_5
  <=> sP2(sK12,sK13,sK11,k4_filter_0(sK11,sK12,sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).

fof(f348,plain,
    ( sP1(k4_filter_0(sK11,sK12,sK13),sK11,sK13,sK12)
    | ~ spl18_5 ),
    inference(resolution,[],[f301,f98])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | sP1(X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ~ sP1(X3,X2,X1,X0)
        | ~ r3_lattices(X2,k4_lattices(X2,X0,X3),X1) )
      & ( ( sP1(X3,X2,X1,X0)
          & r3_lattices(X2,k4_lattices(X2,X0,X3),X1) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X1,X2,X0,X3] :
      ( ( sP2(X1,X2,X0,X3)
        | ~ sP1(X3,X0,X2,X1)
        | ~ r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
      & ( ( sP1(X3,X0,X2,X1)
          & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
        | ~ sP2(X1,X2,X0,X3) ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X1,X2,X0,X3] :
      ( ( sP2(X1,X2,X0,X3)
        | ~ sP1(X3,X0,X2,X1)
        | ~ r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
      & ( ( sP1(X3,X0,X2,X1)
          & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
        | ~ sP2(X1,X2,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X1,X2,X0,X3] :
      ( sP2(X1,X2,X0,X3)
    <=> ( sP1(X3,X0,X2,X1)
        & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f301,plain,
    ( sP2(sK12,sK13,sK11,k4_filter_0(sK11,sK12,sK13))
    | ~ spl18_5 ),
    inference(avatar_component_clause,[],[f300])).

fof(f325,plain,(
    spl18_6 ),
    inference(avatar_contradiction_clause,[],[f324])).

fof(f324,plain,
    ( $false
    | spl18_6 ),
    inference(subsumption_resolution,[],[f323,f76])).

fof(f323,plain,
    ( v2_struct_0(sK11)
    | spl18_6 ),
    inference(subsumption_resolution,[],[f322,f77])).

fof(f322,plain,
    ( ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl18_6 ),
    inference(subsumption_resolution,[],[f321,f79])).

fof(f321,plain,
    ( ~ l3_lattices(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl18_6 ),
    inference(subsumption_resolution,[],[f320,f80])).

fof(f320,plain,
    ( ~ m1_subset_1(sK12,u1_struct_0(sK11))
    | ~ l3_lattices(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl18_6 ),
    inference(subsumption_resolution,[],[f318,f81])).

fof(f318,plain,
    ( ~ m1_subset_1(sK13,u1_struct_0(sK11))
    | ~ m1_subset_1(sK12,u1_struct_0(sK11))
    | ~ l3_lattices(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl18_6 ),
    inference(resolution,[],[f306,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_filter_0)).

fof(f306,plain,
    ( ~ m1_subset_1(k4_filter_0(sK11,sK12,sK13),u1_struct_0(sK11))
    | spl18_6 ),
    inference(avatar_component_clause,[],[f304])).

fof(f317,plain,(
    spl18_5 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | spl18_5 ),
    inference(subsumption_resolution,[],[f315,f79])).

fof(f315,plain,
    ( ~ l3_lattices(sK11)
    | spl18_5 ),
    inference(subsumption_resolution,[],[f314,f80])).

fof(f314,plain,
    ( ~ m1_subset_1(sK12,u1_struct_0(sK11))
    | ~ l3_lattices(sK11)
    | spl18_5 ),
    inference(subsumption_resolution,[],[f313,f81])).

fof(f313,plain,
    ( ~ m1_subset_1(sK13,u1_struct_0(sK11))
    | ~ m1_subset_1(sK12,u1_struct_0(sK11))
    | ~ l3_lattices(sK11)
    | spl18_5 ),
    inference(subsumption_resolution,[],[f312,f76])).

fof(f312,plain,
    ( v2_struct_0(sK11)
    | ~ m1_subset_1(sK13,u1_struct_0(sK11))
    | ~ m1_subset_1(sK12,u1_struct_0(sK11))
    | ~ l3_lattices(sK11)
    | spl18_5 ),
    inference(subsumption_resolution,[],[f311,f77])).

fof(f311,plain,
    ( ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | ~ m1_subset_1(sK13,u1_struct_0(sK11))
    | ~ m1_subset_1(sK12,u1_struct_0(sK11))
    | ~ l3_lattices(sK11)
    | spl18_5 ),
    inference(subsumption_resolution,[],[f308,f84])).

fof(f84,plain,(
    v3_filter_0(sK11) ),
    inference(cnf_transformation,[],[f45])).

fof(f308,plain,
    ( ~ v3_filter_0(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | ~ m1_subset_1(sK13,u1_struct_0(sK11))
    | ~ m1_subset_1(sK12,u1_struct_0(sK11))
    | ~ l3_lattices(sK11)
    | spl18_5 ),
    inference(resolution,[],[f302,f243])).

fof(f243,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X2,X0,k4_filter_0(X0,X1,X2))
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f241,f124])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP2(X1,X2,X0,k4_filter_0(X0,X1,X2)) ) ),
    inference(resolution,[],[f136,f132])).

fof(f132,plain,(
    ! [X2,X3,X1] :
      ( ~ sP3(k4_filter_0(X1,X3,X2),X1,X2,X3)
      | sP2(X3,X2,X1,k4_filter_0(X1,X3,X2)) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X3,X2,X1,X0)
      | k4_filter_0(X1,X3,X2) != X0
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k4_filter_0(X1,X3,X2) = X0
          | ~ sP2(X3,X2,X1,X0) )
        & ( sP2(X3,X2,X1,X0)
          | k4_filter_0(X1,X3,X2) != X0 ) )
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f47])).

fof(f47,plain,(
    ! [X3,X0,X2,X1] :
      ( ( ( k4_filter_0(X0,X1,X2) = X3
          | ~ sP2(X1,X2,X0,X3) )
        & ( sP2(X1,X2,X0,X3)
          | k4_filter_0(X0,X1,X2) != X3 ) )
      | ~ sP3(X3,X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X3,X0,X2,X1] :
      ( ( k4_filter_0(X0,X1,X2) = X3
      <=> sP2(X1,X2,X0,X3) )
      | ~ sP3(X3,X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f136,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( sP3(X3,X0,X2,X1)
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l3_lattices(X0)
              | ~ v3_filter_0(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f30,f29,f28])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_filter_0(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r3_lattices(X0,X4,X3)
                          | ~ r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l3_lattices(X0)
              | ~ v3_filter_0(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k4_filter_0(X0,X1,X2) = X3
                  <=> ( ! [X4] :
                          ( r3_lattices(X0,X4,X3)
                          | ~ r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
                          | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                      & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ l3_lattices(X0)
              | ~ v3_filter_0(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( l3_lattices(X0)
                  & v3_filter_0(X0)
                  & v10_lattices(X0)
                  & ~ v2_struct_0(X0) )
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( k4_filter_0(X0,X1,X2) = X3
                    <=> ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X0))
                           => ( r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
                             => r3_lattices(X0,X4,X3) ) )
                        & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_filter_0)).

fof(f302,plain,
    ( ~ sP2(sK12,sK13,sK11,k4_filter_0(sK11,sK12,sK13))
    | spl18_5 ),
    inference(avatar_component_clause,[],[f300])).

fof(f307,plain,
    ( ~ spl18_5
    | ~ spl18_6
    | spl18_4 ),
    inference(avatar_split_clause,[],[f297,f283,f304,f300])).

fof(f283,plain,
    ( spl18_4
  <=> sP9(sK13,sK12,sK11,k4_filter_0(sK11,sK12,sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).

fof(f297,plain,
    ( ~ m1_subset_1(k4_filter_0(sK11,sK12,sK13),u1_struct_0(sK11))
    | ~ sP2(sK12,sK13,sK11,k4_filter_0(sK11,sK12,sK13))
    | spl18_4 ),
    inference(resolution,[],[f285,f174])).

fof(f174,plain,(
    ! [X6,X4,X7,X5] :
      ( sP9(X4,X5,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ sP2(X5,X4,X6,X7) ) ),
    inference(resolution,[],[f134,f97])).

fof(f97,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X2,k4_lattices(X2,X0,X3),X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f134,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r3_lattices(X2,k4_lattices(X2,X1,X4),X0)
      | sP9(X0,X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X2)) ) ),
    inference(equality_resolution,[],[f130])).

fof(f130,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP9(X0,X1,X2,X3)
      | ~ r3_lattices(X2,k4_lattices(X2,X1,X4),X0)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f285,plain,
    ( ~ sP9(sK13,sK12,sK11,k4_filter_0(sK11,sK12,sK13))
    | spl18_4 ),
    inference(avatar_component_clause,[],[f283])).

fof(f295,plain,(
    spl18_3 ),
    inference(avatar_contradiction_clause,[],[f294])).

fof(f294,plain,
    ( $false
    | spl18_3 ),
    inference(subsumption_resolution,[],[f293,f76])).

fof(f293,plain,
    ( v2_struct_0(sK11)
    | spl18_3 ),
    inference(subsumption_resolution,[],[f292,f77])).

fof(f292,plain,
    ( ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl18_3 ),
    inference(subsumption_resolution,[],[f291,f78])).

fof(f291,plain,
    ( ~ v4_lattice3(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl18_3 ),
    inference(subsumption_resolution,[],[f290,f79])).

fof(f290,plain,
    ( ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl18_3 ),
    inference(subsumption_resolution,[],[f289,f80])).

fof(f289,plain,
    ( ~ m1_subset_1(sK12,u1_struct_0(sK11))
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl18_3 ),
    inference(subsumption_resolution,[],[f287,f81])).

fof(f287,plain,
    ( ~ m1_subset_1(sK13,u1_struct_0(sK11))
    | ~ m1_subset_1(sK12,u1_struct_0(sK11))
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl18_3 ),
    inference(resolution,[],[f281,f131])).

fof(f281,plain,
    ( ~ sP10(k4_filter_0(sK11,sK12,sK13),sK11,sK12,sK13)
    | spl18_3 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl18_3
  <=> sP10(k4_filter_0(sK11,sK12,sK13),sK11,sK12,sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).

fof(f286,plain,
    ( ~ spl18_3
    | ~ spl18_4
    | spl18_2 ),
    inference(avatar_split_clause,[],[f276,f268,f283,f279])).

fof(f276,plain,
    ( ~ sP9(sK13,sK12,sK11,k4_filter_0(sK11,sK12,sK13))
    | ~ sP10(k4_filter_0(sK11,sK12,sK13),sK11,sK12,sK13)
    | spl18_2 ),
    inference(resolution,[],[f270,f126])).

fof(f126,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      | ~ sP9(X3,X2,X1,X0)
      | ~ sP10(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f270,plain,
    ( ~ r2_hidden(k4_filter_0(sK11,sK12,sK13),a_3_6_lattice3(sK11,sK12,sK13))
    | spl18_2 ),
    inference(avatar_component_clause,[],[f268])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:33:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (14827)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.46  % (14835)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.50  % (14817)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.51  % (14834)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (14832)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (14814)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (14826)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (14815)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (14822)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (14821)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (14829)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  % (14824)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % (14823)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.53  % (14836)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.53  % (14828)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.54  % (14816)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.54  % (14818)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.54  % (14837)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.54  % (14820)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.54  % (14819)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.54  % (14833)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.55  % (14831)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.55  % (14838)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.55  % (14839)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.55/0.56  % (14830)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.55/0.56  % (14825)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 2.10/0.65  % (14818)Refutation found. Thanks to Tanya!
% 2.10/0.65  % SZS status Theorem for theBenchmark
% 2.10/0.65  % SZS output start Proof for theBenchmark
% 2.10/0.65  fof(f886,plain,(
% 2.10/0.65    $false),
% 2.10/0.65    inference(avatar_sat_refutation,[],[f286,f295,f307,f317,f325,f351,f885])).
% 2.10/0.65  fof(f885,plain,(
% 2.10/0.65    ~spl18_2 | ~spl18_6 | ~spl18_7),
% 2.10/0.65    inference(avatar_contradiction_clause,[],[f884])).
% 2.10/0.65  fof(f884,plain,(
% 2.10/0.65    $false | (~spl18_2 | ~spl18_6 | ~spl18_7)),
% 2.10/0.65    inference(subsumption_resolution,[],[f883,f344])).
% 2.10/0.65  fof(f344,plain,(
% 2.10/0.65    sP1(k4_filter_0(sK11,sK12,sK13),sK11,sK13,sK12) | ~spl18_7),
% 2.10/0.65    inference(avatar_component_clause,[],[f343])).
% 2.10/0.65  fof(f343,plain,(
% 2.10/0.65    spl18_7 <=> sP1(k4_filter_0(sK11,sK12,sK13),sK11,sK13,sK12)),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl18_7])])).
% 2.10/0.65  fof(f883,plain,(
% 2.10/0.65    ~sP1(k4_filter_0(sK11,sK12,sK13),sK11,sK13,sK12) | (~spl18_2 | ~spl18_6)),
% 2.10/0.65    inference(subsumption_resolution,[],[f872,f305])).
% 2.10/0.65  fof(f305,plain,(
% 2.10/0.65    m1_subset_1(k4_filter_0(sK11,sK12,sK13),u1_struct_0(sK11)) | ~spl18_6),
% 2.10/0.65    inference(avatar_component_clause,[],[f304])).
% 2.10/0.65  fof(f304,plain,(
% 2.10/0.65    spl18_6 <=> m1_subset_1(k4_filter_0(sK11,sK12,sK13),u1_struct_0(sK11))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl18_6])])).
% 2.10/0.65  fof(f872,plain,(
% 2.10/0.65    ~m1_subset_1(k4_filter_0(sK11,sK12,sK13),u1_struct_0(sK11)) | ~sP1(k4_filter_0(sK11,sK12,sK13),sK11,sK13,sK12) | ~spl18_2),
% 2.10/0.65    inference(trivial_inequality_removal,[],[f871])).
% 2.10/0.65  fof(f871,plain,(
% 2.10/0.65    ~m1_subset_1(k4_filter_0(sK11,sK12,sK13),u1_struct_0(sK11)) | ~sP1(k4_filter_0(sK11,sK12,sK13),sK11,sK13,sK12) | k4_filter_0(sK11,sK12,sK13) != k4_filter_0(sK11,sK12,sK13) | ~spl18_2),
% 2.10/0.65    inference(resolution,[],[f866,f269])).
% 2.10/0.65  fof(f269,plain,(
% 2.10/0.65    r2_hidden(k4_filter_0(sK11,sK12,sK13),a_3_6_lattice3(sK11,sK12,sK13)) | ~spl18_2),
% 2.10/0.65    inference(avatar_component_clause,[],[f268])).
% 2.10/0.65  fof(f268,plain,(
% 2.10/0.65    spl18_2 <=> r2_hidden(k4_filter_0(sK11,sK12,sK13),a_3_6_lattice3(sK11,sK12,sK13))),
% 2.10/0.65    introduced(avatar_definition,[new_symbols(naming,[spl18_2])])).
% 2.10/0.65  fof(f866,plain,(
% 2.10/0.65    ( ! [X34] : (~r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13)) | ~m1_subset_1(X34,u1_struct_0(sK11)) | ~sP1(X34,sK11,sK13,sK12) | k4_filter_0(sK11,sK12,sK13) != X34) )),
% 2.10/0.65    inference(subsumption_resolution,[],[f865,f80])).
% 2.10/0.65  fof(f80,plain,(
% 2.10/0.65    m1_subset_1(sK12,u1_struct_0(sK11))),
% 2.10/0.65    inference(cnf_transformation,[],[f45])).
% 2.10/0.65  fof(f45,plain,(
% 2.10/0.65    ((k4_filter_0(sK11,sK12,sK13) != k15_lattice3(sK11,a_3_6_lattice3(sK11,sK12,sK13)) & l3_lattices(sK11) & v3_filter_0(sK11) & v10_lattices(sK11) & ~v2_struct_0(sK11) & m1_subset_1(sK13,u1_struct_0(sK11))) & m1_subset_1(sK12,u1_struct_0(sK11))) & l3_lattices(sK11) & v4_lattice3(sK11) & v10_lattices(sK11) & ~v2_struct_0(sK11)),
% 2.10/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f11,f44,f43,f42])).
% 2.10/0.65  fof(f42,plain,(
% 2.10/0.65    ? [X0] : (? [X1] : (? [X2] : (k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k4_filter_0(sK11,X1,X2) != k15_lattice3(sK11,a_3_6_lattice3(sK11,X1,X2)) & l3_lattices(sK11) & v3_filter_0(sK11) & v10_lattices(sK11) & ~v2_struct_0(sK11) & m1_subset_1(X2,u1_struct_0(sK11))) & m1_subset_1(X1,u1_struct_0(sK11))) & l3_lattices(sK11) & v4_lattice3(sK11) & v10_lattices(sK11) & ~v2_struct_0(sK11))),
% 2.10/0.65    introduced(choice_axiom,[])).
% 2.10/0.65  fof(f43,plain,(
% 2.10/0.65    ? [X1] : (? [X2] : (k4_filter_0(sK11,X1,X2) != k15_lattice3(sK11,a_3_6_lattice3(sK11,X1,X2)) & l3_lattices(sK11) & v3_filter_0(sK11) & v10_lattices(sK11) & ~v2_struct_0(sK11) & m1_subset_1(X2,u1_struct_0(sK11))) & m1_subset_1(X1,u1_struct_0(sK11))) => (? [X2] : (k4_filter_0(sK11,sK12,X2) != k15_lattice3(sK11,a_3_6_lattice3(sK11,sK12,X2)) & l3_lattices(sK11) & v3_filter_0(sK11) & v10_lattices(sK11) & ~v2_struct_0(sK11) & m1_subset_1(X2,u1_struct_0(sK11))) & m1_subset_1(sK12,u1_struct_0(sK11)))),
% 2.10/0.65    introduced(choice_axiom,[])).
% 2.10/0.65  fof(f44,plain,(
% 2.10/0.65    ? [X2] : (k4_filter_0(sK11,sK12,X2) != k15_lattice3(sK11,a_3_6_lattice3(sK11,sK12,X2)) & l3_lattices(sK11) & v3_filter_0(sK11) & v10_lattices(sK11) & ~v2_struct_0(sK11) & m1_subset_1(X2,u1_struct_0(sK11))) => (k4_filter_0(sK11,sK12,sK13) != k15_lattice3(sK11,a_3_6_lattice3(sK11,sK12,sK13)) & l3_lattices(sK11) & v3_filter_0(sK11) & v10_lattices(sK11) & ~v2_struct_0(sK11) & m1_subset_1(sK13,u1_struct_0(sK11)))),
% 2.10/0.65    introduced(choice_axiom,[])).
% 2.10/0.65  fof(f11,plain,(
% 2.10/0.65    ? [X0] : (? [X1] : (? [X2] : (k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.10/0.65    inference(flattening,[],[f10])).
% 2.10/0.65  fof(f10,plain,(
% 2.10/0.65    ? [X0] : (? [X1] : (? [X2] : ((k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & (l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.10/0.65    inference(ennf_transformation,[],[f9])).
% 2.10/0.65  fof(f9,negated_conjecture,(
% 2.10/0.65    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => k4_filter_0(X0,X1,X2) = k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))))))),
% 2.10/0.65    inference(negated_conjecture,[],[f8])).
% 2.10/0.65  fof(f8,conjecture,(
% 2.10/0.65    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => k4_filter_0(X0,X1,X2) = k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))))))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_lattice3)).
% 2.10/0.65  fof(f865,plain,(
% 2.10/0.65    ( ! [X34] : (~sP1(X34,sK11,sK13,sK12) | ~m1_subset_1(X34,u1_struct_0(sK11)) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13)) | k4_filter_0(sK11,sK12,sK13) != X34) )),
% 2.10/0.65    inference(subsumption_resolution,[],[f864,f81])).
% 2.10/0.65  fof(f81,plain,(
% 2.10/0.65    m1_subset_1(sK13,u1_struct_0(sK11))),
% 2.10/0.65    inference(cnf_transformation,[],[f45])).
% 2.10/0.65  fof(f864,plain,(
% 2.10/0.65    ( ! [X34] : (~sP1(X34,sK11,sK13,sK12) | ~m1_subset_1(sK13,u1_struct_0(sK11)) | ~m1_subset_1(X34,u1_struct_0(sK11)) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13)) | k4_filter_0(sK11,sK12,sK13) != X34) )),
% 2.10/0.65    inference(subsumption_resolution,[],[f863,f76])).
% 2.10/0.65  fof(f76,plain,(
% 2.10/0.65    ~v2_struct_0(sK11)),
% 2.10/0.65    inference(cnf_transformation,[],[f45])).
% 2.10/0.65  fof(f863,plain,(
% 2.10/0.65    ( ! [X34] : (v2_struct_0(sK11) | ~sP1(X34,sK11,sK13,sK12) | ~m1_subset_1(sK13,u1_struct_0(sK11)) | ~m1_subset_1(X34,u1_struct_0(sK11)) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13)) | k4_filter_0(sK11,sK12,sK13) != X34) )),
% 2.10/0.65    inference(subsumption_resolution,[],[f862,f77])).
% 2.10/0.65  fof(f77,plain,(
% 2.10/0.65    v10_lattices(sK11)),
% 2.10/0.65    inference(cnf_transformation,[],[f45])).
% 2.10/0.65  fof(f862,plain,(
% 2.10/0.65    ( ! [X34] : (~v10_lattices(sK11) | v2_struct_0(sK11) | ~sP1(X34,sK11,sK13,sK12) | ~m1_subset_1(sK13,u1_struct_0(sK11)) | ~m1_subset_1(X34,u1_struct_0(sK11)) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13)) | k4_filter_0(sK11,sK12,sK13) != X34) )),
% 2.10/0.65    inference(subsumption_resolution,[],[f861,f78])).
% 2.10/0.65  fof(f78,plain,(
% 2.10/0.65    v4_lattice3(sK11)),
% 2.10/0.65    inference(cnf_transformation,[],[f45])).
% 2.10/0.65  fof(f861,plain,(
% 2.10/0.65    ( ! [X34] : (~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | ~sP1(X34,sK11,sK13,sK12) | ~m1_subset_1(sK13,u1_struct_0(sK11)) | ~m1_subset_1(X34,u1_struct_0(sK11)) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13)) | k4_filter_0(sK11,sK12,sK13) != X34) )),
% 2.10/0.65    inference(subsumption_resolution,[],[f851,f79])).
% 2.10/0.65  fof(f79,plain,(
% 2.10/0.65    l3_lattices(sK11)),
% 2.10/0.65    inference(cnf_transformation,[],[f45])).
% 2.10/0.65  fof(f851,plain,(
% 2.10/0.65    ( ! [X34] : (~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | ~sP1(X34,sK11,sK13,sK12) | ~m1_subset_1(sK13,u1_struct_0(sK11)) | ~m1_subset_1(X34,u1_struct_0(sK11)) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13)) | k4_filter_0(sK11,sK12,sK13) != X34) )),
% 2.10/0.65    inference(duplicate_literal_removal,[],[f850])).
% 2.10/0.65  fof(f850,plain,(
% 2.10/0.65    ( ! [X34] : (~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | ~sP1(X34,sK11,sK13,sK12) | ~m1_subset_1(sK13,u1_struct_0(sK11)) | ~m1_subset_1(X34,u1_struct_0(sK11)) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~r2_hidden(X34,a_3_6_lattice3(sK11,sK12,sK13)) | k4_filter_0(sK11,sK12,sK13) != X34 | ~m1_subset_1(X34,u1_struct_0(sK11))) )),
% 2.10/0.65    inference(resolution,[],[f827,f258])).
% 2.10/0.65  fof(f258,plain,(
% 2.10/0.65    ( ! [X4] : (~r4_lattice3(sK11,X4,a_3_6_lattice3(sK11,sK12,sK13)) | ~r2_hidden(X4,a_3_6_lattice3(sK11,sK12,sK13)) | k4_filter_0(sK11,sK12,sK13) != X4 | ~m1_subset_1(X4,u1_struct_0(sK11))) )),
% 2.10/0.65    inference(subsumption_resolution,[],[f257,f76])).
% 2.10/0.65  fof(f257,plain,(
% 2.10/0.65    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK11)) | ~r2_hidden(X4,a_3_6_lattice3(sK11,sK12,sK13)) | v2_struct_0(sK11) | k4_filter_0(sK11,sK12,sK13) != X4 | ~r4_lattice3(sK11,X4,a_3_6_lattice3(sK11,sK12,sK13))) )),
% 2.10/0.65    inference(subsumption_resolution,[],[f256,f79])).
% 2.10/0.65  fof(f256,plain,(
% 2.10/0.65    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK11)) | ~r2_hidden(X4,a_3_6_lattice3(sK11,sK12,sK13)) | ~l3_lattices(sK11) | v2_struct_0(sK11) | k4_filter_0(sK11,sK12,sK13) != X4 | ~r4_lattice3(sK11,X4,a_3_6_lattice3(sK11,sK12,sK13))) )),
% 2.10/0.65    inference(duplicate_literal_removal,[],[f255])).
% 2.10/0.65  fof(f255,plain,(
% 2.10/0.65    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK11)) | ~r2_hidden(X4,a_3_6_lattice3(sK11,sK12,sK13)) | ~l3_lattices(sK11) | v2_struct_0(sK11) | k4_filter_0(sK11,sK12,sK13) != X4 | ~m1_subset_1(X4,u1_struct_0(sK11)) | ~r4_lattice3(sK11,X4,a_3_6_lattice3(sK11,sK12,sK13))) )),
% 2.10/0.65    inference(resolution,[],[f253,f190])).
% 2.10/0.65  fof(f190,plain,(
% 2.10/0.65    ( ! [X0] : (~sP4(X0,sK11,a_3_6_lattice3(sK11,sK12,sK13)) | k4_filter_0(sK11,sK12,sK13) != X0 | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~r4_lattice3(sK11,X0,a_3_6_lattice3(sK11,sK12,sK13))) )),
% 2.10/0.65    inference(resolution,[],[f189,f109])).
% 2.10/0.65  fof(f109,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (sP5(X0,X1,X2) | ~sP4(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f60])).
% 2.10/0.65  fof(f60,plain,(
% 2.10/0.65    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ~sP4(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) & ((sP4(X2,X1,X0) & r4_lattice3(X1,X2,X0)) | ~sP5(X0,X1,X2)))),
% 2.10/0.65    inference(rectify,[],[f59])).
% 2.10/0.65  fof(f59,plain,(
% 2.10/0.65    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | ~sP4(X2,X0,X1) | ~r4_lattice3(X0,X2,X1)) & ((sP4(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP5(X1,X0,X2)))),
% 2.10/0.65    inference(flattening,[],[f58])).
% 2.10/0.65  fof(f58,plain,(
% 2.10/0.65    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | (~sP4(X2,X0,X1) | ~r4_lattice3(X0,X2,X1))) & ((sP4(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP5(X1,X0,X2)))),
% 2.10/0.65    inference(nnf_transformation,[],[f33])).
% 2.10/0.65  fof(f33,plain,(
% 2.10/0.65    ! [X1,X0,X2] : (sP5(X1,X0,X2) <=> (sP4(X2,X0,X1) & r4_lattice3(X0,X2,X1)))),
% 2.10/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 2.10/0.65  fof(f189,plain,(
% 2.10/0.65    ( ! [X2] : (~sP5(a_3_6_lattice3(sK11,sK12,sK13),sK11,X2) | ~m1_subset_1(X2,u1_struct_0(sK11)) | k4_filter_0(sK11,sK12,sK13) != X2) )),
% 2.10/0.65    inference(subsumption_resolution,[],[f188,f76])).
% 2.10/0.65  fof(f188,plain,(
% 2.10/0.65    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK11)) | v2_struct_0(sK11) | ~sP5(a_3_6_lattice3(sK11,sK12,sK13),sK11,X2) | k4_filter_0(sK11,sK12,sK13) != X2) )),
% 2.10/0.65    inference(subsumption_resolution,[],[f187,f77])).
% 2.10/0.65  fof(f187,plain,(
% 2.10/0.65    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK11)) | ~v10_lattices(sK11) | v2_struct_0(sK11) | ~sP5(a_3_6_lattice3(sK11,sK12,sK13),sK11,X2) | k4_filter_0(sK11,sK12,sK13) != X2) )),
% 2.10/0.65    inference(subsumption_resolution,[],[f186,f78])).
% 2.10/0.65  fof(f186,plain,(
% 2.10/0.65    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK11)) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | ~sP5(a_3_6_lattice3(sK11,sK12,sK13),sK11,X2) | k4_filter_0(sK11,sK12,sK13) != X2) )),
% 2.10/0.65    inference(subsumption_resolution,[],[f185,f79])).
% 2.10/0.65  fof(f185,plain,(
% 2.10/0.65    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK11)) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | ~sP5(a_3_6_lattice3(sK11,sK12,sK13),sK11,X2) | k4_filter_0(sK11,sK12,sK13) != X2) )),
% 2.10/0.65    inference(resolution,[],[f135,f158])).
% 2.10/0.65  fof(f158,plain,(
% 2.10/0.65    ( ! [X0] : (~sP6(X0,sK11,a_3_6_lattice3(sK11,sK12,sK13)) | ~sP5(a_3_6_lattice3(sK11,sK12,sK13),sK11,X0) | k4_filter_0(sK11,sK12,sK13) != X0) )),
% 2.10/0.65    inference(superposition,[],[f86,f106])).
% 2.10/0.65  fof(f106,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (k15_lattice3(X1,X2) = X0 | ~sP5(X2,X1,X0) | ~sP6(X0,X1,X2)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f57])).
% 2.10/0.65  fof(f57,plain,(
% 2.10/0.65    ! [X0,X1,X2] : (((k15_lattice3(X1,X2) = X0 | ~sP5(X2,X1,X0)) & (sP5(X2,X1,X0) | k15_lattice3(X1,X2) != X0)) | ~sP6(X0,X1,X2))),
% 2.10/0.65    inference(rectify,[],[f56])).
% 2.10/0.65  fof(f56,plain,(
% 2.10/0.65    ! [X2,X0,X1] : (((k15_lattice3(X0,X1) = X2 | ~sP5(X1,X0,X2)) & (sP5(X1,X0,X2) | k15_lattice3(X0,X1) != X2)) | ~sP6(X2,X0,X1))),
% 2.10/0.65    inference(nnf_transformation,[],[f34])).
% 2.10/0.65  fof(f34,plain,(
% 2.10/0.65    ! [X2,X0,X1] : ((k15_lattice3(X0,X1) = X2 <=> sP5(X1,X0,X2)) | ~sP6(X2,X0,X1))),
% 2.10/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 2.10/0.65  fof(f86,plain,(
% 2.10/0.65    k4_filter_0(sK11,sK12,sK13) != k15_lattice3(sK11,a_3_6_lattice3(sK11,sK12,sK13))),
% 2.10/0.65    inference(cnf_transformation,[],[f45])).
% 2.10/0.65  fof(f135,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (sP6(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.10/0.65    inference(duplicate_literal_removal,[],[f114])).
% 2.10/0.65  fof(f114,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (sP6(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f35])).
% 2.10/0.65  fof(f35,plain,(
% 2.10/0.65    ! [X0] : (! [X1,X2] : (sP6(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.10/0.65    inference(definition_folding,[],[f17,f34,f33,f32])).
% 2.10/0.65  fof(f32,plain,(
% 2.10/0.65    ! [X2,X0,X1] : (sP4(X2,X0,X1) <=> ! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 2.10/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 2.10/0.65  fof(f17,plain,(
% 2.10/0.65    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.10/0.65    inference(flattening,[],[f16])).
% 2.10/0.65  fof(f16,plain,(
% 2.10/0.65    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.10/0.65    inference(ennf_transformation,[],[f6])).
% 2.10/0.65  fof(f6,axiom,(
% 2.10/0.65    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 2.10/0.65  fof(f253,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (sP4(X0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 2.10/0.65    inference(duplicate_literal_removal,[],[f252])).
% 2.10/0.65  fof(f252,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | sP4(X0,X2,X1) | ~l3_lattices(X2) | v2_struct_0(X2) | sP4(X0,X2,X1)) )),
% 2.10/0.65    inference(resolution,[],[f250,f148])).
% 2.10/0.65  fof(f148,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (sP8(X0,sK15(X1,X0,X2)) | ~l3_lattices(X0) | v2_struct_0(X0) | sP4(X1,X0,X2)) )),
% 2.10/0.65    inference(resolution,[],[f121,f111])).
% 2.10/0.65  fof(f111,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) | sP4(X0,X1,X2)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f64])).
% 2.10/0.65  fof(f64,plain,(
% 2.10/0.65    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | (~r1_lattices(X1,X0,sK15(X0,X1,X2)) & r4_lattice3(X1,sK15(X0,X1,X2),X2) & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 2.10/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f62,f63])).
% 2.10/0.65  fof(f63,plain,(
% 2.10/0.65    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK15(X0,X1,X2)) & r4_lattice3(X1,sK15(X0,X1,X2),X2) & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))))),
% 2.10/0.65    introduced(choice_axiom,[])).
% 2.10/0.65  fof(f62,plain,(
% 2.10/0.65    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 2.10/0.65    inference(rectify,[],[f61])).
% 2.10/0.65  fof(f61,plain,(
% 2.10/0.65    ! [X2,X0,X1] : ((sP4(X2,X0,X1) | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP4(X2,X0,X1)))),
% 2.10/0.65    inference(nnf_transformation,[],[f32])).
% 2.10/0.65  fof(f121,plain,(
% 2.10/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP8(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f38])).
% 2.10/0.65  fof(f38,plain,(
% 2.10/0.65    ! [X0] : (! [X1] : (sP8(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.10/0.65    inference(definition_folding,[],[f19,f37,f36])).
% 2.10/0.65  fof(f36,plain,(
% 2.10/0.65    ! [X1,X0,X2] : (sP7(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 2.10/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 2.10/0.65  fof(f37,plain,(
% 2.10/0.65    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP7(X1,X0,X2)) | ~sP8(X0,X1))),
% 2.10/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 2.10/0.65  fof(f19,plain,(
% 2.10/0.65    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.10/0.65    inference(flattening,[],[f18])).
% 2.10/0.65  fof(f18,plain,(
% 2.10/0.65    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.10/0.65    inference(ennf_transformation,[],[f5])).
% 2.10/0.65  fof(f5,axiom,(
% 2.10/0.65    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 2.10/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 2.10/0.65  fof(f250,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (~sP8(X1,sK15(X0,X1,X2)) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | sP4(X0,X1,X2)) )),
% 2.10/0.65    inference(duplicate_literal_removal,[],[f248])).
% 2.10/0.65  fof(f248,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~sP8(X1,sK15(X0,X1,X2)) | sP4(X0,X1,X2) | sP4(X0,X1,X2)) )),
% 2.10/0.65    inference(resolution,[],[f213,f113])).
% 2.10/0.65  fof(f113,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK15(X0,X1,X2)) | sP4(X0,X1,X2)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f64])).
% 2.10/0.65  fof(f213,plain,(
% 2.10/0.65    ( ! [X2,X0,X3,X1] : (r1_lattices(X1,X0,sK15(X2,X1,X3)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X3) | ~sP8(X1,sK15(X2,X1,X3)) | sP4(X2,X1,X3)) )),
% 2.10/0.65    inference(resolution,[],[f164,f112])).
% 2.10/0.65  fof(f112,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK15(X0,X1,X2),X2) | sP4(X0,X1,X2)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f64])).
% 2.10/0.65  fof(f164,plain,(
% 2.10/0.65    ( ! [X2,X0,X3,X1] : (~r4_lattice3(X2,X3,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | r1_lattices(X2,X0,X3) | ~r2_hidden(X0,X1) | ~sP8(X2,X3)) )),
% 2.10/0.65    inference(resolution,[],[f117,f115])).
% 2.10/0.65  fof(f115,plain,(
% 2.10/0.65    ( ! [X2,X0,X1] : (sP7(X1,X0,X2) | ~r4_lattice3(X0,X1,X2) | ~sP8(X0,X1)) )),
% 2.10/0.65    inference(cnf_transformation,[],[f65])).
% 2.29/0.65  fof(f65,plain,(
% 2.29/0.65    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP7(X1,X0,X2)) & (sP7(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP8(X0,X1))),
% 2.29/0.65    inference(nnf_transformation,[],[f37])).
% 2.29/0.65  fof(f117,plain,(
% 2.29/0.65    ( ! [X4,X2,X0,X1] : (~sP7(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X4,X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f69])).
% 2.29/0.65  fof(f69,plain,(
% 2.29/0.65    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | (~r1_lattices(X1,sK16(X0,X1,X2),X0) & r2_hidden(sK16(X0,X1,X2),X2) & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 2.29/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f67,f68])).
% 2.29/0.65  fof(f68,plain,(
% 2.29/0.65    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK16(X0,X1,X2),X0) & r2_hidden(sK16(X0,X1,X2),X2) & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))))),
% 2.29/0.65    introduced(choice_axiom,[])).
% 2.29/0.65  fof(f67,plain,(
% 2.29/0.65    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 2.29/0.65    inference(rectify,[],[f66])).
% 2.29/0.65  fof(f66,plain,(
% 2.29/0.65    ! [X1,X0,X2] : ((sP7(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP7(X1,X0,X2)))),
% 2.29/0.65    inference(nnf_transformation,[],[f36])).
% 2.29/0.65  fof(f827,plain,(
% 2.29/0.65    ( ! [X6,X8,X7,X5] : (r4_lattice3(X6,X7,a_3_6_lattice3(X6,X5,X8)) | ~l3_lattices(X6) | ~v4_lattice3(X6) | ~v10_lattices(X6) | v2_struct_0(X6) | ~sP1(X7,X6,X8,X5) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(X6))) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f826,f121])).
% 2.29/0.65  fof(f826,plain,(
% 2.29/0.65    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X5,u1_struct_0(X6)) | ~l3_lattices(X6) | ~v4_lattice3(X6) | ~v10_lattices(X6) | v2_struct_0(X6) | ~sP1(X7,X6,X8,X5) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~m1_subset_1(X7,u1_struct_0(X6)) | r4_lattice3(X6,X7,a_3_6_lattice3(X6,X5,X8)) | ~sP8(X6,X7)) )),
% 2.29/0.65    inference(resolution,[],[f769,f116])).
% 2.29/0.65  fof(f116,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (~sP7(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP8(X0,X1)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f65])).
% 2.29/0.65  fof(f769,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (sP7(X3,X1,a_3_6_lattice3(X1,X2,X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~sP1(X3,X1,X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f768,f140])).
% 2.29/0.65  fof(f140,plain,(
% 2.29/0.65    ( ! [X3] : (v6_lattices(X3) | v2_struct_0(X3) | ~l3_lattices(X3) | ~v10_lattices(X3)) )),
% 2.29/0.65    inference(resolution,[],[f94,f90])).
% 2.29/0.65  fof(f90,plain,(
% 2.29/0.65    ( ! [X0] : (~sP0(X0) | v6_lattices(X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f46])).
% 2.29/0.65  fof(f46,plain,(
% 2.29/0.65    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 2.29/0.65    inference(nnf_transformation,[],[f26])).
% 2.29/0.65  fof(f26,plain,(
% 2.29/0.65    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 2.29/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.29/0.65  fof(f94,plain,(
% 2.29/0.65    ( ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f27])).
% 2.29/0.65  fof(f27,plain,(
% 2.29/0.65    ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.29/0.65    inference(definition_folding,[],[f13,f26])).
% 2.29/0.65  fof(f13,plain,(
% 2.29/0.65    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 2.29/0.65    inference(flattening,[],[f12])).
% 2.29/0.65  fof(f12,plain,(
% 2.29/0.65    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 2.29/0.65    inference(ennf_transformation,[],[f1])).
% 2.29/0.65  fof(f1,axiom,(
% 2.29/0.65    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 2.29/0.65  fof(f768,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~sP1(X3,X1,X0,X2) | sP7(X3,X1,a_3_6_lattice3(X1,X2,X0)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v6_lattices(X1)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f767,f142])).
% 2.29/0.65  fof(f142,plain,(
% 2.29/0.65    ( ! [X5] : (v8_lattices(X5) | v2_struct_0(X5) | ~l3_lattices(X5) | ~v10_lattices(X5)) )),
% 2.29/0.65    inference(resolution,[],[f94,f92])).
% 2.29/0.65  fof(f92,plain,(
% 2.29/0.65    ( ! [X0] : (~sP0(X0) | v8_lattices(X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f46])).
% 2.29/0.65  fof(f767,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~sP1(X3,X1,X0,X2) | sP7(X3,X1,a_3_6_lattice3(X1,X2,X0)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v8_lattices(X1) | ~v6_lattices(X1)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f766,f143])).
% 2.29/0.65  fof(f143,plain,(
% 2.29/0.65    ( ! [X6] : (v9_lattices(X6) | v2_struct_0(X6) | ~l3_lattices(X6) | ~v10_lattices(X6)) )),
% 2.29/0.65    inference(resolution,[],[f94,f93])).
% 2.29/0.65  fof(f93,plain,(
% 2.29/0.65    ( ! [X0] : (~sP0(X0) | v9_lattices(X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f46])).
% 2.29/0.65  fof(f766,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~sP1(X3,X1,X0,X2) | sP7(X3,X1,a_3_6_lattice3(X1,X2,X0)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v9_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1)) )),
% 2.29/0.65    inference(duplicate_literal_removal,[],[f763])).
% 2.29/0.65  fof(f763,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~sP1(X3,X1,X0,X2) | sP7(X3,X1,a_3_6_lattice3(X1,X2,X0)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1) | sP7(X3,X1,a_3_6_lattice3(X1,X2,X0))) )),
% 2.29/0.65    inference(resolution,[],[f493,f275])).
% 2.29/0.65  fof(f275,plain,(
% 2.29/0.65    ( ! [X4,X5,X3] : (~r3_lattices(X3,sK16(X4,X3,X5),X4) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v9_lattices(X3) | ~v8_lattices(X3) | ~v6_lattices(X3) | v2_struct_0(X3) | sP7(X4,X3,X5)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f273,f118])).
% 2.29/0.65  fof(f118,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) | sP7(X0,X1,X2)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f69])).
% 2.29/0.65  fof(f273,plain,(
% 2.29/0.65    ( ! [X4,X5,X3] : (~r3_lattices(X3,sK16(X4,X3,X5),X4) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~m1_subset_1(sK16(X4,X3,X5),u1_struct_0(X3)) | ~l3_lattices(X3) | ~v9_lattices(X3) | ~v8_lattices(X3) | ~v6_lattices(X3) | v2_struct_0(X3) | sP7(X4,X3,X5)) )),
% 2.29/0.65    inference(resolution,[],[f122,f120])).
% 2.29/0.65  fof(f120,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK16(X0,X1,X2),X0) | sP7(X0,X1,X2)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f69])).
% 2.29/0.65  fof(f122,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f70])).
% 2.29/0.65  fof(f70,plain,(
% 2.29/0.65    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.29/0.65    inference(nnf_transformation,[],[f21])).
% 2.29/0.65  fof(f21,plain,(
% 2.29/0.65    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 2.29/0.65    inference(flattening,[],[f20])).
% 2.29/0.65  fof(f20,plain,(
% 2.29/0.65    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 2.29/0.65    inference(ennf_transformation,[],[f2])).
% 2.29/0.65  fof(f2,axiom,(
% 2.29/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 2.29/0.65  fof(f493,plain,(
% 2.29/0.65    ( ! [X6,X10,X8,X7,X5,X9] : (r3_lattices(X7,sK16(X5,X6,a_3_6_lattice3(X7,X8,X9)),X10) | ~m1_subset_1(X9,u1_struct_0(X7)) | ~m1_subset_1(X8,u1_struct_0(X7)) | ~l3_lattices(X7) | ~v4_lattice3(X7) | ~v10_lattices(X7) | v2_struct_0(X7) | ~sP1(X10,X7,X9,X8) | sP7(X5,X6,a_3_6_lattice3(X7,X8,X9))) )),
% 2.29/0.65    inference(resolution,[],[f408,f204])).
% 2.29/0.65  fof(f204,plain,(
% 2.29/0.65    ( ! [X4,X2,X0,X3,X1] : (~sP9(X3,X4,X0,X1) | ~sP1(X2,X0,X3,X4) | r3_lattices(X0,X1,X2)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f200,f163])).
% 2.29/0.65  fof(f163,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (~sP9(X0,X1,X2,X3) | m1_subset_1(X3,u1_struct_0(X2))) )),
% 2.29/0.65    inference(duplicate_literal_removal,[],[f162])).
% 2.29/0.65  fof(f162,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,u1_struct_0(X2)) | ~sP9(X0,X1,X2,X3) | ~sP9(X0,X1,X2,X3)) )),
% 2.29/0.65    inference(superposition,[],[f127,f128])).
% 2.29/0.65  fof(f128,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (sK17(X0,X1,X2,X3) = X3 | ~sP9(X0,X1,X2,X3)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f75])).
% 2.29/0.65  fof(f75,plain,(
% 2.29/0.65    ! [X0,X1,X2,X3] : ((sP9(X0,X1,X2,X3) | ! [X4] : (~r3_lattices(X2,k4_lattices(X2,X1,X4),X0) | X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & ((r3_lattices(X2,k4_lattices(X2,X1,sK17(X0,X1,X2,X3)),X0) & sK17(X0,X1,X2,X3) = X3 & m1_subset_1(sK17(X0,X1,X2,X3),u1_struct_0(X2))) | ~sP9(X0,X1,X2,X3)))),
% 2.29/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f73,f74])).
% 2.29/0.65  fof(f74,plain,(
% 2.29/0.65    ! [X3,X2,X1,X0] : (? [X5] : (r3_lattices(X2,k4_lattices(X2,X1,X5),X0) & X3 = X5 & m1_subset_1(X5,u1_struct_0(X2))) => (r3_lattices(X2,k4_lattices(X2,X1,sK17(X0,X1,X2,X3)),X0) & sK17(X0,X1,X2,X3) = X3 & m1_subset_1(sK17(X0,X1,X2,X3),u1_struct_0(X2))))),
% 2.29/0.65    introduced(choice_axiom,[])).
% 2.29/0.65  fof(f73,plain,(
% 2.29/0.65    ! [X0,X1,X2,X3] : ((sP9(X0,X1,X2,X3) | ! [X4] : (~r3_lattices(X2,k4_lattices(X2,X1,X4),X0) | X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & (? [X5] : (r3_lattices(X2,k4_lattices(X2,X1,X5),X0) & X3 = X5 & m1_subset_1(X5,u1_struct_0(X2))) | ~sP9(X0,X1,X2,X3)))),
% 2.29/0.65    inference(rectify,[],[f72])).
% 2.29/0.65  fof(f72,plain,(
% 2.29/0.65    ! [X3,X2,X1,X0] : ((sP9(X3,X2,X1,X0) | ! [X4] : (~r3_lattices(X1,k4_lattices(X1,X2,X4),X3) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP9(X3,X2,X1,X0)))),
% 2.29/0.65    inference(nnf_transformation,[],[f39])).
% 2.29/0.65  fof(f39,plain,(
% 2.29/0.65    ! [X3,X2,X1,X0] : (sP9(X3,X2,X1,X0) <=> ? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))))),
% 2.29/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 2.29/0.65  fof(f127,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK17(X0,X1,X2,X3),u1_struct_0(X2)) | ~sP9(X0,X1,X2,X3)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f75])).
% 2.29/0.65  fof(f200,plain,(
% 2.29/0.65    ( ! [X4,X2,X0,X3,X1] : (r3_lattices(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~sP1(X2,X0,X3,X4) | ~sP9(X3,X4,X0,X1)) )),
% 2.29/0.65    inference(resolution,[],[f100,f170])).
% 2.29/0.65  fof(f170,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (r3_lattices(X2,k4_lattices(X2,X1,X3),X0) | ~sP9(X0,X1,X2,X3)) )),
% 2.29/0.65    inference(duplicate_literal_removal,[],[f169])).
% 2.29/0.65  fof(f169,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (r3_lattices(X2,k4_lattices(X2,X1,X3),X0) | ~sP9(X0,X1,X2,X3) | ~sP9(X0,X1,X2,X3)) )),
% 2.29/0.65    inference(superposition,[],[f129,f128])).
% 2.29/0.65  fof(f129,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (r3_lattices(X2,k4_lattices(X2,X1,sK17(X0,X1,X2,X3)),X0) | ~sP9(X0,X1,X2,X3)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f75])).
% 2.29/0.65  fof(f100,plain,(
% 2.29/0.65    ( ! [X2,X0,X5,X3,X1] : (~r3_lattices(X1,k4_lattices(X1,X3,X5),X2) | r3_lattices(X1,X5,X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~sP1(X0,X1,X2,X3)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f55])).
% 2.29/0.65  fof(f55,plain,(
% 2.29/0.65    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (~r3_lattices(X1,sK14(X0,X1,X2,X3),X0) & r3_lattices(X1,k4_lattices(X1,X3,sK14(X0,X1,X2,X3)),X2) & m1_subset_1(sK14(X0,X1,X2,X3),u1_struct_0(X1)))) & (! [X5] : (r3_lattices(X1,X5,X0) | ~r3_lattices(X1,k4_lattices(X1,X3,X5),X2) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~sP1(X0,X1,X2,X3)))),
% 2.29/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f53,f54])).
% 2.29/0.65  fof(f54,plain,(
% 2.29/0.65    ! [X3,X2,X1,X0] : (? [X4] : (~r3_lattices(X1,X4,X0) & r3_lattices(X1,k4_lattices(X1,X3,X4),X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r3_lattices(X1,sK14(X0,X1,X2,X3),X0) & r3_lattices(X1,k4_lattices(X1,X3,sK14(X0,X1,X2,X3)),X2) & m1_subset_1(sK14(X0,X1,X2,X3),u1_struct_0(X1))))),
% 2.29/0.65    introduced(choice_axiom,[])).
% 2.29/0.65  fof(f53,plain,(
% 2.29/0.65    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (~r3_lattices(X1,X4,X0) & r3_lattices(X1,k4_lattices(X1,X3,X4),X2) & m1_subset_1(X4,u1_struct_0(X1)))) & (! [X5] : (r3_lattices(X1,X5,X0) | ~r3_lattices(X1,k4_lattices(X1,X3,X5),X2) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~sP1(X0,X1,X2,X3)))),
% 2.29/0.65    inference(rectify,[],[f52])).
% 2.29/0.65  fof(f52,plain,(
% 2.29/0.65    ! [X3,X0,X2,X1] : ((sP1(X3,X0,X2,X1) | ? [X4] : (~r3_lattices(X0,X4,X3) & r3_lattices(X0,k4_lattices(X0,X1,X4),X2) & m1_subset_1(X4,u1_struct_0(X0)))) & (! [X4] : (r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~sP1(X3,X0,X2,X1)))),
% 2.29/0.65    inference(nnf_transformation,[],[f28])).
% 2.29/0.65  fof(f28,plain,(
% 2.29/0.65    ! [X3,X0,X2,X1] : (sP1(X3,X0,X2,X1) <=> ! [X4] : (r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2) | ~m1_subset_1(X4,u1_struct_0(X0))))),
% 2.29/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.29/0.65  fof(f408,plain,(
% 2.29/0.65    ( ! [X4,X2,X0,X3,X1] : (sP9(X0,X1,X2,sK16(X3,X4,a_3_6_lattice3(X2,X1,X0))) | sP7(X3,X4,a_3_6_lattice3(X2,X1,X0)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 2.29/0.65    inference(resolution,[],[f166,f131])).
% 2.29/0.65  fof(f131,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (sP10(X0,X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f41])).
% 2.29/0.65  fof(f41,plain,(
% 2.29/0.65    ! [X0,X1,X2,X3] : (sP10(X0,X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 2.29/0.65    inference(definition_folding,[],[f25,f40,f39])).
% 2.29/0.65  fof(f40,plain,(
% 2.29/0.65    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) <=> sP9(X3,X2,X1,X0)) | ~sP10(X0,X1,X2,X3))),
% 2.29/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).
% 2.29/0.65  fof(f25,plain,(
% 2.29/0.65    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) <=> ? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 2.29/0.65    inference(flattening,[],[f24])).
% 2.29/0.65  fof(f24,plain,(
% 2.29/0.65    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) <=> ? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1)))) | (~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 2.29/0.65    inference(ennf_transformation,[],[f7])).
% 2.29/0.65  fof(f7,axiom,(
% 2.29/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1)) & l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) <=> ? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_6_lattice3)).
% 2.29/0.65  fof(f166,plain,(
% 2.29/0.65    ( ! [X4,X2,X0,X3,X1] : (~sP10(sK16(X3,X4,a_3_6_lattice3(X2,X1,X0)),X2,X1,X0) | sP9(X0,X1,X2,sK16(X3,X4,a_3_6_lattice3(X2,X1,X0))) | sP7(X3,X4,a_3_6_lattice3(X2,X1,X0))) )),
% 2.29/0.65    inference(resolution,[],[f125,f119])).
% 2.29/0.65  fof(f119,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (r2_hidden(sK16(X0,X1,X2),X2) | sP7(X0,X1,X2)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f69])).
% 2.29/0.65  fof(f125,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | sP9(X3,X2,X1,X0) | ~sP10(X0,X1,X2,X3)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f71])).
% 2.29/0.65  fof(f71,plain,(
% 2.29/0.65    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ~sP9(X3,X2,X1,X0)) & (sP9(X3,X2,X1,X0) | ~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)))) | ~sP10(X0,X1,X2,X3))),
% 2.29/0.65    inference(nnf_transformation,[],[f40])).
% 2.29/0.65  fof(f351,plain,(
% 2.29/0.65    spl18_7 | ~spl18_5),
% 2.29/0.65    inference(avatar_split_clause,[],[f348,f300,f343])).
% 2.29/0.65  fof(f300,plain,(
% 2.29/0.65    spl18_5 <=> sP2(sK12,sK13,sK11,k4_filter_0(sK11,sK12,sK13))),
% 2.29/0.65    introduced(avatar_definition,[new_symbols(naming,[spl18_5])])).
% 2.29/0.65  fof(f348,plain,(
% 2.29/0.65    sP1(k4_filter_0(sK11,sK12,sK13),sK11,sK13,sK12) | ~spl18_5),
% 2.29/0.65    inference(resolution,[],[f301,f98])).
% 2.29/0.65  fof(f98,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (~sP2(X0,X1,X2,X3) | sP1(X3,X2,X1,X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f51])).
% 2.29/0.65  fof(f51,plain,(
% 2.29/0.65    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ~sP1(X3,X2,X1,X0) | ~r3_lattices(X2,k4_lattices(X2,X0,X3),X1)) & ((sP1(X3,X2,X1,X0) & r3_lattices(X2,k4_lattices(X2,X0,X3),X1)) | ~sP2(X0,X1,X2,X3)))),
% 2.29/0.65    inference(rectify,[],[f50])).
% 2.29/0.65  fof(f50,plain,(
% 2.29/0.65    ! [X1,X2,X0,X3] : ((sP2(X1,X2,X0,X3) | ~sP1(X3,X0,X2,X1) | ~r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) & ((sP1(X3,X0,X2,X1) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) | ~sP2(X1,X2,X0,X3)))),
% 2.29/0.65    inference(flattening,[],[f49])).
% 2.29/0.65  fof(f49,plain,(
% 2.29/0.65    ! [X1,X2,X0,X3] : ((sP2(X1,X2,X0,X3) | (~sP1(X3,X0,X2,X1) | ~r3_lattices(X0,k4_lattices(X0,X1,X3),X2))) & ((sP1(X3,X0,X2,X1) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) | ~sP2(X1,X2,X0,X3)))),
% 2.29/0.65    inference(nnf_transformation,[],[f29])).
% 2.29/0.65  fof(f29,plain,(
% 2.29/0.65    ! [X1,X2,X0,X3] : (sP2(X1,X2,X0,X3) <=> (sP1(X3,X0,X2,X1) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2)))),
% 2.29/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.29/0.65  fof(f301,plain,(
% 2.29/0.65    sP2(sK12,sK13,sK11,k4_filter_0(sK11,sK12,sK13)) | ~spl18_5),
% 2.29/0.65    inference(avatar_component_clause,[],[f300])).
% 2.29/0.65  fof(f325,plain,(
% 2.29/0.65    spl18_6),
% 2.29/0.65    inference(avatar_contradiction_clause,[],[f324])).
% 2.29/0.65  fof(f324,plain,(
% 2.29/0.65    $false | spl18_6),
% 2.29/0.65    inference(subsumption_resolution,[],[f323,f76])).
% 2.29/0.65  fof(f323,plain,(
% 2.29/0.65    v2_struct_0(sK11) | spl18_6),
% 2.29/0.65    inference(subsumption_resolution,[],[f322,f77])).
% 2.29/0.65  fof(f322,plain,(
% 2.29/0.65    ~v10_lattices(sK11) | v2_struct_0(sK11) | spl18_6),
% 2.29/0.65    inference(subsumption_resolution,[],[f321,f79])).
% 2.29/0.65  fof(f321,plain,(
% 2.29/0.65    ~l3_lattices(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | spl18_6),
% 2.29/0.65    inference(subsumption_resolution,[],[f320,f80])).
% 2.29/0.65  fof(f320,plain,(
% 2.29/0.65    ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~l3_lattices(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | spl18_6),
% 2.29/0.65    inference(subsumption_resolution,[],[f318,f81])).
% 2.29/0.65  fof(f318,plain,(
% 2.29/0.65    ~m1_subset_1(sK13,u1_struct_0(sK11)) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~l3_lattices(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | spl18_6),
% 2.29/0.65    inference(resolution,[],[f306,f124])).
% 2.29/0.65  fof(f124,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f23])).
% 2.29/0.65  fof(f23,plain,(
% 2.29/0.65    ! [X0,X1,X2] : (m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.29/0.65    inference(flattening,[],[f22])).
% 2.29/0.65  fof(f22,plain,(
% 2.29/0.65    ! [X0,X1,X2] : (m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.29/0.65    inference(ennf_transformation,[],[f4])).
% 2.29/0.65  fof(f4,axiom,(
% 2.29/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_filter_0)).
% 2.29/0.65  fof(f306,plain,(
% 2.29/0.65    ~m1_subset_1(k4_filter_0(sK11,sK12,sK13),u1_struct_0(sK11)) | spl18_6),
% 2.29/0.65    inference(avatar_component_clause,[],[f304])).
% 2.29/0.65  fof(f317,plain,(
% 2.29/0.65    spl18_5),
% 2.29/0.65    inference(avatar_contradiction_clause,[],[f316])).
% 2.29/0.65  fof(f316,plain,(
% 2.29/0.65    $false | spl18_5),
% 2.29/0.65    inference(subsumption_resolution,[],[f315,f79])).
% 2.29/0.65  fof(f315,plain,(
% 2.29/0.65    ~l3_lattices(sK11) | spl18_5),
% 2.29/0.65    inference(subsumption_resolution,[],[f314,f80])).
% 2.29/0.65  fof(f314,plain,(
% 2.29/0.65    ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~l3_lattices(sK11) | spl18_5),
% 2.29/0.65    inference(subsumption_resolution,[],[f313,f81])).
% 2.29/0.65  fof(f313,plain,(
% 2.29/0.65    ~m1_subset_1(sK13,u1_struct_0(sK11)) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~l3_lattices(sK11) | spl18_5),
% 2.29/0.65    inference(subsumption_resolution,[],[f312,f76])).
% 2.29/0.65  fof(f312,plain,(
% 2.29/0.65    v2_struct_0(sK11) | ~m1_subset_1(sK13,u1_struct_0(sK11)) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~l3_lattices(sK11) | spl18_5),
% 2.29/0.65    inference(subsumption_resolution,[],[f311,f77])).
% 2.29/0.65  fof(f311,plain,(
% 2.29/0.65    ~v10_lattices(sK11) | v2_struct_0(sK11) | ~m1_subset_1(sK13,u1_struct_0(sK11)) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~l3_lattices(sK11) | spl18_5),
% 2.29/0.65    inference(subsumption_resolution,[],[f308,f84])).
% 2.29/0.65  fof(f84,plain,(
% 2.29/0.65    v3_filter_0(sK11)),
% 2.29/0.65    inference(cnf_transformation,[],[f45])).
% 2.29/0.65  fof(f308,plain,(
% 2.29/0.65    ~v3_filter_0(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | ~m1_subset_1(sK13,u1_struct_0(sK11)) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~l3_lattices(sK11) | spl18_5),
% 2.29/0.65    inference(resolution,[],[f302,f243])).
% 2.29/0.65  fof(f243,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (sP2(X1,X2,X0,k4_filter_0(X0,X1,X2)) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0)) )),
% 2.29/0.65    inference(subsumption_resolution,[],[f241,f124])).
% 2.29/0.65  fof(f241,plain,(
% 2.29/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | sP2(X1,X2,X0,k4_filter_0(X0,X1,X2))) )),
% 2.29/0.65    inference(resolution,[],[f136,f132])).
% 2.29/0.65  fof(f132,plain,(
% 2.29/0.65    ( ! [X2,X3,X1] : (~sP3(k4_filter_0(X1,X3,X2),X1,X2,X3) | sP2(X3,X2,X1,k4_filter_0(X1,X3,X2))) )),
% 2.29/0.65    inference(equality_resolution,[],[f95])).
% 2.29/0.65  fof(f95,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (sP2(X3,X2,X1,X0) | k4_filter_0(X1,X3,X2) != X0 | ~sP3(X0,X1,X2,X3)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f48])).
% 2.29/0.65  fof(f48,plain,(
% 2.29/0.65    ! [X0,X1,X2,X3] : (((k4_filter_0(X1,X3,X2) = X0 | ~sP2(X3,X2,X1,X0)) & (sP2(X3,X2,X1,X0) | k4_filter_0(X1,X3,X2) != X0)) | ~sP3(X0,X1,X2,X3))),
% 2.29/0.65    inference(rectify,[],[f47])).
% 2.29/0.65  fof(f47,plain,(
% 2.29/0.65    ! [X3,X0,X2,X1] : (((k4_filter_0(X0,X1,X2) = X3 | ~sP2(X1,X2,X0,X3)) & (sP2(X1,X2,X0,X3) | k4_filter_0(X0,X1,X2) != X3)) | ~sP3(X3,X0,X2,X1))),
% 2.29/0.65    inference(nnf_transformation,[],[f30])).
% 2.29/0.65  fof(f30,plain,(
% 2.29/0.65    ! [X3,X0,X2,X1] : ((k4_filter_0(X0,X1,X2) = X3 <=> sP2(X1,X2,X0,X3)) | ~sP3(X3,X0,X2,X1))),
% 2.29/0.65    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.29/0.65  fof(f136,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (sP3(X3,X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 2.29/0.65    inference(duplicate_literal_removal,[],[f104])).
% 2.29/0.65  fof(f104,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (sP3(X3,X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f31])).
% 2.29/0.65  fof(f31,plain,(
% 2.29/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP3(X3,X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.29/0.65    inference(definition_folding,[],[f15,f30,f29,f28])).
% 2.29/0.65  fof(f15,plain,(
% 2.29/0.65    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_filter_0(X0,X1,X2) = X3 <=> (! [X4] : (r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.29/0.65    inference(flattening,[],[f14])).
% 2.29/0.65  fof(f14,plain,(
% 2.29/0.65    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k4_filter_0(X0,X1,X2) = X3 <=> (! [X4] : ((r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.29/0.65    inference(ennf_transformation,[],[f3])).
% 2.29/0.65  fof(f3,axiom,(
% 2.29/0.65    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k4_filter_0(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r3_lattices(X0,k4_lattices(X0,X1,X4),X2) => r3_lattices(X0,X4,X3))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2))))))))),
% 2.29/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_filter_0)).
% 2.29/0.65  fof(f302,plain,(
% 2.29/0.65    ~sP2(sK12,sK13,sK11,k4_filter_0(sK11,sK12,sK13)) | spl18_5),
% 2.29/0.65    inference(avatar_component_clause,[],[f300])).
% 2.29/0.65  fof(f307,plain,(
% 2.29/0.65    ~spl18_5 | ~spl18_6 | spl18_4),
% 2.29/0.65    inference(avatar_split_clause,[],[f297,f283,f304,f300])).
% 2.29/0.65  fof(f283,plain,(
% 2.29/0.65    spl18_4 <=> sP9(sK13,sK12,sK11,k4_filter_0(sK11,sK12,sK13))),
% 2.29/0.65    introduced(avatar_definition,[new_symbols(naming,[spl18_4])])).
% 2.29/0.65  fof(f297,plain,(
% 2.29/0.65    ~m1_subset_1(k4_filter_0(sK11,sK12,sK13),u1_struct_0(sK11)) | ~sP2(sK12,sK13,sK11,k4_filter_0(sK11,sK12,sK13)) | spl18_4),
% 2.29/0.65    inference(resolution,[],[f285,f174])).
% 2.29/0.65  fof(f174,plain,(
% 2.29/0.65    ( ! [X6,X4,X7,X5] : (sP9(X4,X5,X6,X7) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~sP2(X5,X4,X6,X7)) )),
% 2.29/0.65    inference(resolution,[],[f134,f97])).
% 2.29/0.65  fof(f97,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (r3_lattices(X2,k4_lattices(X2,X0,X3),X1) | ~sP2(X0,X1,X2,X3)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f51])).
% 2.29/0.65  fof(f134,plain,(
% 2.29/0.65    ( ! [X4,X2,X0,X1] : (~r3_lattices(X2,k4_lattices(X2,X1,X4),X0) | sP9(X0,X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X2))) )),
% 2.29/0.65    inference(equality_resolution,[],[f130])).
% 2.29/0.65  fof(f130,plain,(
% 2.29/0.65    ( ! [X4,X2,X0,X3,X1] : (sP9(X0,X1,X2,X3) | ~r3_lattices(X2,k4_lattices(X2,X1,X4),X0) | X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) )),
% 2.29/0.65    inference(cnf_transformation,[],[f75])).
% 2.29/0.65  fof(f285,plain,(
% 2.29/0.65    ~sP9(sK13,sK12,sK11,k4_filter_0(sK11,sK12,sK13)) | spl18_4),
% 2.29/0.65    inference(avatar_component_clause,[],[f283])).
% 2.29/0.65  fof(f295,plain,(
% 2.29/0.65    spl18_3),
% 2.29/0.65    inference(avatar_contradiction_clause,[],[f294])).
% 2.29/0.65  fof(f294,plain,(
% 2.29/0.65    $false | spl18_3),
% 2.29/0.65    inference(subsumption_resolution,[],[f293,f76])).
% 2.29/0.65  fof(f293,plain,(
% 2.29/0.65    v2_struct_0(sK11) | spl18_3),
% 2.29/0.65    inference(subsumption_resolution,[],[f292,f77])).
% 2.29/0.65  fof(f292,plain,(
% 2.29/0.65    ~v10_lattices(sK11) | v2_struct_0(sK11) | spl18_3),
% 2.29/0.65    inference(subsumption_resolution,[],[f291,f78])).
% 2.29/0.65  fof(f291,plain,(
% 2.29/0.65    ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | spl18_3),
% 2.29/0.65    inference(subsumption_resolution,[],[f290,f79])).
% 2.29/0.65  fof(f290,plain,(
% 2.29/0.65    ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | spl18_3),
% 2.29/0.65    inference(subsumption_resolution,[],[f289,f80])).
% 2.29/0.65  fof(f289,plain,(
% 2.29/0.65    ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | spl18_3),
% 2.29/0.65    inference(subsumption_resolution,[],[f287,f81])).
% 2.29/0.65  fof(f287,plain,(
% 2.29/0.65    ~m1_subset_1(sK13,u1_struct_0(sK11)) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | spl18_3),
% 2.29/0.65    inference(resolution,[],[f281,f131])).
% 2.29/0.65  fof(f281,plain,(
% 2.29/0.65    ~sP10(k4_filter_0(sK11,sK12,sK13),sK11,sK12,sK13) | spl18_3),
% 2.29/0.65    inference(avatar_component_clause,[],[f279])).
% 2.29/0.65  fof(f279,plain,(
% 2.29/0.65    spl18_3 <=> sP10(k4_filter_0(sK11,sK12,sK13),sK11,sK12,sK13)),
% 2.29/0.65    introduced(avatar_definition,[new_symbols(naming,[spl18_3])])).
% 2.29/0.65  fof(f286,plain,(
% 2.29/0.65    ~spl18_3 | ~spl18_4 | spl18_2),
% 2.29/0.65    inference(avatar_split_clause,[],[f276,f268,f283,f279])).
% 2.29/0.65  fof(f276,plain,(
% 2.29/0.65    ~sP9(sK13,sK12,sK11,k4_filter_0(sK11,sK12,sK13)) | ~sP10(k4_filter_0(sK11,sK12,sK13),sK11,sK12,sK13) | spl18_2),
% 2.29/0.65    inference(resolution,[],[f270,f126])).
% 2.29/0.65  fof(f126,plain,(
% 2.29/0.65    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ~sP9(X3,X2,X1,X0) | ~sP10(X0,X1,X2,X3)) )),
% 2.29/0.65    inference(cnf_transformation,[],[f71])).
% 2.29/0.65  fof(f270,plain,(
% 2.29/0.65    ~r2_hidden(k4_filter_0(sK11,sK12,sK13),a_3_6_lattice3(sK11,sK12,sK13)) | spl18_2),
% 2.29/0.65    inference(avatar_component_clause,[],[f268])).
% 2.29/0.65  % SZS output end Proof for theBenchmark
% 2.29/0.65  % (14818)------------------------------
% 2.29/0.65  % (14818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.65  % (14818)Termination reason: Refutation
% 2.29/0.65  
% 2.29/0.65  % (14818)Memory used [KB]: 6780
% 2.29/0.65  % (14818)Time elapsed: 0.241 s
% 2.29/0.65  % (14818)------------------------------
% 2.29/0.65  % (14818)------------------------------
% 2.29/0.66  % (14823)Refutation not found, incomplete strategy% (14823)------------------------------
% 2.29/0.66  % (14823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.66  % (14823)Termination reason: Refutation not found, incomplete strategy
% 2.29/0.66  
% 2.29/0.66  % (14823)Memory used [KB]: 6140
% 2.29/0.66  % (14823)Time elapsed: 0.243 s
% 2.29/0.66  % (14823)------------------------------
% 2.29/0.66  % (14823)------------------------------
% 2.29/0.67  % (14813)Success in time 0.312 s
%------------------------------------------------------------------------------
