%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:39 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  324 (1392 expanded)
%              Number of leaves         :   38 ( 471 expanded)
%              Depth                    :   35
%              Number of atoms          : 1649 (10831 expanded)
%              Number of equality atoms :   64 (1411 expanded)
%              Maximal formula depth    :   19 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1090,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f148,f149,f150,f282,f287,f292,f735,f739,f763,f804,f811,f968,f1007,f1089])).

fof(f1089,plain,
    ( spl19_3
    | ~ spl19_11 ),
    inference(avatar_contradiction_clause,[],[f1088])).

fof(f1088,plain,
    ( $false
    | spl19_3
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f1087,f147])).

fof(f147,plain,
    ( ~ sP0(sK13,sK12,sK14)
    | spl19_3 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl19_3
  <=> sP0(sK13,sK12,sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).

fof(f1087,plain,
    ( sP0(sK13,sK12,sK14)
    | ~ spl19_11 ),
    inference(duplicate_literal_removal,[],[f1086])).

fof(f1086,plain,
    ( sP0(sK13,sK12,sK14)
    | sP0(sK13,sK12,sK14)
    | ~ spl19_11 ),
    inference(resolution,[],[f1080,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X1,sK11(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r3_lattices(X1,sK11(X0,X1,X2),X0)
          & r3_lattice3(X1,sK11(X0,X1,X2),X2)
          & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r3_lattices(X1,X4,X0)
            | ~ r3_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f44,f45])).

fof(f45,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X1,X3,X0)
          & r3_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r3_lattices(X1,sK11(X0,X1,X2),X0)
        & r3_lattice3(X1,sK11(X0,X1,X2),X2)
        & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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

fof(f26,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r3_lattices(X0,X3,X1)
          | ~ r3_lattice3(X0,X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1080,plain,
    ( ! [X0] :
        ( r3_lattices(sK12,sK11(X0,sK12,sK14),sK13)
        | sP0(X0,sK12,sK14) )
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f1076,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1076,plain,
    ( ! [X0] :
        ( r3_lattices(sK12,sK11(X0,sK12,sK14),sK13)
        | ~ m1_subset_1(sK11(X0,sK12,sK14),u1_struct_0(sK12))
        | sP0(X0,sK12,sK14) )
    | ~ spl19_11 ),
    inference(resolution,[],[f1068,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK11(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f1068,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK12,X0,sK14)
        | r3_lattices(sK12,X0,sK13)
        | ~ m1_subset_1(X0,u1_struct_0(sK12)) )
    | ~ spl19_11 ),
    inference(resolution,[],[f1066,f134])).

fof(f134,plain,(
    ! [X0,X3,X1] :
      ( sP9(X0,X1,X3)
      | ~ r3_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( sP9(X0,X1,X2)
      | ~ r3_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( ( sP9(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r3_lattice3(X1,sK18(X0,X1,X2),X0)
          & sK18(X0,X1,X2) = X2
          & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP9(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f76,f77])).

fof(f77,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK18(X0,X1,X2),X0)
        & sK18(X0,X1,X2) = X2
        & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( sP9(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattice3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP9(X0,X1,X2) ) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ! [X2,X1,X0] :
      ( ( sP9(X2,X1,X0)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP9(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X2,X1,X0] :
      ( sP9(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f1066,plain,
    ( ! [X0] :
        ( ~ sP9(sK14,sK12,X0)
        | r3_lattices(sK12,X0,sK13) )
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f1065,f83])).

fof(f83,plain,(
    ~ v2_struct_0(sK12) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( ~ sP0(sK13,sK12,sK14)
      | ~ r3_lattice3(sK12,sK13,sK14)
      | sK13 != k16_lattice3(sK12,sK14) )
    & ( ( sP0(sK13,sK12,sK14)
        & r3_lattice3(sK12,sK13,sK14) )
      | sK13 = k16_lattice3(sK12,sK14) )
    & m1_subset_1(sK13,u1_struct_0(sK12))
    & l3_lattices(sK12)
    & v4_lattice3(sK12)
    & v10_lattices(sK12)
    & ~ v2_struct_0(sK12) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f48,f51,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ sP0(X1,X0,X2)
                  | ~ r3_lattice3(X0,X1,X2)
                  | k16_lattice3(X0,X2) != X1 )
                & ( ( sP0(X1,X0,X2)
                    & r3_lattice3(X0,X1,X2) )
                  | k16_lattice3(X0,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP0(X1,sK12,X2)
                | ~ r3_lattice3(sK12,X1,X2)
                | k16_lattice3(sK12,X2) != X1 )
              & ( ( sP0(X1,sK12,X2)
                  & r3_lattice3(sK12,X1,X2) )
                | k16_lattice3(sK12,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(sK12)) )
      & l3_lattices(sK12)
      & v4_lattice3(sK12)
      & v10_lattices(sK12)
      & ~ v2_struct_0(sK12) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ sP0(X1,sK12,X2)
              | ~ r3_lattice3(sK12,X1,X2)
              | k16_lattice3(sK12,X2) != X1 )
            & ( ( sP0(X1,sK12,X2)
                & r3_lattice3(sK12,X1,X2) )
              | k16_lattice3(sK12,X2) = X1 ) )
        & m1_subset_1(X1,u1_struct_0(sK12)) )
   => ( ? [X2] :
          ( ( ~ sP0(sK13,sK12,X2)
            | ~ r3_lattice3(sK12,sK13,X2)
            | k16_lattice3(sK12,X2) != sK13 )
          & ( ( sP0(sK13,sK12,X2)
              & r3_lattice3(sK12,sK13,X2) )
            | k16_lattice3(sK12,X2) = sK13 ) )
      & m1_subset_1(sK13,u1_struct_0(sK12)) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X2] :
        ( ( ~ sP0(sK13,sK12,X2)
          | ~ r3_lattice3(sK12,sK13,X2)
          | k16_lattice3(sK12,X2) != sK13 )
        & ( ( sP0(sK13,sK12,X2)
            & r3_lattice3(sK12,sK13,X2) )
          | k16_lattice3(sK12,X2) = sK13 ) )
   => ( ( ~ sP0(sK13,sK12,sK14)
        | ~ r3_lattice3(sK12,sK13,sK14)
        | sK13 != k16_lattice3(sK12,sK14) )
      & ( ( sP0(sK13,sK12,sK14)
          & r3_lattice3(sK12,sK13,sK14) )
        | sK13 = k16_lattice3(sK12,sK14) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP0(X1,X0,X2)
                | ~ r3_lattice3(X0,X1,X2)
                | k16_lattice3(X0,X2) != X1 )
              & ( ( sP0(X1,X0,X2)
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ sP0(X1,X0,X2)
                | ~ r3_lattice3(X0,X1,X2)
                | k16_lattice3(X0,X2) != X1 )
              & ( ( sP0(X1,X0,X2)
                  & r3_lattice3(X0,X1,X2) )
                | k16_lattice3(X0,X2) = X1 ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) = X1
            <~> ( sP0(X1,X0,X2)
                & r3_lattice3(X0,X1,X2) ) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f11,f26])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k16_lattice3(X0,X2) = X1
            <~> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
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
              ( k16_lattice3(X0,X2) = X1
            <~> ( ! [X3] :
                    ( r3_lattices(X0,X3,X1)
                    | ~ r3_lattice3(X0,X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r3_lattice3(X0,X1,X2) ) )
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
                ( k16_lattice3(X0,X2) = X1
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r3_lattice3(X0,X3,X2)
                       => r3_lattices(X0,X3,X1) ) )
                  & r3_lattice3(X0,X1,X2) ) ) ) ) ),
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
              ( k16_lattice3(X0,X2) = X1
            <=> ( ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( r3_lattice3(X0,X3,X2)
                     => r3_lattices(X0,X3,X1) ) )
                & r3_lattice3(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).

fof(f1065,plain,
    ( ! [X0] :
        ( ~ sP9(sK14,sK12,X0)
        | r3_lattices(sK12,X0,sK13)
        | v2_struct_0(sK12) )
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f1063,f86])).

fof(f86,plain,(
    l3_lattices(sK12) ),
    inference(cnf_transformation,[],[f52])).

fof(f1063,plain,
    ( ! [X0] :
        ( ~ sP9(sK14,sK12,X0)
        | r3_lattices(sK12,X0,sK13)
        | ~ l3_lattices(sK12)
        | v2_struct_0(sK12) )
    | ~ spl19_11 ),
    inference(resolution,[],[f970,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( sP10(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( sP10(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f25,f41,f40])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> sP9(X2,X1,X0) )
      | ~ sP10(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

fof(f970,plain,
    ( ! [X0] :
        ( ~ sP10(X0,sK12,sK14)
        | ~ sP9(sK14,sK12,X0)
        | r3_lattices(sK12,X0,sK13) )
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f917,f179])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ sP9(X0,X1,X2)
      | m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f178])).

fof(f178,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X1))
      | ~ sP9(X0,X1,X2)
      | ~ sP9(X0,X1,X2) ) ),
    inference(superposition,[],[f128,f129])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( sK18(X0,X1,X2) = X2
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1))
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f917,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK12))
        | r3_lattices(sK12,X0,sK13)
        | ~ sP9(sK14,sK12,X0)
        | ~ sP10(X0,sK12,sK14) )
    | ~ spl19_11 ),
    inference(resolution,[],[f828,f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ sP9(X2,X1,X0)
      | ~ sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ~ sP9(X2,X1,X0) )
        & ( sP9(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ sP10(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f828,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,a_2_1_lattice3(sK12,sK14))
        | ~ m1_subset_1(X1,u1_struct_0(sK12))
        | r3_lattices(sK12,X1,sK13) )
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f827,f84])).

fof(f84,plain,(
    v10_lattices(sK12) ),
    inference(cnf_transformation,[],[f52])).

fof(f827,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK12))
        | ~ r2_hidden(X1,a_2_1_lattice3(sK12,sK14))
        | ~ v10_lattices(sK12)
        | r3_lattices(sK12,X1,sK13) )
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f826,f85])).

fof(f85,plain,(
    v4_lattice3(sK12) ),
    inference(cnf_transformation,[],[f52])).

fof(f826,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK12))
        | ~ v4_lattice3(sK12)
        | ~ r2_hidden(X1,a_2_1_lattice3(sK12,sK14))
        | ~ v10_lattices(sK12)
        | r3_lattices(sK12,X1,sK13) )
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f825,f86])).

fof(f825,plain,
    ( ! [X1] :
        ( ~ l3_lattices(sK12)
        | ~ m1_subset_1(X1,u1_struct_0(sK12))
        | ~ v4_lattice3(sK12)
        | ~ r2_hidden(X1,a_2_1_lattice3(sK12,sK14))
        | ~ v10_lattices(sK12)
        | r3_lattices(sK12,X1,sK13) )
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f824,f87])).

fof(f87,plain,(
    m1_subset_1(sK13,u1_struct_0(sK12)) ),
    inference(cnf_transformation,[],[f52])).

fof(f824,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK13,u1_struct_0(sK12))
        | ~ l3_lattices(sK12)
        | ~ m1_subset_1(X1,u1_struct_0(sK12))
        | ~ v4_lattice3(sK12)
        | ~ r2_hidden(X1,a_2_1_lattice3(sK12,sK14))
        | ~ v10_lattices(sK12)
        | r3_lattices(sK12,X1,sK13) )
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f814,f83])).

fof(f814,plain,
    ( ! [X1] :
        ( v2_struct_0(sK12)
        | ~ m1_subset_1(sK13,u1_struct_0(sK12))
        | ~ l3_lattices(sK12)
        | ~ m1_subset_1(X1,u1_struct_0(sK12))
        | ~ v4_lattice3(sK12)
        | ~ r2_hidden(X1,a_2_1_lattice3(sK12,sK14))
        | ~ v10_lattices(sK12)
        | r3_lattices(sK12,X1,sK13) )
    | ~ spl19_11 ),
    inference(resolution,[],[f799,f650])).

fof(f650,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X1,X0,X2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ r2_hidden(X3,X1)
      | ~ v10_lattices(X0)
      | r3_lattices(X0,X3,X2) ) ),
    inference(subsumption_resolution,[],[f641,f135])).

fof(f135,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( sP4(X2,X0,X1)
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
          ( sP4(X2,X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f32,f31,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ! [X3] :
          ( r1_lattices(X0,X2,X3)
          | ~ r4_lattice3(X0,X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f31,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ( sP2(X2,X0,X1)
        & r4_lattice3(X0,X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ( k15_lattice3(X0,X1) = X2
      <=> sP3(X1,X0,X2) )
      | ~ sP4(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f641,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X0,X3,X2)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ r2_hidden(X3,X1)
      | ~ v10_lattices(X0)
      | ~ sP3(X1,X0,X2)
      | ~ sP4(X2,X0,X1) ) ),
    inference(superposition,[],[f479,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X1,X2) = X0
      | ~ sP3(X2,X1,X0)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( ( k15_lattice3(X1,X2) = X0
          | ~ sP3(X2,X1,X0) )
        & ( sP3(X2,X1,X0)
          | k15_lattice3(X1,X2) != X0 ) )
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ( ( k15_lattice3(X0,X1) = X2
          | ~ sP3(X1,X0,X2) )
        & ( sP3(X1,X0,X2)
          | k15_lattice3(X0,X1) != X2 ) )
      | ~ sP4(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f479,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X2,k15_lattice3(X0,X1))
      | v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ r2_hidden(X2,X1)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f478,f154])).

fof(f154,plain,(
    ! [X3] :
      ( v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3) ) ),
    inference(resolution,[],[f98,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP1(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP1(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f98,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( sP1(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f13,f28])).

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

fof(f478,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ r2_hidden(X2,X1)
      | r3_lattices(X0,X2,k15_lattice3(X0,X1))
      | ~ v6_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f477,f156])).

fof(f156,plain,(
    ! [X5] :
      ( v8_lattices(X5)
      | v2_struct_0(X5)
      | ~ l3_lattices(X5)
      | ~ v10_lattices(X5) ) ),
    inference(resolution,[],[f98,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f477,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ r2_hidden(X2,X1)
      | r3_lattices(X0,X2,k15_lattice3(X0,X1))
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f476,f157])).

fof(f157,plain,(
    ! [X6] :
      ( v9_lattices(X6)
      | v2_struct_0(X6)
      | ~ l3_lattices(X6)
      | ~ v10_lattices(X6) ) ),
    inference(resolution,[],[f98,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ sP1(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f476,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ r2_hidden(X2,X1)
      | r3_lattices(X0,X2,k15_lattice3(X0,X1))
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f471])).

fof(f471,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ r2_hidden(X2,X1)
      | r3_lattices(X0,X2,k15_lattice3(X0,X1))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f252,f125])).

fof(f125,plain,(
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
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f252,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,X2,k15_lattice3(X0,X1))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f248,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP6(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP6(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f35,f34])).

fof(f34,plain,(
    ! [X1,X0,X2] :
      ( sP5(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP5(X1,X0,X2) )
      | ~ sP6(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).

fof(f248,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_lattices(X0,X2,k15_lattice3(X0,X1))
      | ~ r2_hidden(X2,X1)
      | ~ sP6(X0,k15_lattice3(X0,X1)) ) ),
    inference(resolution,[],[f240,f196])).

fof(f196,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_lattice3(X2,X3,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | r1_lattices(X2,X0,X3)
      | ~ r2_hidden(X0,X1)
      | ~ sP6(X2,X3) ) ),
    inference(resolution,[],[f112,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( sP5(X1,X0,X2)
      | ~ r4_lattice3(X0,X1,X2)
      | ~ sP6(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP5(X1,X0,X2) )
          & ( sP5(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP6(X0,X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f112,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK16(X0,X1,X2),X0)
          & r2_hidden(sK16(X0,X1,X2),X2)
          & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f65,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK16(X0,X1,X2),X0)
        & r2_hidden(sK16(X0,X1,X2),X2)
        & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X1,X0,X2] :
      ( ( sP5(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X3,X1)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X3,X1)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP5(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f240,plain,(
    ! [X2,X3] :
      ( r4_lattice3(X2,k15_lattice3(X2,X3),X3)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(k15_lattice3(X2,X3),u1_struct_0(X2))
      | ~ l3_lattices(X2) ) ),
    inference(resolution,[],[f216,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | r4_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ~ sP2(X2,X1,X0)
        | ~ r4_lattice3(X1,X2,X0) )
      & ( ( sP2(X2,X1,X0)
          & r4_lattice3(X1,X2,X0) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | ~ sP2(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP2(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
        | ~ sP2(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP2(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f216,plain,(
    ! [X0,X1] :
      ( sP3(X1,X0,k15_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f135,f133])).

fof(f133,plain,(
    ! [X2,X1] :
      ( ~ sP4(k15_lattice3(X1,X2),X1,X2)
      | sP3(X2,X1,k15_lattice3(X1,X2)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( sP3(X2,X1,X0)
      | k15_lattice3(X1,X2) != X0
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f799,plain,
    ( sP3(a_2_1_lattice3(sK12,sK14),sK12,sK13)
    | ~ spl19_11 ),
    inference(avatar_component_clause,[],[f797])).

fof(f797,plain,
    ( spl19_11
  <=> sP3(a_2_1_lattice3(sK12,sK14),sK12,sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_11])])).

fof(f1007,plain,
    ( spl19_2
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7 ),
    inference(avatar_split_clause,[],[f1006,f275,f271,f267,f263,f141])).

fof(f141,plain,
    ( spl19_2
  <=> r3_lattice3(sK12,sK13,sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_2])])).

fof(f263,plain,
    ( spl19_4
  <=> v6_lattices(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).

fof(f267,plain,
    ( spl19_5
  <=> v8_lattices(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_5])])).

fof(f271,plain,
    ( spl19_6
  <=> v9_lattices(sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_6])])).

fof(f275,plain,
    ( spl19_7
  <=> ! [X0] :
        ( r3_lattices(sK12,sK13,X0)
        | ~ r2_hidden(X0,sK14)
        | ~ m1_subset_1(X0,u1_struct_0(sK12)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_7])])).

fof(f1006,plain,
    ( r3_lattice3(sK12,sK13,sK14)
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7 ),
    inference(subsumption_resolution,[],[f848,f175])).

fof(f175,plain,(
    sP8(sK12,sK13) ),
    inference(subsumption_resolution,[],[f174,f83])).

fof(f174,plain,
    ( sP8(sK12,sK13)
    | v2_struct_0(sK12) ),
    inference(subsumption_resolution,[],[f170,f86])).

fof(f170,plain,
    ( sP8(sK12,sK13)
    | ~ l3_lattices(sK12)
    | v2_struct_0(sK12) ),
    inference(resolution,[],[f123,f87])).

fof(f123,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP8(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP8(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f38,f37])).

fof(f37,plain,(
    ! [X1,X0,X2] :
      ( sP7(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP7(X1,X0,X2) )
      | ~ sP8(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).

fof(f848,plain,
    ( r3_lattice3(sK12,sK13,sK14)
    | ~ sP8(sK12,sK13)
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7 ),
    inference(resolution,[],[f846,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X1,X0,X2)
      | r3_lattice3(X0,X1,X2)
      | ~ sP8(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP7(X1,X0,X2) )
          & ( sP7(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP8(X0,X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f846,plain,
    ( sP7(sK13,sK12,sK14)
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7 ),
    inference(duplicate_literal_removal,[],[f845])).

fof(f845,plain,
    ( sP7(sK13,sK12,sK14)
    | sP7(sK13,sK12,sK14)
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7 ),
    inference(resolution,[],[f770,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK17(X0,X1,X2),X2)
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK17(X0,X1,X2))
          & r2_hidden(sK17(X0,X1,X2),X2)
          & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f70,f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK17(X0,X1,X2))
        & r2_hidden(sK17(X0,X1,X2),X2)
        & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X1,X0,X2] :
      ( ( sP7(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X1,X3)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP7(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f770,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK17(sK13,sK12,X0),sK14)
        | sP7(sK13,sK12,X0) )
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7 ),
    inference(subsumption_resolution,[],[f769,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f769,plain,
    ( ! [X0] :
        ( sP7(sK13,sK12,X0)
        | ~ r2_hidden(sK17(sK13,sK12,X0),sK14)
        | ~ m1_subset_1(sK17(sK13,sK12,X0),u1_struct_0(sK12)) )
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7 ),
    inference(subsumption_resolution,[],[f768,f83])).

fof(f768,plain,
    ( ! [X0] :
        ( v2_struct_0(sK12)
        | sP7(sK13,sK12,X0)
        | ~ r2_hidden(sK17(sK13,sK12,X0),sK14)
        | ~ m1_subset_1(sK17(sK13,sK12,X0),u1_struct_0(sK12)) )
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7 ),
    inference(subsumption_resolution,[],[f767,f264])).

fof(f264,plain,
    ( v6_lattices(sK12)
    | ~ spl19_4 ),
    inference(avatar_component_clause,[],[f263])).

fof(f767,plain,
    ( ! [X0] :
        ( ~ v6_lattices(sK12)
        | v2_struct_0(sK12)
        | sP7(sK13,sK12,X0)
        | ~ r2_hidden(sK17(sK13,sK12,X0),sK14)
        | ~ m1_subset_1(sK17(sK13,sK12,X0),u1_struct_0(sK12)) )
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_7 ),
    inference(subsumption_resolution,[],[f766,f268])).

fof(f268,plain,
    ( v8_lattices(sK12)
    | ~ spl19_5 ),
    inference(avatar_component_clause,[],[f267])).

fof(f766,plain,
    ( ! [X0] :
        ( ~ v8_lattices(sK12)
        | ~ v6_lattices(sK12)
        | v2_struct_0(sK12)
        | sP7(sK13,sK12,X0)
        | ~ r2_hidden(sK17(sK13,sK12,X0),sK14)
        | ~ m1_subset_1(sK17(sK13,sK12,X0),u1_struct_0(sK12)) )
    | ~ spl19_6
    | ~ spl19_7 ),
    inference(subsumption_resolution,[],[f765,f272])).

fof(f272,plain,
    ( v9_lattices(sK12)
    | ~ spl19_6 ),
    inference(avatar_component_clause,[],[f271])).

fof(f765,plain,
    ( ! [X0] :
        ( ~ v9_lattices(sK12)
        | ~ v8_lattices(sK12)
        | ~ v6_lattices(sK12)
        | v2_struct_0(sK12)
        | sP7(sK13,sK12,X0)
        | ~ r2_hidden(sK17(sK13,sK12,X0),sK14)
        | ~ m1_subset_1(sK17(sK13,sK12,X0),u1_struct_0(sK12)) )
    | ~ spl19_7 ),
    inference(subsumption_resolution,[],[f764,f86])).

fof(f764,plain,
    ( ! [X0] :
        ( ~ l3_lattices(sK12)
        | ~ v9_lattices(sK12)
        | ~ v8_lattices(sK12)
        | ~ v6_lattices(sK12)
        | v2_struct_0(sK12)
        | sP7(sK13,sK12,X0)
        | ~ r2_hidden(sK17(sK13,sK12,X0),sK14)
        | ~ m1_subset_1(sK17(sK13,sK12,X0),u1_struct_0(sK12)) )
    | ~ spl19_7 ),
    inference(subsumption_resolution,[],[f355,f87])).

fof(f355,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK13,u1_struct_0(sK12))
        | ~ l3_lattices(sK12)
        | ~ v9_lattices(sK12)
        | ~ v8_lattices(sK12)
        | ~ v6_lattices(sK12)
        | v2_struct_0(sK12)
        | sP7(sK13,sK12,X0)
        | ~ r2_hidden(sK17(sK13,sK12,X0),sK14)
        | ~ m1_subset_1(sK17(sK13,sK12,X0),u1_struct_0(sK12)) )
    | ~ spl19_7 ),
    inference(resolution,[],[f234,f276])).

fof(f276,plain,
    ( ! [X0] :
        ( r3_lattices(sK12,sK13,X0)
        | ~ r2_hidden(X0,sK14)
        | ~ m1_subset_1(X0,u1_struct_0(sK12)) )
    | ~ spl19_7 ),
    inference(avatar_component_clause,[],[f275])).

fof(f234,plain,(
    ! [X4,X5,X3] :
      ( ~ r3_lattices(X3,X4,sK17(X4,X3,X5))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ v8_lattices(X3)
      | ~ v6_lattices(X3)
      | v2_struct_0(X3)
      | sP7(X4,X3,X5) ) ),
    inference(subsumption_resolution,[],[f231,f120])).

fof(f231,plain,(
    ! [X4,X5,X3] :
      ( ~ r3_lattices(X3,X4,sK17(X4,X3,X5))
      | ~ m1_subset_1(sK17(X4,X3,X5),u1_struct_0(X3))
      | ~ m1_subset_1(X4,u1_struct_0(X3))
      | ~ l3_lattices(X3)
      | ~ v9_lattices(X3)
      | ~ v8_lattices(X3)
      | ~ v6_lattices(X3)
      | v2_struct_0(X3)
      | sP7(X4,X3,X5) ) ),
    inference(resolution,[],[f124,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK17(X0,X1,X2))
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f124,plain,(
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
    inference(cnf_transformation,[],[f73])).

fof(f968,plain,
    ( spl19_7
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_11 ),
    inference(avatar_split_clause,[],[f967,f797,f271,f267,f263,f275])).

fof(f967,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK12))
        | ~ r2_hidden(X2,sK14)
        | r3_lattices(sK12,sK13,X2) )
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f966,f83])).

fof(f966,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK12))
        | ~ r2_hidden(X2,sK14)
        | r3_lattices(sK12,sK13,X2)
        | v2_struct_0(sK12) )
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f965,f264])).

fof(f965,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK12))
        | ~ r2_hidden(X2,sK14)
        | r3_lattices(sK12,sK13,X2)
        | ~ v6_lattices(sK12)
        | v2_struct_0(sK12) )
    | ~ spl19_5
    | ~ spl19_6
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f964,f268])).

fof(f964,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK12))
        | ~ r2_hidden(X2,sK14)
        | r3_lattices(sK12,sK13,X2)
        | ~ v8_lattices(sK12)
        | ~ v6_lattices(sK12)
        | v2_struct_0(sK12) )
    | ~ spl19_6
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f963,f272])).

fof(f963,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK12))
        | ~ r2_hidden(X2,sK14)
        | r3_lattices(sK12,sK13,X2)
        | ~ v9_lattices(sK12)
        | ~ v8_lattices(sK12)
        | ~ v6_lattices(sK12)
        | v2_struct_0(sK12) )
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f962,f86])).

fof(f962,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK12))
        | ~ r2_hidden(X2,sK14)
        | r3_lattices(sK12,sK13,X2)
        | ~ l3_lattices(sK12)
        | ~ v9_lattices(sK12)
        | ~ v8_lattices(sK12)
        | ~ v6_lattices(sK12)
        | v2_struct_0(sK12) )
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f959,f87])).

fof(f959,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK12))
        | ~ r2_hidden(X2,sK14)
        | r3_lattices(sK12,sK13,X2)
        | ~ m1_subset_1(sK13,u1_struct_0(sK12))
        | ~ l3_lattices(sK12)
        | ~ v9_lattices(sK12)
        | ~ v8_lattices(sK12)
        | ~ v6_lattices(sK12)
        | v2_struct_0(sK12) )
    | ~ spl19_11 ),
    inference(duplicate_literal_removal,[],[f958])).

fof(f958,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK12))
        | ~ r2_hidden(X2,sK14)
        | r3_lattices(sK12,sK13,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK12))
        | ~ m1_subset_1(sK13,u1_struct_0(sK12))
        | ~ l3_lattices(sK12)
        | ~ v9_lattices(sK12)
        | ~ v8_lattices(sK12)
        | ~ v6_lattices(sK12)
        | v2_struct_0(sK12) )
    | ~ spl19_11 ),
    inference(resolution,[],[f930,f125])).

fof(f930,plain,
    ( ! [X0] :
        ( r1_lattices(sK12,sK13,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK12))
        | ~ r2_hidden(X0,sK14) )
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f929,f83])).

fof(f929,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK12))
        | r1_lattices(sK12,sK13,X0)
        | ~ r2_hidden(X0,sK14)
        | v2_struct_0(sK12) )
    | ~ spl19_11 ),
    inference(subsumption_resolution,[],[f927,f86])).

fof(f927,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK12))
        | r1_lattices(sK12,sK13,X0)
        | ~ l3_lattices(sK12)
        | ~ r2_hidden(X0,sK14)
        | v2_struct_0(sK12) )
    | ~ spl19_11 ),
    inference(duplicate_literal_removal,[],[f921])).

fof(f921,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK12))
        | r1_lattices(sK12,sK13,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK12))
        | ~ l3_lattices(sK12)
        | ~ r2_hidden(X0,sK14)
        | v2_struct_0(sK12) )
    | ~ spl19_11 ),
    inference(resolution,[],[f844,f507])).

fof(f507,plain,(
    ! [X6,X4,X5] :
      ( r4_lattice3(X4,X5,a_2_1_lattice3(X4,X6))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ r2_hidden(X5,X6)
      | v2_struct_0(X4) ) ),
    inference(subsumption_resolution,[],[f506,f116])).

fof(f506,plain,(
    ! [X6,X4,X5] :
      ( v2_struct_0(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ r2_hidden(X5,X6)
      | r4_lattice3(X4,X5,a_2_1_lattice3(X4,X6))
      | ~ sP6(X4,X5) ) ),
    inference(resolution,[],[f501,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP6(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f501,plain,(
    ! [X2,X0,X1] :
      ( sP5(X1,X0,a_2_1_lattice3(X0,X2))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ r2_hidden(X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f496])).

fof(f496,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | sP5(X1,X0,a_2_1_lattice3(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ r2_hidden(X1,X2)
      | sP5(X1,X0,a_2_1_lattice3(X0,X2)) ) ),
    inference(resolution,[],[f310,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK16(X0,X1,X2),X0)
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f310,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( r1_lattices(X2,sK16(X3,X4,a_2_1_lattice3(X2,X5)),X6)
      | v2_struct_0(X2)
      | sP5(X3,X4,a_2_1_lattice3(X2,X5))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ r2_hidden(X6,X5) ) ),
    inference(subsumption_resolution,[],[f309,f304])).

fof(f304,plain,(
    ! [X6,X4,X7,X5] :
      ( sP8(X6,sK16(X4,X5,a_2_1_lattice3(X6,X7)))
      | ~ l3_lattices(X6)
      | v2_struct_0(X6)
      | sP5(X4,X5,a_2_1_lattice3(X6,X7)) ) ),
    inference(duplicate_literal_removal,[],[f300])).

fof(f300,plain,(
    ! [X6,X4,X7,X5] :
      ( sP5(X4,X5,a_2_1_lattice3(X6,X7))
      | ~ l3_lattices(X6)
      | v2_struct_0(X6)
      | sP8(X6,sK16(X4,X5,a_2_1_lattice3(X6,X7)))
      | ~ l3_lattices(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f298,f199])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( ~ sP9(X0,X1,X2)
      | sP8(X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f198])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( sP8(X1,X2)
      | ~ sP9(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP9(X0,X1,X2) ) ),
    inference(superposition,[],[f176,f129])).

fof(f176,plain,(
    ! [X2,X0,X1] :
      ( sP8(X1,sK18(X0,X1,X2))
      | ~ sP9(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f128,f123])).

fof(f298,plain,(
    ! [X2,X0,X3,X1] :
      ( sP9(X0,X1,sK16(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP5(X2,X3,a_2_1_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f192,f132])).

fof(f192,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP10(sK16(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0)
      | sP9(X0,X1,sK16(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP5(X2,X3,a_2_1_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f126,f114])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK16(X0,X1,X2),X2)
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | sP9(X2,X1,X0)
      | ~ sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f309,plain,(
    ! [X6,X4,X2,X5,X3] :
      ( ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP5(X3,X4,a_2_1_lattice3(X2,X5))
      | ~ m1_subset_1(X6,u1_struct_0(X2))
      | r1_lattices(X2,sK16(X3,X4,a_2_1_lattice3(X2,X5)),X6)
      | ~ r2_hidden(X6,X5)
      | ~ sP8(X2,sK16(X3,X4,a_2_1_lattice3(X2,X5))) ) ),
    inference(resolution,[],[f301,f197])).

fof(f197,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X2,X3,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | r1_lattices(X2,X3,X0)
      | ~ r2_hidden(X0,X1)
      | ~ sP8(X2,X3) ) ),
    inference(resolution,[],[f119,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( sP7(X1,X0,X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP8(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f119,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f301,plain,(
    ! [X10,X8,X11,X9] :
      ( r3_lattice3(X10,sK16(X8,X9,a_2_1_lattice3(X10,X11)),X11)
      | ~ l3_lattices(X10)
      | v2_struct_0(X10)
      | sP5(X8,X9,a_2_1_lattice3(X10,X11)) ) ),
    inference(resolution,[],[f298,f181])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ sP9(X0,X1,X2)
      | r3_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,X2,X0)
      | ~ sP9(X0,X1,X2)
      | ~ sP9(X0,X1,X2) ) ),
    inference(superposition,[],[f130,f129])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK18(X0,X1,X2),X0)
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f844,plain,
    ( ! [X0] :
        ( ~ r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14))
        | ~ m1_subset_1(X0,u1_struct_0(sK12))
        | r1_lattices(sK12,sK13,X0) )
    | ~ spl19_11 ),
    inference(resolution,[],[f817,f104])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ r4_lattice3(X1,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK15(X0,X1,X2))
          & r4_lattice3(X1,sK15(X0,X1,X2),X2)
          & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f60,f61])).

fof(f61,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r4_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK15(X0,X1,X2))
        & r4_lattice3(X1,sK15(X0,X1,X2),X2)
        & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r4_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_lattices(X0,X2,X3)
            & r4_lattice3(X0,X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X2,X3)
            | ~ r4_lattice3(X0,X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f817,plain,
    ( sP2(sK13,sK12,a_2_1_lattice3(sK12,sK14))
    | ~ spl19_11 ),
    inference(resolution,[],[f799,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | sP2(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f811,plain,(
    spl19_12 ),
    inference(avatar_contradiction_clause,[],[f810])).

fof(f810,plain,
    ( $false
    | spl19_12 ),
    inference(subsumption_resolution,[],[f809,f83])).

fof(f809,plain,
    ( v2_struct_0(sK12)
    | spl19_12 ),
    inference(subsumption_resolution,[],[f808,f84])).

fof(f808,plain,
    ( ~ v10_lattices(sK12)
    | v2_struct_0(sK12)
    | spl19_12 ),
    inference(subsumption_resolution,[],[f807,f85])).

fof(f807,plain,
    ( ~ v4_lattice3(sK12)
    | ~ v10_lattices(sK12)
    | v2_struct_0(sK12)
    | spl19_12 ),
    inference(subsumption_resolution,[],[f806,f86])).

fof(f806,plain,
    ( ~ l3_lattices(sK12)
    | ~ v4_lattice3(sK12)
    | ~ v10_lattices(sK12)
    | v2_struct_0(sK12)
    | spl19_12 ),
    inference(subsumption_resolution,[],[f805,f87])).

fof(f805,plain,
    ( ~ m1_subset_1(sK13,u1_struct_0(sK12))
    | ~ l3_lattices(sK12)
    | ~ v4_lattice3(sK12)
    | ~ v10_lattices(sK12)
    | v2_struct_0(sK12)
    | spl19_12 ),
    inference(resolution,[],[f803,f135])).

fof(f803,plain,
    ( ~ sP4(sK13,sK12,a_2_1_lattice3(sK12,sK14))
    | spl19_12 ),
    inference(avatar_component_clause,[],[f801])).

fof(f801,plain,
    ( spl19_12
  <=> sP4(sK13,sK12,a_2_1_lattice3(sK12,sK14)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_12])])).

fof(f804,plain,
    ( spl19_11
    | ~ spl19_12
    | ~ spl19_1 ),
    inference(avatar_split_clause,[],[f795,f137,f801,f797])).

fof(f137,plain,
    ( spl19_1
  <=> sK13 = k16_lattice3(sK12,sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).

fof(f795,plain,
    ( ~ sP4(sK13,sK12,a_2_1_lattice3(sK12,sK14))
    | sP3(a_2_1_lattice3(sK12,sK14),sK12,sK13)
    | ~ spl19_1 ),
    inference(subsumption_resolution,[],[f794,f83])).

fof(f794,plain,
    ( ~ sP4(sK13,sK12,a_2_1_lattice3(sK12,sK14))
    | sP3(a_2_1_lattice3(sK12,sK14),sK12,sK13)
    | v2_struct_0(sK12)
    | ~ spl19_1 ),
    inference(subsumption_resolution,[],[f783,f86])).

fof(f783,plain,
    ( ~ sP4(sK13,sK12,a_2_1_lattice3(sK12,sK14))
    | sP3(a_2_1_lattice3(sK12,sK14),sK12,sK13)
    | ~ l3_lattices(sK12)
    | v2_struct_0(sK12)
    | ~ spl19_1 ),
    inference(superposition,[],[f191,f138])).

fof(f138,plain,
    ( sK13 = k16_lattice3(sK12,sK14)
    | ~ spl19_1 ),
    inference(avatar_component_clause,[],[f137])).

fof(f191,plain,(
    ! [X4,X3] :
      ( ~ sP4(k16_lattice3(X3,X4),X3,a_2_1_lattice3(X3,X4))
      | sP3(a_2_1_lattice3(X3,X4),X3,k16_lattice3(X3,X4))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f133,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).

fof(f763,plain,
    ( ~ spl19_2
    | spl19_9 ),
    inference(avatar_split_clause,[],[f762,f732,f141])).

fof(f732,plain,
    ( spl19_9
  <=> sP9(sK14,sK12,sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_9])])).

fof(f762,plain,
    ( ~ r3_lattice3(sK12,sK13,sK14)
    | spl19_9 ),
    inference(subsumption_resolution,[],[f748,f87])).

fof(f748,plain,
    ( ~ r3_lattice3(sK12,sK13,sK14)
    | ~ m1_subset_1(sK13,u1_struct_0(sK12))
    | spl19_9 ),
    inference(resolution,[],[f734,f134])).

fof(f734,plain,
    ( ~ sP9(sK14,sK12,sK13)
    | spl19_9 ),
    inference(avatar_component_clause,[],[f732])).

fof(f739,plain,(
    spl19_8 ),
    inference(avatar_contradiction_clause,[],[f738])).

fof(f738,plain,
    ( $false
    | spl19_8 ),
    inference(subsumption_resolution,[],[f737,f83])).

fof(f737,plain,
    ( v2_struct_0(sK12)
    | spl19_8 ),
    inference(subsumption_resolution,[],[f736,f86])).

fof(f736,plain,
    ( ~ l3_lattices(sK12)
    | v2_struct_0(sK12)
    | spl19_8 ),
    inference(resolution,[],[f730,f132])).

fof(f730,plain,
    ( ~ sP10(sK13,sK12,sK14)
    | spl19_8 ),
    inference(avatar_component_clause,[],[f728])).

fof(f728,plain,
    ( spl19_8
  <=> sP10(sK13,sK12,sK14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_8])])).

fof(f735,plain,
    ( ~ spl19_8
    | ~ spl19_9
    | spl19_1
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(avatar_split_clause,[],[f726,f271,f267,f263,f145,f137,f732,f728])).

fof(f726,plain,
    ( ~ sP9(sK14,sK12,sK13)
    | ~ sP10(sK13,sK12,sK14)
    | spl19_1
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(resolution,[],[f725,f127])).

fof(f725,plain,
    ( ~ r2_hidden(sK13,a_2_1_lattice3(sK12,sK14))
    | spl19_1
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f724,f86])).

fof(f724,plain,
    ( ~ l3_lattices(sK12)
    | ~ r2_hidden(sK13,a_2_1_lattice3(sK12,sK14))
    | spl19_1
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f723,f83])).

fof(f723,plain,
    ( v2_struct_0(sK12)
    | ~ l3_lattices(sK12)
    | ~ r2_hidden(sK13,a_2_1_lattice3(sK12,sK14))
    | spl19_1
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f722,f84])).

fof(f722,plain,
    ( ~ v10_lattices(sK12)
    | v2_struct_0(sK12)
    | ~ l3_lattices(sK12)
    | ~ r2_hidden(sK13,a_2_1_lattice3(sK12,sK14))
    | spl19_1
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f721,f85])).

fof(f721,plain,
    ( ~ v4_lattice3(sK12)
    | ~ v10_lattices(sK12)
    | v2_struct_0(sK12)
    | ~ l3_lattices(sK12)
    | ~ r2_hidden(sK13,a_2_1_lattice3(sK12,sK14))
    | spl19_1
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f720,f87])).

fof(f720,plain,
    ( ~ m1_subset_1(sK13,u1_struct_0(sK12))
    | ~ v4_lattice3(sK12)
    | ~ v10_lattices(sK12)
    | v2_struct_0(sK12)
    | ~ l3_lattices(sK12)
    | ~ r2_hidden(sK13,a_2_1_lattice3(sK12,sK14))
    | spl19_1
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f715,f139])).

fof(f139,plain,
    ( sK13 != k16_lattice3(sK12,sK14)
    | spl19_1 ),
    inference(avatar_component_clause,[],[f137])).

fof(f715,plain,
    ( sK13 = k16_lattice3(sK12,sK14)
    | ~ m1_subset_1(sK13,u1_struct_0(sK12))
    | ~ v4_lattice3(sK12)
    | ~ v10_lattices(sK12)
    | v2_struct_0(sK12)
    | ~ l3_lattices(sK12)
    | ~ r2_hidden(sK13,a_2_1_lattice3(sK12,sK14))
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(resolution,[],[f636,f401])).

fof(f401,plain,
    ( r4_lattice3(sK12,sK13,a_2_1_lattice3(sK12,sK14))
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f400,f165])).

fof(f165,plain,(
    sP6(sK12,sK13) ),
    inference(subsumption_resolution,[],[f164,f83])).

fof(f164,plain,
    ( sP6(sK12,sK13)
    | v2_struct_0(sK12) ),
    inference(subsumption_resolution,[],[f161,f86])).

fof(f161,plain,
    ( sP6(sK12,sK13)
    | ~ l3_lattices(sK12)
    | v2_struct_0(sK12) ),
    inference(resolution,[],[f116,f87])).

fof(f400,plain,
    ( r4_lattice3(sK12,sK13,a_2_1_lattice3(sK12,sK14))
    | ~ sP6(sK12,sK13)
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(resolution,[],[f398,f111])).

fof(f398,plain,
    ( sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14))
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f397,f83])).

fof(f397,plain,
    ( v2_struct_0(sK12)
    | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14))
    | ~ spl19_3
    | ~ spl19_4
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f396,f264])).

fof(f396,plain,
    ( ~ v6_lattices(sK12)
    | v2_struct_0(sK12)
    | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14))
    | ~ spl19_3
    | ~ spl19_5
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f395,f268])).

fof(f395,plain,
    ( ~ v8_lattices(sK12)
    | ~ v6_lattices(sK12)
    | v2_struct_0(sK12)
    | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14))
    | ~ spl19_3
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f394,f272])).

fof(f394,plain,
    ( ~ v9_lattices(sK12)
    | ~ v8_lattices(sK12)
    | ~ v6_lattices(sK12)
    | v2_struct_0(sK12)
    | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14))
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f393,f86])).

fof(f393,plain,
    ( ~ l3_lattices(sK12)
    | ~ v9_lattices(sK12)
    | ~ v8_lattices(sK12)
    | ~ v6_lattices(sK12)
    | v2_struct_0(sK12)
    | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14))
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f392,f87])).

fof(f392,plain,
    ( ~ m1_subset_1(sK13,u1_struct_0(sK12))
    | ~ l3_lattices(sK12)
    | ~ v9_lattices(sK12)
    | ~ v8_lattices(sK12)
    | ~ v6_lattices(sK12)
    | v2_struct_0(sK12)
    | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14))
    | ~ spl19_3 ),
    inference(duplicate_literal_removal,[],[f391])).

fof(f391,plain,
    ( ~ m1_subset_1(sK13,u1_struct_0(sK12))
    | ~ l3_lattices(sK12)
    | ~ v9_lattices(sK12)
    | ~ v8_lattices(sK12)
    | ~ v6_lattices(sK12)
    | v2_struct_0(sK12)
    | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14))
    | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14))
    | ~ spl19_3 ),
    inference(resolution,[],[f235,f307])).

fof(f307,plain,
    ( ! [X17,X16] :
        ( r3_lattices(sK12,sK16(X16,X17,a_2_1_lattice3(sK12,sK14)),sK13)
        | sP5(X16,X17,a_2_1_lattice3(sK12,sK14)) )
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f306,f83])).

fof(f306,plain,
    ( ! [X17,X16] :
        ( sP5(X16,X17,a_2_1_lattice3(sK12,sK14))
        | v2_struct_0(sK12)
        | r3_lattices(sK12,sK16(X16,X17,a_2_1_lattice3(sK12,sK14)),sK13) )
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f303,f86])).

fof(f303,plain,
    ( ! [X17,X16] :
        ( sP5(X16,X17,a_2_1_lattice3(sK12,sK14))
        | ~ l3_lattices(sK12)
        | v2_struct_0(sK12)
        | r3_lattices(sK12,sK16(X16,X17,a_2_1_lattice3(sK12,sK14)),sK13) )
    | ~ spl19_3 ),
    inference(resolution,[],[f298,f214])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ sP9(sK14,sK12,X0)
        | r3_lattices(sK12,X0,sK13) )
    | ~ spl19_3 ),
    inference(duplicate_literal_removal,[],[f213])).

fof(f213,plain,
    ( ! [X0] :
        ( r3_lattices(sK12,X0,sK13)
        | ~ sP9(sK14,sK12,X0)
        | ~ sP9(sK14,sK12,X0) )
    | ~ spl19_3 ),
    inference(superposition,[],[f210,f129])).

fof(f210,plain,
    ( ! [X1] :
        ( r3_lattices(sK12,sK18(sK14,sK12,X1),sK13)
        | ~ sP9(sK14,sK12,X1) )
    | ~ spl19_3 ),
    inference(subsumption_resolution,[],[f207,f128])).

fof(f207,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK18(sK14,sK12,X1),u1_struct_0(sK12))
        | r3_lattices(sK12,sK18(sK14,sK12,X1),sK13)
        | ~ sP9(sK14,sK12,X1) )
    | ~ spl19_3 ),
    inference(resolution,[],[f204,f130])).

fof(f204,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK12,X0,sK14)
        | ~ m1_subset_1(X0,u1_struct_0(sK12))
        | r3_lattices(sK12,X0,sK13) )
    | ~ spl19_3 ),
    inference(resolution,[],[f79,f146])).

fof(f146,plain,
    ( sP0(sK13,sK12,sK14)
    | ~ spl19_3 ),
    inference(avatar_component_clause,[],[f145])).

fof(f79,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r3_lattice3(X1,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r3_lattices(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f235,plain,(
    ! [X6,X8,X7] :
      ( ~ r3_lattices(X6,sK16(X7,X6,X8),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ l3_lattices(X6)
      | ~ v9_lattices(X6)
      | ~ v8_lattices(X6)
      | ~ v6_lattices(X6)
      | v2_struct_0(X6)
      | sP5(X7,X6,X8) ) ),
    inference(subsumption_resolution,[],[f232,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f232,plain,(
    ! [X6,X8,X7] :
      ( ~ r3_lattices(X6,sK16(X7,X6,X8),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ m1_subset_1(sK16(X7,X6,X8),u1_struct_0(X6))
      | ~ l3_lattices(X6)
      | ~ v9_lattices(X6)
      | ~ v8_lattices(X6)
      | ~ v6_lattices(X6)
      | v2_struct_0(X6)
      | sP5(X7,X6,X8) ) ),
    inference(resolution,[],[f124,f115])).

fof(f636,plain,(
    ! [X6,X4,X5] :
      ( ~ r4_lattice3(X4,X6,a_2_1_lattice3(X4,X5))
      | k16_lattice3(X4,X5) = X6
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | v2_struct_0(X4)
      | ~ l3_lattices(X4)
      | ~ r2_hidden(X6,a_2_1_lattice3(X4,X5)) ) ),
    inference(duplicate_literal_removal,[],[f635])).

fof(f635,plain,(
    ! [X6,X4,X5] :
      ( ~ l3_lattices(X4)
      | k16_lattice3(X4,X5) = X6
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | v2_struct_0(X4)
      | ~ r4_lattice3(X4,X6,a_2_1_lattice3(X4,X5))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ r2_hidden(X6,a_2_1_lattice3(X4,X5))
      | ~ l3_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f334,f347])).

fof(f347,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f346])).

fof(f346,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | sP2(X0,X2,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP2(X0,X2,X1) ) ),
    inference(resolution,[],[f342,f162])).

fof(f162,plain,(
    ! [X4,X5,X3] :
      ( sP6(X3,sK15(X4,X3,X5))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | sP2(X4,X3,X5) ) ),
    inference(resolution,[],[f116,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f342,plain,(
    ! [X2,X0,X1] :
      ( ~ sP6(X1,sK15(X0,X1,X2))
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | sP2(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X2)
      | ~ sP6(X1,sK15(X0,X1,X2))
      | sP2(X0,X1,X2)
      | sP2(X0,X1,X2) ) ),
    inference(resolution,[],[f217,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK15(X0,X1,X2))
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f217,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X1,X0,sK15(X2,X1,X3))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X3)
      | ~ sP6(X1,sK15(X2,X1,X3))
      | sP2(X2,X1,X3) ) ),
    inference(resolution,[],[f196,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK15(X0,X1,X2),X2)
      | sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f334,plain,(
    ! [X4,X2,X3] :
      ( ~ sP2(X4,X2,a_2_1_lattice3(X2,X3))
      | ~ l3_lattices(X2)
      | k16_lattice3(X2,X3) = X4
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ r4_lattice3(X2,X4,a_2_1_lattice3(X2,X3)) ) ),
    inference(resolution,[],[f254,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,X2)
      | ~ sP2(X2,X1,X0)
      | ~ r4_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f254,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(a_2_1_lattice3(X0,X1),X0,X2)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | k16_lattice3(X0,X1) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,(
    ! [X2,X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ sP3(a_2_1_lattice3(X0,X1),X0,X2)
      | k16_lattice3(X0,X1) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f189,f135])).

fof(f189,plain,(
    ! [X4,X2,X3] :
      ( ~ sP4(X4,X2,a_2_1_lattice3(X2,X3))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | ~ sP3(a_2_1_lattice3(X2,X3),X2,X4)
      | k16_lattice3(X2,X3) = X4 ) ),
    inference(superposition,[],[f109,f100])).

fof(f292,plain,(
    spl19_6 ),
    inference(avatar_contradiction_clause,[],[f291])).

fof(f291,plain,
    ( $false
    | spl19_6 ),
    inference(subsumption_resolution,[],[f290,f84])).

fof(f290,plain,
    ( ~ v10_lattices(sK12)
    | spl19_6 ),
    inference(subsumption_resolution,[],[f289,f86])).

fof(f289,plain,
    ( ~ l3_lattices(sK12)
    | ~ v10_lattices(sK12)
    | spl19_6 ),
    inference(subsumption_resolution,[],[f288,f83])).

fof(f288,plain,
    ( v2_struct_0(sK12)
    | ~ l3_lattices(sK12)
    | ~ v10_lattices(sK12)
    | spl19_6 ),
    inference(resolution,[],[f273,f157])).

fof(f273,plain,
    ( ~ v9_lattices(sK12)
    | spl19_6 ),
    inference(avatar_component_clause,[],[f271])).

fof(f287,plain,(
    spl19_5 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | spl19_5 ),
    inference(subsumption_resolution,[],[f285,f84])).

fof(f285,plain,
    ( ~ v10_lattices(sK12)
    | spl19_5 ),
    inference(subsumption_resolution,[],[f284,f86])).

fof(f284,plain,
    ( ~ l3_lattices(sK12)
    | ~ v10_lattices(sK12)
    | spl19_5 ),
    inference(subsumption_resolution,[],[f283,f83])).

fof(f283,plain,
    ( v2_struct_0(sK12)
    | ~ l3_lattices(sK12)
    | ~ v10_lattices(sK12)
    | spl19_5 ),
    inference(resolution,[],[f269,f156])).

fof(f269,plain,
    ( ~ v8_lattices(sK12)
    | spl19_5 ),
    inference(avatar_component_clause,[],[f267])).

fof(f282,plain,(
    spl19_4 ),
    inference(avatar_contradiction_clause,[],[f281])).

fof(f281,plain,
    ( $false
    | spl19_4 ),
    inference(subsumption_resolution,[],[f280,f84])).

fof(f280,plain,
    ( ~ v10_lattices(sK12)
    | spl19_4 ),
    inference(subsumption_resolution,[],[f279,f86])).

fof(f279,plain,
    ( ~ l3_lattices(sK12)
    | ~ v10_lattices(sK12)
    | spl19_4 ),
    inference(subsumption_resolution,[],[f278,f83])).

fof(f278,plain,
    ( v2_struct_0(sK12)
    | ~ l3_lattices(sK12)
    | ~ v10_lattices(sK12)
    | spl19_4 ),
    inference(resolution,[],[f265,f154])).

fof(f265,plain,
    ( ~ v6_lattices(sK12)
    | spl19_4 ),
    inference(avatar_component_clause,[],[f263])).

fof(f150,plain,
    ( spl19_1
    | spl19_2 ),
    inference(avatar_split_clause,[],[f88,f141,f137])).

fof(f88,plain,
    ( r3_lattice3(sK12,sK13,sK14)
    | sK13 = k16_lattice3(sK12,sK14) ),
    inference(cnf_transformation,[],[f52])).

fof(f149,plain,
    ( spl19_1
    | spl19_3 ),
    inference(avatar_split_clause,[],[f89,f145,f137])).

fof(f89,plain,
    ( sP0(sK13,sK12,sK14)
    | sK13 = k16_lattice3(sK12,sK14) ),
    inference(cnf_transformation,[],[f52])).

fof(f148,plain,
    ( ~ spl19_1
    | ~ spl19_2
    | ~ spl19_3 ),
    inference(avatar_split_clause,[],[f90,f145,f141,f137])).

fof(f90,plain,
    ( ~ sP0(sK13,sK12,sK14)
    | ~ r3_lattice3(sK12,sK13,sK14)
    | sK13 != k16_lattice3(sK12,sK14) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:28:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.49  % (6165)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (6164)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (6160)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.50  % (6168)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (6182)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.51  % (6163)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.51  % (6173)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (6183)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.52  % (6162)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (6171)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.52  % (6176)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.52  % (6178)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (6167)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  % (6180)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  % (6179)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.52  % (6161)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.53  % (6166)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.53  % (6170)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.53  % (6174)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.53  % (6172)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (6166)Refutation not found, incomplete strategy% (6166)------------------------------
% 0.20/0.53  % (6166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (6166)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (6166)Memory used [KB]: 1663
% 0.20/0.53  % (6166)Time elapsed: 0.088 s
% 0.20/0.53  % (6166)------------------------------
% 0.20/0.53  % (6166)------------------------------
% 0.20/0.54  % (6159)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.54  % (6177)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.54  % (6181)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.54  % (6184)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.54  % (6159)Refutation not found, incomplete strategy% (6159)------------------------------
% 0.20/0.54  % (6159)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (6159)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (6159)Memory used [KB]: 10618
% 0.20/0.54  % (6159)Time elapsed: 0.134 s
% 0.20/0.54  % (6159)------------------------------
% 0.20/0.54  % (6159)------------------------------
% 0.20/0.56  % (6169)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.56  % (6175)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.58  % (6163)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f1090,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(avatar_sat_refutation,[],[f148,f149,f150,f282,f287,f292,f735,f739,f763,f804,f811,f968,f1007,f1089])).
% 0.20/0.58  fof(f1089,plain,(
% 0.20/0.58    spl19_3 | ~spl19_11),
% 0.20/0.58    inference(avatar_contradiction_clause,[],[f1088])).
% 0.20/0.58  fof(f1088,plain,(
% 0.20/0.58    $false | (spl19_3 | ~spl19_11)),
% 0.20/0.58    inference(subsumption_resolution,[],[f1087,f147])).
% 0.20/0.58  fof(f147,plain,(
% 0.20/0.58    ~sP0(sK13,sK12,sK14) | spl19_3),
% 0.20/0.58    inference(avatar_component_clause,[],[f145])).
% 0.20/0.58  fof(f145,plain,(
% 0.20/0.58    spl19_3 <=> sP0(sK13,sK12,sK14)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl19_3])])).
% 0.20/0.58  fof(f1087,plain,(
% 0.20/0.58    sP0(sK13,sK12,sK14) | ~spl19_11),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f1086])).
% 0.20/0.58  fof(f1086,plain,(
% 0.20/0.58    sP0(sK13,sK12,sK14) | sP0(sK13,sK12,sK14) | ~spl19_11),
% 0.20/0.58    inference(resolution,[],[f1080,f82])).
% 0.20/0.58  fof(f82,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~r3_lattices(X1,sK11(X0,X1,X2),X0) | sP0(X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f46])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r3_lattices(X1,sK11(X0,X1,X2),X0) & r3_lattice3(X1,sK11(X0,X1,X2),X2) & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f44,f45])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r3_lattices(X1,sK11(X0,X1,X2),X0) & r3_lattice3(X1,sK11(X0,X1,X2),X2) & m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f44,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.58    inference(rectify,[],[f43])).
% 0.20/0.58  fof(f43,plain,(
% 0.20/0.58    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 0.20/0.58    inference(nnf_transformation,[],[f26])).
% 0.20/0.58  fof(f26,plain,(
% 0.20/0.58    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.58  fof(f1080,plain,(
% 0.20/0.58    ( ! [X0] : (r3_lattices(sK12,sK11(X0,sK12,sK14),sK13) | sP0(X0,sK12,sK14)) ) | ~spl19_11),
% 0.20/0.58    inference(subsumption_resolution,[],[f1076,f80])).
% 0.20/0.58  fof(f80,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (m1_subset_1(sK11(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f46])).
% 0.20/0.58  fof(f1076,plain,(
% 0.20/0.58    ( ! [X0] : (r3_lattices(sK12,sK11(X0,sK12,sK14),sK13) | ~m1_subset_1(sK11(X0,sK12,sK14),u1_struct_0(sK12)) | sP0(X0,sK12,sK14)) ) | ~spl19_11),
% 0.20/0.58    inference(resolution,[],[f1068,f81])).
% 0.20/0.58  fof(f81,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK11(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f46])).
% 0.20/0.58  fof(f1068,plain,(
% 0.20/0.58    ( ! [X0] : (~r3_lattice3(sK12,X0,sK14) | r3_lattices(sK12,X0,sK13) | ~m1_subset_1(X0,u1_struct_0(sK12))) ) | ~spl19_11),
% 0.20/0.58    inference(resolution,[],[f1066,f134])).
% 0.20/0.58  fof(f134,plain,(
% 0.20/0.58    ( ! [X0,X3,X1] : (sP9(X0,X1,X3) | ~r3_lattice3(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.20/0.58    inference(equality_resolution,[],[f131])).
% 0.20/0.58  fof(f131,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (sP9(X0,X1,X2) | ~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.20/0.58    inference(cnf_transformation,[],[f78])).
% 0.20/0.58  fof(f78,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((sP9(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK18(X0,X1,X2),X0) & sK18(X0,X1,X2) = X2 & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1))) | ~sP9(X0,X1,X2)))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f76,f77])).
% 0.20/0.58  fof(f77,plain,(
% 0.20/0.58    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK18(X0,X1,X2),X0) & sK18(X0,X1,X2) = X2 & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f76,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((sP9(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP9(X0,X1,X2)))),
% 0.20/0.58    inference(rectify,[],[f75])).
% 0.20/0.58  fof(f75,plain,(
% 0.20/0.58    ! [X2,X1,X0] : ((sP9(X2,X1,X0) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP9(X2,X1,X0)))),
% 0.20/0.58    inference(nnf_transformation,[],[f40])).
% 0.20/0.58  fof(f40,plain,(
% 0.20/0.58    ! [X2,X1,X0] : (sP9(X2,X1,X0) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 0.20/0.58  fof(f1066,plain,(
% 0.20/0.58    ( ! [X0] : (~sP9(sK14,sK12,X0) | r3_lattices(sK12,X0,sK13)) ) | ~spl19_11),
% 0.20/0.58    inference(subsumption_resolution,[],[f1065,f83])).
% 0.20/0.58  fof(f83,plain,(
% 0.20/0.58    ~v2_struct_0(sK12)),
% 0.20/0.58    inference(cnf_transformation,[],[f52])).
% 0.20/0.58  fof(f52,plain,(
% 0.20/0.58    (((~sP0(sK13,sK12,sK14) | ~r3_lattice3(sK12,sK13,sK14) | sK13 != k16_lattice3(sK12,sK14)) & ((sP0(sK13,sK12,sK14) & r3_lattice3(sK12,sK13,sK14)) | sK13 = k16_lattice3(sK12,sK14))) & m1_subset_1(sK13,u1_struct_0(sK12))) & l3_lattices(sK12) & v4_lattice3(sK12) & v10_lattices(sK12) & ~v2_struct_0(sK12)),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13,sK14])],[f48,f51,f50,f49])).
% 0.20/0.58  fof(f49,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : ((~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~sP0(X1,sK12,X2) | ~r3_lattice3(sK12,X1,X2) | k16_lattice3(sK12,X2) != X1) & ((sP0(X1,sK12,X2) & r3_lattice3(sK12,X1,X2)) | k16_lattice3(sK12,X2) = X1)) & m1_subset_1(X1,u1_struct_0(sK12))) & l3_lattices(sK12) & v4_lattice3(sK12) & v10_lattices(sK12) & ~v2_struct_0(sK12))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f50,plain,(
% 0.20/0.58    ? [X1] : (? [X2] : ((~sP0(X1,sK12,X2) | ~r3_lattice3(sK12,X1,X2) | k16_lattice3(sK12,X2) != X1) & ((sP0(X1,sK12,X2) & r3_lattice3(sK12,X1,X2)) | k16_lattice3(sK12,X2) = X1)) & m1_subset_1(X1,u1_struct_0(sK12))) => (? [X2] : ((~sP0(sK13,sK12,X2) | ~r3_lattice3(sK12,sK13,X2) | k16_lattice3(sK12,X2) != sK13) & ((sP0(sK13,sK12,X2) & r3_lattice3(sK12,sK13,X2)) | k16_lattice3(sK12,X2) = sK13)) & m1_subset_1(sK13,u1_struct_0(sK12)))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f51,plain,(
% 0.20/0.58    ? [X2] : ((~sP0(sK13,sK12,X2) | ~r3_lattice3(sK12,sK13,X2) | k16_lattice3(sK12,X2) != sK13) & ((sP0(sK13,sK12,X2) & r3_lattice3(sK12,sK13,X2)) | k16_lattice3(sK12,X2) = sK13)) => ((~sP0(sK13,sK12,sK14) | ~r3_lattice3(sK12,sK13,sK14) | sK13 != k16_lattice3(sK12,sK14)) & ((sP0(sK13,sK12,sK14) & r3_lattice3(sK12,sK13,sK14)) | sK13 = k16_lattice3(sK12,sK14)))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f48,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : ((~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) != X1) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f47])).
% 0.20/0.58  fof(f47,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : (((~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) != X1) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | k16_lattice3(X0,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.58    inference(nnf_transformation,[],[f27])).
% 0.20/0.58  fof(f27,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) = X1 <~> (sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.58    inference(definition_folding,[],[f11,f26])).
% 0.20/0.58  fof(f11,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) = X1 <~> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f10])).
% 0.20/0.58  fof(f10,plain,(
% 0.20/0.58    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) = X1 <~> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f9])).
% 0.20/0.58  fof(f9,negated_conjecture,(
% 0.20/0.58    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 0.20/0.58    inference(negated_conjecture,[],[f8])).
% 0.20/0.58  fof(f8,conjecture,(
% 0.20/0.58    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 0.20/0.58  fof(f1065,plain,(
% 0.20/0.58    ( ! [X0] : (~sP9(sK14,sK12,X0) | r3_lattices(sK12,X0,sK13) | v2_struct_0(sK12)) ) | ~spl19_11),
% 0.20/0.58    inference(subsumption_resolution,[],[f1063,f86])).
% 0.20/0.58  fof(f86,plain,(
% 0.20/0.58    l3_lattices(sK12)),
% 0.20/0.58    inference(cnf_transformation,[],[f52])).
% 0.20/0.58  fof(f1063,plain,(
% 0.20/0.58    ( ! [X0] : (~sP9(sK14,sK12,X0) | r3_lattices(sK12,X0,sK13) | ~l3_lattices(sK12) | v2_struct_0(sK12)) ) | ~spl19_11),
% 0.20/0.58    inference(resolution,[],[f970,f132])).
% 0.20/0.58  fof(f132,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (sP10(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f42])).
% 0.20/0.58  fof(f42,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (sP10(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 0.20/0.58    inference(definition_folding,[],[f25,f41,f40])).
% 0.20/0.58  fof(f41,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> sP9(X2,X1,X0)) | ~sP10(X0,X1,X2))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).
% 0.20/0.58  fof(f25,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 0.20/0.58    inference(flattening,[],[f24])).
% 0.20/0.58  fof(f24,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 0.20/0.58    inference(ennf_transformation,[],[f7])).
% 0.20/0.58  fof(f7,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).
% 0.20/0.58  fof(f970,plain,(
% 0.20/0.58    ( ! [X0] : (~sP10(X0,sK12,sK14) | ~sP9(sK14,sK12,X0) | r3_lattices(sK12,X0,sK13)) ) | ~spl19_11),
% 0.20/0.58    inference(subsumption_resolution,[],[f917,f179])).
% 0.20/0.58  fof(f179,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~sP9(X0,X1,X2) | m1_subset_1(X2,u1_struct_0(X1))) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f178])).
% 0.20/0.58  fof(f178,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X1)) | ~sP9(X0,X1,X2) | ~sP9(X0,X1,X2)) )),
% 0.20/0.58    inference(superposition,[],[f128,f129])).
% 0.20/0.58  fof(f129,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (sK18(X0,X1,X2) = X2 | ~sP9(X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f78])).
% 0.20/0.58  fof(f128,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)) | ~sP9(X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f78])).
% 0.20/0.58  fof(f917,plain,(
% 0.20/0.58    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK12)) | r3_lattices(sK12,X0,sK13) | ~sP9(sK14,sK12,X0) | ~sP10(X0,sK12,sK14)) ) | ~spl19_11),
% 0.20/0.58    inference(resolution,[],[f828,f127])).
% 0.20/0.58  fof(f127,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP9(X2,X1,X0) | ~sP10(X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f74])).
% 0.20/0.58  fof(f74,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP9(X2,X1,X0)) & (sP9(X2,X1,X0) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~sP10(X0,X1,X2))),
% 0.20/0.58    inference(nnf_transformation,[],[f41])).
% 0.20/0.58  fof(f828,plain,(
% 0.20/0.58    ( ! [X1] : (~r2_hidden(X1,a_2_1_lattice3(sK12,sK14)) | ~m1_subset_1(X1,u1_struct_0(sK12)) | r3_lattices(sK12,X1,sK13)) ) | ~spl19_11),
% 0.20/0.58    inference(subsumption_resolution,[],[f827,f84])).
% 0.20/0.58  fof(f84,plain,(
% 0.20/0.58    v10_lattices(sK12)),
% 0.20/0.58    inference(cnf_transformation,[],[f52])).
% 0.20/0.58  fof(f827,plain,(
% 0.20/0.58    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK12)) | ~r2_hidden(X1,a_2_1_lattice3(sK12,sK14)) | ~v10_lattices(sK12) | r3_lattices(sK12,X1,sK13)) ) | ~spl19_11),
% 0.20/0.58    inference(subsumption_resolution,[],[f826,f85])).
% 0.20/0.58  fof(f85,plain,(
% 0.20/0.58    v4_lattice3(sK12)),
% 0.20/0.58    inference(cnf_transformation,[],[f52])).
% 0.20/0.58  fof(f826,plain,(
% 0.20/0.58    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK12)) | ~v4_lattice3(sK12) | ~r2_hidden(X1,a_2_1_lattice3(sK12,sK14)) | ~v10_lattices(sK12) | r3_lattices(sK12,X1,sK13)) ) | ~spl19_11),
% 0.20/0.58    inference(subsumption_resolution,[],[f825,f86])).
% 0.20/0.58  fof(f825,plain,(
% 0.20/0.58    ( ! [X1] : (~l3_lattices(sK12) | ~m1_subset_1(X1,u1_struct_0(sK12)) | ~v4_lattice3(sK12) | ~r2_hidden(X1,a_2_1_lattice3(sK12,sK14)) | ~v10_lattices(sK12) | r3_lattices(sK12,X1,sK13)) ) | ~spl19_11),
% 0.20/0.58    inference(subsumption_resolution,[],[f824,f87])).
% 0.20/0.58  fof(f87,plain,(
% 0.20/0.58    m1_subset_1(sK13,u1_struct_0(sK12))),
% 0.20/0.58    inference(cnf_transformation,[],[f52])).
% 0.20/0.58  fof(f824,plain,(
% 0.20/0.58    ( ! [X1] : (~m1_subset_1(sK13,u1_struct_0(sK12)) | ~l3_lattices(sK12) | ~m1_subset_1(X1,u1_struct_0(sK12)) | ~v4_lattice3(sK12) | ~r2_hidden(X1,a_2_1_lattice3(sK12,sK14)) | ~v10_lattices(sK12) | r3_lattices(sK12,X1,sK13)) ) | ~spl19_11),
% 0.20/0.58    inference(subsumption_resolution,[],[f814,f83])).
% 0.20/0.58  fof(f814,plain,(
% 0.20/0.58    ( ! [X1] : (v2_struct_0(sK12) | ~m1_subset_1(sK13,u1_struct_0(sK12)) | ~l3_lattices(sK12) | ~m1_subset_1(X1,u1_struct_0(sK12)) | ~v4_lattice3(sK12) | ~r2_hidden(X1,a_2_1_lattice3(sK12,sK14)) | ~v10_lattices(sK12) | r3_lattices(sK12,X1,sK13)) ) | ~spl19_11),
% 0.20/0.58    inference(resolution,[],[f799,f650])).
% 0.20/0.58  fof(f650,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~sP3(X1,X0,X2) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~r2_hidden(X3,X1) | ~v10_lattices(X0) | r3_lattices(X0,X3,X2)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f641,f135])).
% 0.20/0.58  fof(f135,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (sP4(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f108])).
% 0.20/0.58  fof(f108,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (sP4(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f33])).
% 0.20/0.58  fof(f33,plain,(
% 0.20/0.58    ! [X0] : (! [X1,X2] : (sP4(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(definition_folding,[],[f15,f32,f31,f30])).
% 0.20/0.58  fof(f30,plain,(
% 0.20/0.58    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> ! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.58  fof(f31,plain,(
% 0.20/0.58    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> (sP2(X2,X0,X1) & r4_lattice3(X0,X2,X1)))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.58  fof(f32,plain,(
% 0.20/0.58    ! [X2,X0,X1] : ((k15_lattice3(X0,X1) = X2 <=> sP3(X1,X0,X2)) | ~sP4(X2,X0,X1))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.58  fof(f15,plain,(
% 0.20/0.58    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f14])).
% 0.20/0.58  fof(f14,plain,(
% 0.20/0.58    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f5])).
% 0.20/0.58  fof(f5,axiom,(
% 0.20/0.58    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 0.20/0.58  fof(f641,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (r3_lattices(X0,X3,X2) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~r2_hidden(X3,X1) | ~v10_lattices(X0) | ~sP3(X1,X0,X2) | ~sP4(X2,X0,X1)) )),
% 0.20/0.58    inference(superposition,[],[f479,f100])).
% 0.20/0.58  fof(f100,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k15_lattice3(X1,X2) = X0 | ~sP3(X2,X1,X0) | ~sP4(X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f55])).
% 0.20/0.58  fof(f55,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (((k15_lattice3(X1,X2) = X0 | ~sP3(X2,X1,X0)) & (sP3(X2,X1,X0) | k15_lattice3(X1,X2) != X0)) | ~sP4(X0,X1,X2))),
% 0.20/0.58    inference(rectify,[],[f54])).
% 0.20/0.58  fof(f54,plain,(
% 0.20/0.58    ! [X2,X0,X1] : (((k15_lattice3(X0,X1) = X2 | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | k15_lattice3(X0,X1) != X2)) | ~sP4(X2,X0,X1))),
% 0.20/0.58    inference(nnf_transformation,[],[f32])).
% 0.20/0.58  fof(f479,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r3_lattices(X0,X2,k15_lattice3(X0,X1)) | v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~r2_hidden(X2,X1) | ~v10_lattices(X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f478,f154])).
% 0.20/0.58  fof(f154,plain,(
% 0.20/0.58    ( ! [X3] : (v6_lattices(X3) | v2_struct_0(X3) | ~l3_lattices(X3) | ~v10_lattices(X3)) )),
% 0.20/0.58    inference(resolution,[],[f98,f94])).
% 0.20/0.58  fof(f94,plain,(
% 0.20/0.58    ( ! [X0] : (~sP1(X0) | v6_lattices(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f53])).
% 0.20/0.58  fof(f53,plain,(
% 0.20/0.58    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP1(X0))),
% 0.20/0.58    inference(nnf_transformation,[],[f28])).
% 0.20/0.58  fof(f28,plain,(
% 0.20/0.58    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP1(X0))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.58  fof(f98,plain,(
% 0.20/0.58    ( ! [X0] : (sP1(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f29])).
% 0.20/0.58  fof(f29,plain,(
% 0.20/0.58    ! [X0] : (sP1(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.58    inference(definition_folding,[],[f13,f28])).
% 0.20/0.58  fof(f13,plain,(
% 0.20/0.58    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.58    inference(flattening,[],[f12])).
% 0.20/0.58  fof(f12,plain,(
% 0.20/0.58    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f1])).
% 0.20/0.58  fof(f1,axiom,(
% 0.20/0.58    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.20/0.58  fof(f478,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~r2_hidden(X2,X1) | r3_lattices(X0,X2,k15_lattice3(X0,X1)) | ~v6_lattices(X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f477,f156])).
% 0.20/0.58  fof(f156,plain,(
% 0.20/0.58    ( ! [X5] : (v8_lattices(X5) | v2_struct_0(X5) | ~l3_lattices(X5) | ~v10_lattices(X5)) )),
% 0.20/0.58    inference(resolution,[],[f98,f96])).
% 0.20/0.58  fof(f96,plain,(
% 0.20/0.58    ( ! [X0] : (~sP1(X0) | v8_lattices(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f53])).
% 0.20/0.58  fof(f477,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~r2_hidden(X2,X1) | r3_lattices(X0,X2,k15_lattice3(X0,X1)) | ~v8_lattices(X0) | ~v6_lattices(X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f476,f157])).
% 0.20/0.58  fof(f157,plain,(
% 0.20/0.58    ( ! [X6] : (v9_lattices(X6) | v2_struct_0(X6) | ~l3_lattices(X6) | ~v10_lattices(X6)) )),
% 0.20/0.58    inference(resolution,[],[f98,f97])).
% 0.20/0.58  fof(f97,plain,(
% 0.20/0.58    ( ! [X0] : (~sP1(X0) | v9_lattices(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f53])).
% 0.20/0.58  fof(f476,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~r2_hidden(X2,X1) | r3_lattices(X0,X2,k15_lattice3(X0,X1)) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0)) )),
% 0.20/0.58    inference(duplicate_literal_removal,[],[f471])).
% 0.20/0.58  fof(f471,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~r2_hidden(X2,X1) | r3_lattices(X0,X2,k15_lattice3(X0,X1)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(resolution,[],[f252,f125])).
% 0.20/0.58  fof(f125,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f73])).
% 0.20/0.58  fof(f73,plain,(
% 0.20/0.58    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(nnf_transformation,[],[f23])).
% 0.20/0.58  fof(f23,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f22])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f2])).
% 0.20/0.58  fof(f2,axiom,(
% 0.20/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.20/0.58  fof(f252,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (r1_lattices(X0,X2,k15_lattice3(X0,X1)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~r2_hidden(X2,X1)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f248,f116])).
% 0.20/0.58  fof(f116,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP6(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f36])).
% 0.20/0.58  fof(f36,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (sP6(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(definition_folding,[],[f19,f35,f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ! [X1,X0,X2] : (sP5(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP5(X1,X0,X2)) | ~sP6(X0,X1))),
% 0.20/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.58  fof(f19,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.58    inference(flattening,[],[f18])).
% 0.20/0.58  fof(f18,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f4])).
% 0.20/0.58  fof(f4,axiom,(
% 0.20/0.58    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.20/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 0.20/0.58  fof(f248,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_lattices(X0,X2,k15_lattice3(X0,X1)) | ~r2_hidden(X2,X1) | ~sP6(X0,k15_lattice3(X0,X1))) )),
% 0.20/0.58    inference(resolution,[],[f240,f196])).
% 0.20/0.58  fof(f196,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~r4_lattice3(X2,X3,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | r1_lattices(X2,X0,X3) | ~r2_hidden(X0,X1) | ~sP6(X2,X3)) )),
% 0.20/0.58    inference(resolution,[],[f112,f110])).
% 0.20/0.58  fof(f110,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (sP5(X1,X0,X2) | ~r4_lattice3(X0,X1,X2) | ~sP6(X0,X1)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f63])).
% 0.20/0.58  fof(f63,plain,(
% 0.20/0.58    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP5(X1,X0,X2)) & (sP5(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP6(X0,X1))),
% 0.20/0.58    inference(nnf_transformation,[],[f35])).
% 0.20/0.58  fof(f112,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X1] : (~sP5(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X4,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f67])).
% 0.20/0.58  fof(f67,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | (~r1_lattices(X1,sK16(X0,X1,X2),X0) & r2_hidden(sK16(X0,X1,X2),X2) & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP5(X0,X1,X2)))),
% 0.20/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f65,f66])).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK16(X0,X1,X2),X0) & r2_hidden(sK16(X0,X1,X2),X2) & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.58    introduced(choice_axiom,[])).
% 0.20/0.58  fof(f65,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP5(X0,X1,X2)))),
% 0.20/0.58    inference(rectify,[],[f64])).
% 0.20/0.58  fof(f64,plain,(
% 0.20/0.58    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP5(X1,X0,X2)))),
% 0.20/0.58    inference(nnf_transformation,[],[f34])).
% 0.20/0.58  fof(f240,plain,(
% 0.20/0.58    ( ! [X2,X3] : (r4_lattice3(X2,k15_lattice3(X2,X3),X3) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | ~m1_subset_1(k15_lattice3(X2,X3),u1_struct_0(X2)) | ~l3_lattices(X2)) )),
% 0.20/0.58    inference(resolution,[],[f216,f101])).
% 0.20/0.58  fof(f101,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | r4_lattice3(X1,X2,X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f58])).
% 0.20/0.58  fof(f58,plain,(
% 0.20/0.58    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ~sP2(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) & ((sP2(X2,X1,X0) & r4_lattice3(X1,X2,X0)) | ~sP3(X0,X1,X2)))),
% 0.20/0.58    inference(rectify,[],[f57])).
% 0.20/0.58  fof(f57,plain,(
% 0.20/0.58    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ~sP2(X2,X0,X1) | ~r4_lattice3(X0,X2,X1)) & ((sP2(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP3(X1,X0,X2)))),
% 0.20/0.58    inference(flattening,[],[f56])).
% 0.20/0.58  fof(f56,plain,(
% 0.20/0.58    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | (~sP2(X2,X0,X1) | ~r4_lattice3(X0,X2,X1))) & ((sP2(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP3(X1,X0,X2)))),
% 0.20/0.58    inference(nnf_transformation,[],[f31])).
% 0.20/0.58  fof(f216,plain,(
% 0.20/0.58    ( ! [X0,X1] : (sP3(X1,X0,k15_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))) )),
% 0.20/0.58    inference(resolution,[],[f135,f133])).
% 0.20/0.58  fof(f133,plain,(
% 0.20/0.58    ( ! [X2,X1] : (~sP4(k15_lattice3(X1,X2),X1,X2) | sP3(X2,X1,k15_lattice3(X1,X2))) )),
% 0.20/0.58    inference(equality_resolution,[],[f99])).
% 0.20/0.58  fof(f99,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (sP3(X2,X1,X0) | k15_lattice3(X1,X2) != X0 | ~sP4(X0,X1,X2)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f55])).
% 0.20/0.58  fof(f799,plain,(
% 0.20/0.58    sP3(a_2_1_lattice3(sK12,sK14),sK12,sK13) | ~spl19_11),
% 0.20/0.58    inference(avatar_component_clause,[],[f797])).
% 0.20/0.58  fof(f797,plain,(
% 0.20/0.58    spl19_11 <=> sP3(a_2_1_lattice3(sK12,sK14),sK12,sK13)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl19_11])])).
% 0.20/0.58  fof(f1007,plain,(
% 0.20/0.58    spl19_2 | ~spl19_4 | ~spl19_5 | ~spl19_6 | ~spl19_7),
% 0.20/0.58    inference(avatar_split_clause,[],[f1006,f275,f271,f267,f263,f141])).
% 0.20/0.58  fof(f141,plain,(
% 0.20/0.58    spl19_2 <=> r3_lattice3(sK12,sK13,sK14)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl19_2])])).
% 0.20/0.58  fof(f263,plain,(
% 0.20/0.58    spl19_4 <=> v6_lattices(sK12)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).
% 0.20/0.58  fof(f267,plain,(
% 0.20/0.58    spl19_5 <=> v8_lattices(sK12)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl19_5])])).
% 0.20/0.59  fof(f271,plain,(
% 0.20/0.59    spl19_6 <=> v9_lattices(sK12)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl19_6])])).
% 0.20/0.59  fof(f275,plain,(
% 0.20/0.59    spl19_7 <=> ! [X0] : (r3_lattices(sK12,sK13,X0) | ~r2_hidden(X0,sK14) | ~m1_subset_1(X0,u1_struct_0(sK12)))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl19_7])])).
% 0.20/0.59  fof(f1006,plain,(
% 0.20/0.59    r3_lattice3(sK12,sK13,sK14) | (~spl19_4 | ~spl19_5 | ~spl19_6 | ~spl19_7)),
% 0.20/0.59    inference(subsumption_resolution,[],[f848,f175])).
% 0.20/0.59  fof(f175,plain,(
% 0.20/0.59    sP8(sK12,sK13)),
% 0.20/0.59    inference(subsumption_resolution,[],[f174,f83])).
% 0.20/0.59  fof(f174,plain,(
% 0.20/0.59    sP8(sK12,sK13) | v2_struct_0(sK12)),
% 0.20/0.59    inference(subsumption_resolution,[],[f170,f86])).
% 0.20/0.59  fof(f170,plain,(
% 0.20/0.59    sP8(sK12,sK13) | ~l3_lattices(sK12) | v2_struct_0(sK12)),
% 0.20/0.59    inference(resolution,[],[f123,f87])).
% 0.20/0.59  fof(f123,plain,(
% 0.20/0.59    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP8(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f39])).
% 0.20/0.59  fof(f39,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (sP8(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.59    inference(definition_folding,[],[f21,f38,f37])).
% 0.20/0.59  fof(f37,plain,(
% 0.20/0.59    ! [X1,X0,X2] : (sP7(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.20/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 0.20/0.59  fof(f38,plain,(
% 0.20/0.59    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP7(X1,X0,X2)) | ~sP8(X0,X1))),
% 0.20/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 0.20/0.59  fof(f21,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.59    inference(flattening,[],[f20])).
% 0.20/0.59  fof(f20,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f3])).
% 0.20/0.59  fof(f3,axiom,(
% 0.20/0.59    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 0.20/0.59  fof(f848,plain,(
% 0.20/0.59    r3_lattice3(sK12,sK13,sK14) | ~sP8(sK12,sK13) | (~spl19_4 | ~spl19_5 | ~spl19_6 | ~spl19_7)),
% 0.20/0.59    inference(resolution,[],[f846,f118])).
% 0.20/0.59  fof(f118,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~sP7(X1,X0,X2) | r3_lattice3(X0,X1,X2) | ~sP8(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f68])).
% 0.20/0.59  fof(f68,plain,(
% 0.20/0.59    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP7(X1,X0,X2)) & (sP7(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP8(X0,X1))),
% 0.20/0.59    inference(nnf_transformation,[],[f38])).
% 0.20/0.59  fof(f846,plain,(
% 0.20/0.59    sP7(sK13,sK12,sK14) | (~spl19_4 | ~spl19_5 | ~spl19_6 | ~spl19_7)),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f845])).
% 0.20/0.59  fof(f845,plain,(
% 0.20/0.59    sP7(sK13,sK12,sK14) | sP7(sK13,sK12,sK14) | (~spl19_4 | ~spl19_5 | ~spl19_6 | ~spl19_7)),
% 0.20/0.59    inference(resolution,[],[f770,f121])).
% 0.20/0.59  fof(f121,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK17(X0,X1,X2),X2) | sP7(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f72])).
% 0.20/0.59  fof(f72,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | (~r1_lattices(X1,X0,sK17(X0,X1,X2)) & r2_hidden(sK17(X0,X1,X2),X2) & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f70,f71])).
% 0.20/0.59  fof(f71,plain,(
% 0.20/0.59    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK17(X0,X1,X2)) & r2_hidden(sK17(X0,X1,X2),X2) & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f70,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 0.20/0.59    inference(rectify,[],[f69])).
% 0.20/0.59  fof(f69,plain,(
% 0.20/0.59    ! [X1,X0,X2] : ((sP7(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP7(X1,X0,X2)))),
% 0.20/0.59    inference(nnf_transformation,[],[f37])).
% 0.20/0.59  fof(f770,plain,(
% 0.20/0.59    ( ! [X0] : (~r2_hidden(sK17(sK13,sK12,X0),sK14) | sP7(sK13,sK12,X0)) ) | (~spl19_4 | ~spl19_5 | ~spl19_6 | ~spl19_7)),
% 0.20/0.59    inference(subsumption_resolution,[],[f769,f120])).
% 0.20/0.59  fof(f120,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) | sP7(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f72])).
% 0.20/0.59  fof(f769,plain,(
% 0.20/0.59    ( ! [X0] : (sP7(sK13,sK12,X0) | ~r2_hidden(sK17(sK13,sK12,X0),sK14) | ~m1_subset_1(sK17(sK13,sK12,X0),u1_struct_0(sK12))) ) | (~spl19_4 | ~spl19_5 | ~spl19_6 | ~spl19_7)),
% 0.20/0.59    inference(subsumption_resolution,[],[f768,f83])).
% 0.20/0.59  fof(f768,plain,(
% 0.20/0.59    ( ! [X0] : (v2_struct_0(sK12) | sP7(sK13,sK12,X0) | ~r2_hidden(sK17(sK13,sK12,X0),sK14) | ~m1_subset_1(sK17(sK13,sK12,X0),u1_struct_0(sK12))) ) | (~spl19_4 | ~spl19_5 | ~spl19_6 | ~spl19_7)),
% 0.20/0.59    inference(subsumption_resolution,[],[f767,f264])).
% 0.20/0.59  fof(f264,plain,(
% 0.20/0.59    v6_lattices(sK12) | ~spl19_4),
% 0.20/0.59    inference(avatar_component_clause,[],[f263])).
% 0.20/0.59  fof(f767,plain,(
% 0.20/0.59    ( ! [X0] : (~v6_lattices(sK12) | v2_struct_0(sK12) | sP7(sK13,sK12,X0) | ~r2_hidden(sK17(sK13,sK12,X0),sK14) | ~m1_subset_1(sK17(sK13,sK12,X0),u1_struct_0(sK12))) ) | (~spl19_5 | ~spl19_6 | ~spl19_7)),
% 0.20/0.59    inference(subsumption_resolution,[],[f766,f268])).
% 0.20/0.59  fof(f268,plain,(
% 0.20/0.59    v8_lattices(sK12) | ~spl19_5),
% 0.20/0.59    inference(avatar_component_clause,[],[f267])).
% 0.20/0.59  fof(f766,plain,(
% 0.20/0.59    ( ! [X0] : (~v8_lattices(sK12) | ~v6_lattices(sK12) | v2_struct_0(sK12) | sP7(sK13,sK12,X0) | ~r2_hidden(sK17(sK13,sK12,X0),sK14) | ~m1_subset_1(sK17(sK13,sK12,X0),u1_struct_0(sK12))) ) | (~spl19_6 | ~spl19_7)),
% 0.20/0.59    inference(subsumption_resolution,[],[f765,f272])).
% 0.20/0.59  fof(f272,plain,(
% 0.20/0.59    v9_lattices(sK12) | ~spl19_6),
% 0.20/0.59    inference(avatar_component_clause,[],[f271])).
% 0.20/0.59  fof(f765,plain,(
% 0.20/0.59    ( ! [X0] : (~v9_lattices(sK12) | ~v8_lattices(sK12) | ~v6_lattices(sK12) | v2_struct_0(sK12) | sP7(sK13,sK12,X0) | ~r2_hidden(sK17(sK13,sK12,X0),sK14) | ~m1_subset_1(sK17(sK13,sK12,X0),u1_struct_0(sK12))) ) | ~spl19_7),
% 0.20/0.59    inference(subsumption_resolution,[],[f764,f86])).
% 0.20/0.59  fof(f764,plain,(
% 0.20/0.59    ( ! [X0] : (~l3_lattices(sK12) | ~v9_lattices(sK12) | ~v8_lattices(sK12) | ~v6_lattices(sK12) | v2_struct_0(sK12) | sP7(sK13,sK12,X0) | ~r2_hidden(sK17(sK13,sK12,X0),sK14) | ~m1_subset_1(sK17(sK13,sK12,X0),u1_struct_0(sK12))) ) | ~spl19_7),
% 0.20/0.59    inference(subsumption_resolution,[],[f355,f87])).
% 0.20/0.59  fof(f355,plain,(
% 0.20/0.59    ( ! [X0] : (~m1_subset_1(sK13,u1_struct_0(sK12)) | ~l3_lattices(sK12) | ~v9_lattices(sK12) | ~v8_lattices(sK12) | ~v6_lattices(sK12) | v2_struct_0(sK12) | sP7(sK13,sK12,X0) | ~r2_hidden(sK17(sK13,sK12,X0),sK14) | ~m1_subset_1(sK17(sK13,sK12,X0),u1_struct_0(sK12))) ) | ~spl19_7),
% 0.20/0.59    inference(resolution,[],[f234,f276])).
% 0.20/0.59  fof(f276,plain,(
% 0.20/0.59    ( ! [X0] : (r3_lattices(sK12,sK13,X0) | ~r2_hidden(X0,sK14) | ~m1_subset_1(X0,u1_struct_0(sK12))) ) | ~spl19_7),
% 0.20/0.59    inference(avatar_component_clause,[],[f275])).
% 0.20/0.59  fof(f234,plain,(
% 0.20/0.59    ( ! [X4,X5,X3] : (~r3_lattices(X3,X4,sK17(X4,X3,X5)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v9_lattices(X3) | ~v8_lattices(X3) | ~v6_lattices(X3) | v2_struct_0(X3) | sP7(X4,X3,X5)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f231,f120])).
% 0.20/0.59  fof(f231,plain,(
% 0.20/0.59    ( ! [X4,X5,X3] : (~r3_lattices(X3,X4,sK17(X4,X3,X5)) | ~m1_subset_1(sK17(X4,X3,X5),u1_struct_0(X3)) | ~m1_subset_1(X4,u1_struct_0(X3)) | ~l3_lattices(X3) | ~v9_lattices(X3) | ~v8_lattices(X3) | ~v6_lattices(X3) | v2_struct_0(X3) | sP7(X4,X3,X5)) )),
% 0.20/0.59    inference(resolution,[],[f124,f122])).
% 0.20/0.59  fof(f122,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK17(X0,X1,X2)) | sP7(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f72])).
% 0.20/0.59  fof(f124,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f73])).
% 0.20/0.59  fof(f968,plain,(
% 0.20/0.59    spl19_7 | ~spl19_4 | ~spl19_5 | ~spl19_6 | ~spl19_11),
% 0.20/0.59    inference(avatar_split_clause,[],[f967,f797,f271,f267,f263,f275])).
% 0.20/0.59  fof(f967,plain,(
% 0.20/0.59    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK12)) | ~r2_hidden(X2,sK14) | r3_lattices(sK12,sK13,X2)) ) | (~spl19_4 | ~spl19_5 | ~spl19_6 | ~spl19_11)),
% 0.20/0.59    inference(subsumption_resolution,[],[f966,f83])).
% 0.20/0.59  fof(f966,plain,(
% 0.20/0.59    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK12)) | ~r2_hidden(X2,sK14) | r3_lattices(sK12,sK13,X2) | v2_struct_0(sK12)) ) | (~spl19_4 | ~spl19_5 | ~spl19_6 | ~spl19_11)),
% 0.20/0.59    inference(subsumption_resolution,[],[f965,f264])).
% 0.20/0.59  fof(f965,plain,(
% 0.20/0.59    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK12)) | ~r2_hidden(X2,sK14) | r3_lattices(sK12,sK13,X2) | ~v6_lattices(sK12) | v2_struct_0(sK12)) ) | (~spl19_5 | ~spl19_6 | ~spl19_11)),
% 0.20/0.59    inference(subsumption_resolution,[],[f964,f268])).
% 0.20/0.59  fof(f964,plain,(
% 0.20/0.59    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK12)) | ~r2_hidden(X2,sK14) | r3_lattices(sK12,sK13,X2) | ~v8_lattices(sK12) | ~v6_lattices(sK12) | v2_struct_0(sK12)) ) | (~spl19_6 | ~spl19_11)),
% 0.20/0.59    inference(subsumption_resolution,[],[f963,f272])).
% 0.20/0.59  fof(f963,plain,(
% 0.20/0.59    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK12)) | ~r2_hidden(X2,sK14) | r3_lattices(sK12,sK13,X2) | ~v9_lattices(sK12) | ~v8_lattices(sK12) | ~v6_lattices(sK12) | v2_struct_0(sK12)) ) | ~spl19_11),
% 0.20/0.59    inference(subsumption_resolution,[],[f962,f86])).
% 0.20/0.59  fof(f962,plain,(
% 0.20/0.59    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK12)) | ~r2_hidden(X2,sK14) | r3_lattices(sK12,sK13,X2) | ~l3_lattices(sK12) | ~v9_lattices(sK12) | ~v8_lattices(sK12) | ~v6_lattices(sK12) | v2_struct_0(sK12)) ) | ~spl19_11),
% 0.20/0.59    inference(subsumption_resolution,[],[f959,f87])).
% 0.20/0.59  fof(f959,plain,(
% 0.20/0.59    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK12)) | ~r2_hidden(X2,sK14) | r3_lattices(sK12,sK13,X2) | ~m1_subset_1(sK13,u1_struct_0(sK12)) | ~l3_lattices(sK12) | ~v9_lattices(sK12) | ~v8_lattices(sK12) | ~v6_lattices(sK12) | v2_struct_0(sK12)) ) | ~spl19_11),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f958])).
% 0.20/0.59  fof(f958,plain,(
% 0.20/0.59    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK12)) | ~r2_hidden(X2,sK14) | r3_lattices(sK12,sK13,X2) | ~m1_subset_1(X2,u1_struct_0(sK12)) | ~m1_subset_1(sK13,u1_struct_0(sK12)) | ~l3_lattices(sK12) | ~v9_lattices(sK12) | ~v8_lattices(sK12) | ~v6_lattices(sK12) | v2_struct_0(sK12)) ) | ~spl19_11),
% 0.20/0.59    inference(resolution,[],[f930,f125])).
% 0.20/0.59  fof(f930,plain,(
% 0.20/0.59    ( ! [X0] : (r1_lattices(sK12,sK13,X0) | ~m1_subset_1(X0,u1_struct_0(sK12)) | ~r2_hidden(X0,sK14)) ) | ~spl19_11),
% 0.20/0.59    inference(subsumption_resolution,[],[f929,f83])).
% 0.20/0.59  fof(f929,plain,(
% 0.20/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK12)) | r1_lattices(sK12,sK13,X0) | ~r2_hidden(X0,sK14) | v2_struct_0(sK12)) ) | ~spl19_11),
% 0.20/0.59    inference(subsumption_resolution,[],[f927,f86])).
% 0.20/0.59  fof(f927,plain,(
% 0.20/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK12)) | r1_lattices(sK12,sK13,X0) | ~l3_lattices(sK12) | ~r2_hidden(X0,sK14) | v2_struct_0(sK12)) ) | ~spl19_11),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f921])).
% 0.20/0.59  fof(f921,plain,(
% 0.20/0.59    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK12)) | r1_lattices(sK12,sK13,X0) | ~m1_subset_1(X0,u1_struct_0(sK12)) | ~l3_lattices(sK12) | ~r2_hidden(X0,sK14) | v2_struct_0(sK12)) ) | ~spl19_11),
% 0.20/0.59    inference(resolution,[],[f844,f507])).
% 0.20/0.59  fof(f507,plain,(
% 0.20/0.59    ( ! [X6,X4,X5] : (r4_lattice3(X4,X5,a_2_1_lattice3(X4,X6)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l3_lattices(X4) | ~r2_hidden(X5,X6) | v2_struct_0(X4)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f506,f116])).
% 0.20/0.59  fof(f506,plain,(
% 0.20/0.59    ( ! [X6,X4,X5] : (v2_struct_0(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l3_lattices(X4) | ~r2_hidden(X5,X6) | r4_lattice3(X4,X5,a_2_1_lattice3(X4,X6)) | ~sP6(X4,X5)) )),
% 0.20/0.59    inference(resolution,[],[f501,f111])).
% 0.20/0.59  fof(f111,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~sP5(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP6(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f63])).
% 0.20/0.59  fof(f501,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (sP5(X1,X0,a_2_1_lattice3(X0,X2)) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~r2_hidden(X1,X2)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f496])).
% 0.20/0.59  fof(f496,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (v2_struct_0(X0) | sP5(X1,X0,a_2_1_lattice3(X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~r2_hidden(X1,X2) | sP5(X1,X0,a_2_1_lattice3(X0,X2))) )),
% 0.20/0.59    inference(resolution,[],[f310,f115])).
% 0.20/0.59  fof(f115,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK16(X0,X1,X2),X0) | sP5(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f67])).
% 0.20/0.59  fof(f310,plain,(
% 0.20/0.59    ( ! [X6,X4,X2,X5,X3] : (r1_lattices(X2,sK16(X3,X4,a_2_1_lattice3(X2,X5)),X6) | v2_struct_0(X2) | sP5(X3,X4,a_2_1_lattice3(X2,X5)) | ~m1_subset_1(X6,u1_struct_0(X2)) | ~l3_lattices(X2) | ~r2_hidden(X6,X5)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f309,f304])).
% 0.20/0.59  fof(f304,plain,(
% 0.20/0.59    ( ! [X6,X4,X7,X5] : (sP8(X6,sK16(X4,X5,a_2_1_lattice3(X6,X7))) | ~l3_lattices(X6) | v2_struct_0(X6) | sP5(X4,X5,a_2_1_lattice3(X6,X7))) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f300])).
% 0.20/0.59  fof(f300,plain,(
% 0.20/0.59    ( ! [X6,X4,X7,X5] : (sP5(X4,X5,a_2_1_lattice3(X6,X7)) | ~l3_lattices(X6) | v2_struct_0(X6) | sP8(X6,sK16(X4,X5,a_2_1_lattice3(X6,X7))) | ~l3_lattices(X6) | v2_struct_0(X6)) )),
% 0.20/0.59    inference(resolution,[],[f298,f199])).
% 0.20/0.59  fof(f199,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~sP9(X0,X1,X2) | sP8(X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f198])).
% 0.20/0.59  fof(f198,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (sP8(X1,X2) | ~sP9(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1) | ~sP9(X0,X1,X2)) )),
% 0.20/0.59    inference(superposition,[],[f176,f129])).
% 0.20/0.59  fof(f176,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (sP8(X1,sK18(X0,X1,X2)) | ~sP9(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 0.20/0.59    inference(resolution,[],[f128,f123])).
% 0.20/0.59  fof(f298,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (sP9(X0,X1,sK16(X2,X3,a_2_1_lattice3(X1,X0))) | sP5(X2,X3,a_2_1_lattice3(X1,X0)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 0.20/0.59    inference(resolution,[],[f192,f132])).
% 0.20/0.59  fof(f192,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (~sP10(sK16(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0) | sP9(X0,X1,sK16(X2,X3,a_2_1_lattice3(X1,X0))) | sP5(X2,X3,a_2_1_lattice3(X1,X0))) )),
% 0.20/0.59    inference(resolution,[],[f126,f114])).
% 0.20/0.59  fof(f114,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r2_hidden(sK16(X0,X1,X2),X2) | sP5(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f67])).
% 0.20/0.59  fof(f126,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | sP9(X2,X1,X0) | ~sP10(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f74])).
% 0.20/0.59  fof(f309,plain,(
% 0.20/0.59    ( ! [X6,X4,X2,X5,X3] : (~l3_lattices(X2) | v2_struct_0(X2) | sP5(X3,X4,a_2_1_lattice3(X2,X5)) | ~m1_subset_1(X6,u1_struct_0(X2)) | r1_lattices(X2,sK16(X3,X4,a_2_1_lattice3(X2,X5)),X6) | ~r2_hidden(X6,X5) | ~sP8(X2,sK16(X3,X4,a_2_1_lattice3(X2,X5)))) )),
% 0.20/0.59    inference(resolution,[],[f301,f197])).
% 0.20/0.59  fof(f197,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X2,X3,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | r1_lattices(X2,X3,X0) | ~r2_hidden(X0,X1) | ~sP8(X2,X3)) )),
% 0.20/0.59    inference(resolution,[],[f119,f117])).
% 0.20/0.59  fof(f117,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (sP7(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | ~sP8(X0,X1)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f68])).
% 0.20/0.59  fof(f119,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X1] : (~sP7(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f72])).
% 0.20/0.59  fof(f301,plain,(
% 0.20/0.59    ( ! [X10,X8,X11,X9] : (r3_lattice3(X10,sK16(X8,X9,a_2_1_lattice3(X10,X11)),X11) | ~l3_lattices(X10) | v2_struct_0(X10) | sP5(X8,X9,a_2_1_lattice3(X10,X11))) )),
% 0.20/0.59    inference(resolution,[],[f298,f181])).
% 0.20/0.59  fof(f181,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~sP9(X0,X1,X2) | r3_lattice3(X1,X2,X0)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f180])).
% 0.20/0.59  fof(f180,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r3_lattice3(X1,X2,X0) | ~sP9(X0,X1,X2) | ~sP9(X0,X1,X2)) )),
% 0.20/0.59    inference(superposition,[],[f130,f129])).
% 0.20/0.59  fof(f130,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK18(X0,X1,X2),X0) | ~sP9(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f78])).
% 0.20/0.59  fof(f844,plain,(
% 0.20/0.59    ( ! [X0] : (~r4_lattice3(sK12,X0,a_2_1_lattice3(sK12,sK14)) | ~m1_subset_1(X0,u1_struct_0(sK12)) | r1_lattices(sK12,sK13,X0)) ) | ~spl19_11),
% 0.20/0.59    inference(resolution,[],[f817,f104])).
% 0.20/0.59  fof(f104,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f62])).
% 0.20/0.59  fof(f62,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (~r1_lattices(X1,X0,sK15(X0,X1,X2)) & r4_lattice3(X1,sK15(X0,X1,X2),X2) & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 0.20/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f60,f61])).
% 0.20/0.59  fof(f61,plain,(
% 0.20/0.59    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK15(X0,X1,X2)) & r4_lattice3(X1,sK15(X0,X1,X2),X2) & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.59    introduced(choice_axiom,[])).
% 0.20/0.59  fof(f60,plain,(
% 0.20/0.59    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP2(X0,X1,X2)))),
% 0.20/0.59    inference(rectify,[],[f59])).
% 0.20/0.59  fof(f59,plain,(
% 0.20/0.59    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP2(X2,X0,X1)))),
% 0.20/0.59    inference(nnf_transformation,[],[f30])).
% 0.20/0.59  fof(f817,plain,(
% 0.20/0.59    sP2(sK13,sK12,a_2_1_lattice3(sK12,sK14)) | ~spl19_11),
% 0.20/0.59    inference(resolution,[],[f799,f102])).
% 0.20/0.59  fof(f102,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~sP3(X0,X1,X2) | sP2(X2,X1,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f58])).
% 0.20/0.59  fof(f811,plain,(
% 0.20/0.59    spl19_12),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f810])).
% 0.20/0.59  fof(f810,plain,(
% 0.20/0.59    $false | spl19_12),
% 0.20/0.59    inference(subsumption_resolution,[],[f809,f83])).
% 0.20/0.59  fof(f809,plain,(
% 0.20/0.59    v2_struct_0(sK12) | spl19_12),
% 0.20/0.59    inference(subsumption_resolution,[],[f808,f84])).
% 0.20/0.59  fof(f808,plain,(
% 0.20/0.59    ~v10_lattices(sK12) | v2_struct_0(sK12) | spl19_12),
% 0.20/0.59    inference(subsumption_resolution,[],[f807,f85])).
% 0.20/0.59  fof(f807,plain,(
% 0.20/0.59    ~v4_lattice3(sK12) | ~v10_lattices(sK12) | v2_struct_0(sK12) | spl19_12),
% 0.20/0.59    inference(subsumption_resolution,[],[f806,f86])).
% 0.20/0.59  fof(f806,plain,(
% 0.20/0.59    ~l3_lattices(sK12) | ~v4_lattice3(sK12) | ~v10_lattices(sK12) | v2_struct_0(sK12) | spl19_12),
% 0.20/0.59    inference(subsumption_resolution,[],[f805,f87])).
% 0.20/0.59  fof(f805,plain,(
% 0.20/0.59    ~m1_subset_1(sK13,u1_struct_0(sK12)) | ~l3_lattices(sK12) | ~v4_lattice3(sK12) | ~v10_lattices(sK12) | v2_struct_0(sK12) | spl19_12),
% 0.20/0.59    inference(resolution,[],[f803,f135])).
% 0.20/0.59  fof(f803,plain,(
% 0.20/0.59    ~sP4(sK13,sK12,a_2_1_lattice3(sK12,sK14)) | spl19_12),
% 0.20/0.59    inference(avatar_component_clause,[],[f801])).
% 0.20/0.59  fof(f801,plain,(
% 0.20/0.59    spl19_12 <=> sP4(sK13,sK12,a_2_1_lattice3(sK12,sK14))),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl19_12])])).
% 0.20/0.59  fof(f804,plain,(
% 0.20/0.59    spl19_11 | ~spl19_12 | ~spl19_1),
% 0.20/0.59    inference(avatar_split_clause,[],[f795,f137,f801,f797])).
% 0.20/0.59  fof(f137,plain,(
% 0.20/0.59    spl19_1 <=> sK13 = k16_lattice3(sK12,sK14)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl19_1])])).
% 0.20/0.59  fof(f795,plain,(
% 0.20/0.59    ~sP4(sK13,sK12,a_2_1_lattice3(sK12,sK14)) | sP3(a_2_1_lattice3(sK12,sK14),sK12,sK13) | ~spl19_1),
% 0.20/0.59    inference(subsumption_resolution,[],[f794,f83])).
% 0.20/0.59  fof(f794,plain,(
% 0.20/0.59    ~sP4(sK13,sK12,a_2_1_lattice3(sK12,sK14)) | sP3(a_2_1_lattice3(sK12,sK14),sK12,sK13) | v2_struct_0(sK12) | ~spl19_1),
% 0.20/0.59    inference(subsumption_resolution,[],[f783,f86])).
% 0.20/0.59  fof(f783,plain,(
% 0.20/0.59    ~sP4(sK13,sK12,a_2_1_lattice3(sK12,sK14)) | sP3(a_2_1_lattice3(sK12,sK14),sK12,sK13) | ~l3_lattices(sK12) | v2_struct_0(sK12) | ~spl19_1),
% 0.20/0.59    inference(superposition,[],[f191,f138])).
% 0.20/0.59  fof(f138,plain,(
% 0.20/0.59    sK13 = k16_lattice3(sK12,sK14) | ~spl19_1),
% 0.20/0.59    inference(avatar_component_clause,[],[f137])).
% 0.20/0.59  fof(f191,plain,(
% 0.20/0.59    ( ! [X4,X3] : (~sP4(k16_lattice3(X3,X4),X3,a_2_1_lattice3(X3,X4)) | sP3(a_2_1_lattice3(X3,X4),X3,k16_lattice3(X3,X4)) | ~l3_lattices(X3) | v2_struct_0(X3)) )),
% 0.20/0.59    inference(superposition,[],[f133,f109])).
% 0.20/0.59  fof(f109,plain,(
% 0.20/0.59    ( ! [X0,X1] : (k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f17])).
% 0.20/0.59  fof(f17,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.59    inference(flattening,[],[f16])).
% 0.20/0.59  fof(f16,plain,(
% 0.20/0.59    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.59    inference(ennf_transformation,[],[f6])).
% 0.20/0.59  fof(f6,axiom,(
% 0.20/0.59    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)))),
% 0.20/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d22_lattice3)).
% 0.20/0.59  fof(f763,plain,(
% 0.20/0.59    ~spl19_2 | spl19_9),
% 0.20/0.59    inference(avatar_split_clause,[],[f762,f732,f141])).
% 0.20/0.59  fof(f732,plain,(
% 0.20/0.59    spl19_9 <=> sP9(sK14,sK12,sK13)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl19_9])])).
% 0.20/0.59  fof(f762,plain,(
% 0.20/0.59    ~r3_lattice3(sK12,sK13,sK14) | spl19_9),
% 0.20/0.59    inference(subsumption_resolution,[],[f748,f87])).
% 0.20/0.59  fof(f748,plain,(
% 0.20/0.59    ~r3_lattice3(sK12,sK13,sK14) | ~m1_subset_1(sK13,u1_struct_0(sK12)) | spl19_9),
% 0.20/0.59    inference(resolution,[],[f734,f134])).
% 0.20/0.59  fof(f734,plain,(
% 0.20/0.59    ~sP9(sK14,sK12,sK13) | spl19_9),
% 0.20/0.59    inference(avatar_component_clause,[],[f732])).
% 0.20/0.59  fof(f739,plain,(
% 0.20/0.59    spl19_8),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f738])).
% 0.20/0.59  fof(f738,plain,(
% 0.20/0.59    $false | spl19_8),
% 0.20/0.59    inference(subsumption_resolution,[],[f737,f83])).
% 0.20/0.59  fof(f737,plain,(
% 0.20/0.59    v2_struct_0(sK12) | spl19_8),
% 0.20/0.59    inference(subsumption_resolution,[],[f736,f86])).
% 0.20/0.59  fof(f736,plain,(
% 0.20/0.59    ~l3_lattices(sK12) | v2_struct_0(sK12) | spl19_8),
% 0.20/0.59    inference(resolution,[],[f730,f132])).
% 0.20/0.59  fof(f730,plain,(
% 0.20/0.59    ~sP10(sK13,sK12,sK14) | spl19_8),
% 0.20/0.59    inference(avatar_component_clause,[],[f728])).
% 0.20/0.59  fof(f728,plain,(
% 0.20/0.59    spl19_8 <=> sP10(sK13,sK12,sK14)),
% 0.20/0.59    introduced(avatar_definition,[new_symbols(naming,[spl19_8])])).
% 0.20/0.59  fof(f735,plain,(
% 0.20/0.59    ~spl19_8 | ~spl19_9 | spl19_1 | ~spl19_3 | ~spl19_4 | ~spl19_5 | ~spl19_6),
% 0.20/0.59    inference(avatar_split_clause,[],[f726,f271,f267,f263,f145,f137,f732,f728])).
% 0.20/0.59  fof(f726,plain,(
% 0.20/0.59    ~sP9(sK14,sK12,sK13) | ~sP10(sK13,sK12,sK14) | (spl19_1 | ~spl19_3 | ~spl19_4 | ~spl19_5 | ~spl19_6)),
% 0.20/0.59    inference(resolution,[],[f725,f127])).
% 0.20/0.59  fof(f725,plain,(
% 0.20/0.59    ~r2_hidden(sK13,a_2_1_lattice3(sK12,sK14)) | (spl19_1 | ~spl19_3 | ~spl19_4 | ~spl19_5 | ~spl19_6)),
% 0.20/0.59    inference(subsumption_resolution,[],[f724,f86])).
% 0.20/0.59  fof(f724,plain,(
% 0.20/0.59    ~l3_lattices(sK12) | ~r2_hidden(sK13,a_2_1_lattice3(sK12,sK14)) | (spl19_1 | ~spl19_3 | ~spl19_4 | ~spl19_5 | ~spl19_6)),
% 0.20/0.59    inference(subsumption_resolution,[],[f723,f83])).
% 0.20/0.59  fof(f723,plain,(
% 0.20/0.59    v2_struct_0(sK12) | ~l3_lattices(sK12) | ~r2_hidden(sK13,a_2_1_lattice3(sK12,sK14)) | (spl19_1 | ~spl19_3 | ~spl19_4 | ~spl19_5 | ~spl19_6)),
% 0.20/0.59    inference(subsumption_resolution,[],[f722,f84])).
% 0.20/0.59  fof(f722,plain,(
% 0.20/0.59    ~v10_lattices(sK12) | v2_struct_0(sK12) | ~l3_lattices(sK12) | ~r2_hidden(sK13,a_2_1_lattice3(sK12,sK14)) | (spl19_1 | ~spl19_3 | ~spl19_4 | ~spl19_5 | ~spl19_6)),
% 0.20/0.59    inference(subsumption_resolution,[],[f721,f85])).
% 0.20/0.59  fof(f721,plain,(
% 0.20/0.59    ~v4_lattice3(sK12) | ~v10_lattices(sK12) | v2_struct_0(sK12) | ~l3_lattices(sK12) | ~r2_hidden(sK13,a_2_1_lattice3(sK12,sK14)) | (spl19_1 | ~spl19_3 | ~spl19_4 | ~spl19_5 | ~spl19_6)),
% 0.20/0.59    inference(subsumption_resolution,[],[f720,f87])).
% 0.20/0.59  fof(f720,plain,(
% 0.20/0.59    ~m1_subset_1(sK13,u1_struct_0(sK12)) | ~v4_lattice3(sK12) | ~v10_lattices(sK12) | v2_struct_0(sK12) | ~l3_lattices(sK12) | ~r2_hidden(sK13,a_2_1_lattice3(sK12,sK14)) | (spl19_1 | ~spl19_3 | ~spl19_4 | ~spl19_5 | ~spl19_6)),
% 0.20/0.59    inference(subsumption_resolution,[],[f715,f139])).
% 0.20/0.59  fof(f139,plain,(
% 0.20/0.59    sK13 != k16_lattice3(sK12,sK14) | spl19_1),
% 0.20/0.59    inference(avatar_component_clause,[],[f137])).
% 0.20/0.59  fof(f715,plain,(
% 0.20/0.59    sK13 = k16_lattice3(sK12,sK14) | ~m1_subset_1(sK13,u1_struct_0(sK12)) | ~v4_lattice3(sK12) | ~v10_lattices(sK12) | v2_struct_0(sK12) | ~l3_lattices(sK12) | ~r2_hidden(sK13,a_2_1_lattice3(sK12,sK14)) | (~spl19_3 | ~spl19_4 | ~spl19_5 | ~spl19_6)),
% 0.20/0.59    inference(resolution,[],[f636,f401])).
% 0.20/0.59  fof(f401,plain,(
% 0.20/0.59    r4_lattice3(sK12,sK13,a_2_1_lattice3(sK12,sK14)) | (~spl19_3 | ~spl19_4 | ~spl19_5 | ~spl19_6)),
% 0.20/0.59    inference(subsumption_resolution,[],[f400,f165])).
% 0.20/0.59  fof(f165,plain,(
% 0.20/0.59    sP6(sK12,sK13)),
% 0.20/0.59    inference(subsumption_resolution,[],[f164,f83])).
% 0.20/0.59  fof(f164,plain,(
% 0.20/0.59    sP6(sK12,sK13) | v2_struct_0(sK12)),
% 0.20/0.59    inference(subsumption_resolution,[],[f161,f86])).
% 0.20/0.59  fof(f161,plain,(
% 0.20/0.59    sP6(sK12,sK13) | ~l3_lattices(sK12) | v2_struct_0(sK12)),
% 0.20/0.59    inference(resolution,[],[f116,f87])).
% 0.20/0.59  fof(f400,plain,(
% 0.20/0.59    r4_lattice3(sK12,sK13,a_2_1_lattice3(sK12,sK14)) | ~sP6(sK12,sK13) | (~spl19_3 | ~spl19_4 | ~spl19_5 | ~spl19_6)),
% 0.20/0.59    inference(resolution,[],[f398,f111])).
% 0.20/0.59  fof(f398,plain,(
% 0.20/0.59    sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14)) | (~spl19_3 | ~spl19_4 | ~spl19_5 | ~spl19_6)),
% 0.20/0.59    inference(subsumption_resolution,[],[f397,f83])).
% 0.20/0.59  fof(f397,plain,(
% 0.20/0.59    v2_struct_0(sK12) | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14)) | (~spl19_3 | ~spl19_4 | ~spl19_5 | ~spl19_6)),
% 0.20/0.59    inference(subsumption_resolution,[],[f396,f264])).
% 0.20/0.59  fof(f396,plain,(
% 0.20/0.59    ~v6_lattices(sK12) | v2_struct_0(sK12) | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14)) | (~spl19_3 | ~spl19_5 | ~spl19_6)),
% 0.20/0.59    inference(subsumption_resolution,[],[f395,f268])).
% 0.20/0.59  fof(f395,plain,(
% 0.20/0.59    ~v8_lattices(sK12) | ~v6_lattices(sK12) | v2_struct_0(sK12) | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14)) | (~spl19_3 | ~spl19_6)),
% 0.20/0.59    inference(subsumption_resolution,[],[f394,f272])).
% 0.20/0.59  fof(f394,plain,(
% 0.20/0.59    ~v9_lattices(sK12) | ~v8_lattices(sK12) | ~v6_lattices(sK12) | v2_struct_0(sK12) | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14)) | ~spl19_3),
% 0.20/0.59    inference(subsumption_resolution,[],[f393,f86])).
% 0.20/0.59  fof(f393,plain,(
% 0.20/0.59    ~l3_lattices(sK12) | ~v9_lattices(sK12) | ~v8_lattices(sK12) | ~v6_lattices(sK12) | v2_struct_0(sK12) | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14)) | ~spl19_3),
% 0.20/0.59    inference(subsumption_resolution,[],[f392,f87])).
% 0.20/0.59  fof(f392,plain,(
% 0.20/0.59    ~m1_subset_1(sK13,u1_struct_0(sK12)) | ~l3_lattices(sK12) | ~v9_lattices(sK12) | ~v8_lattices(sK12) | ~v6_lattices(sK12) | v2_struct_0(sK12) | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14)) | ~spl19_3),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f391])).
% 0.20/0.59  fof(f391,plain,(
% 0.20/0.59    ~m1_subset_1(sK13,u1_struct_0(sK12)) | ~l3_lattices(sK12) | ~v9_lattices(sK12) | ~v8_lattices(sK12) | ~v6_lattices(sK12) | v2_struct_0(sK12) | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14)) | sP5(sK13,sK12,a_2_1_lattice3(sK12,sK14)) | ~spl19_3),
% 0.20/0.59    inference(resolution,[],[f235,f307])).
% 0.20/0.59  fof(f307,plain,(
% 0.20/0.59    ( ! [X17,X16] : (r3_lattices(sK12,sK16(X16,X17,a_2_1_lattice3(sK12,sK14)),sK13) | sP5(X16,X17,a_2_1_lattice3(sK12,sK14))) ) | ~spl19_3),
% 0.20/0.59    inference(subsumption_resolution,[],[f306,f83])).
% 0.20/0.59  fof(f306,plain,(
% 0.20/0.59    ( ! [X17,X16] : (sP5(X16,X17,a_2_1_lattice3(sK12,sK14)) | v2_struct_0(sK12) | r3_lattices(sK12,sK16(X16,X17,a_2_1_lattice3(sK12,sK14)),sK13)) ) | ~spl19_3),
% 0.20/0.59    inference(subsumption_resolution,[],[f303,f86])).
% 0.20/0.59  fof(f303,plain,(
% 0.20/0.59    ( ! [X17,X16] : (sP5(X16,X17,a_2_1_lattice3(sK12,sK14)) | ~l3_lattices(sK12) | v2_struct_0(sK12) | r3_lattices(sK12,sK16(X16,X17,a_2_1_lattice3(sK12,sK14)),sK13)) ) | ~spl19_3),
% 0.20/0.59    inference(resolution,[],[f298,f214])).
% 0.20/0.59  fof(f214,plain,(
% 0.20/0.59    ( ! [X0] : (~sP9(sK14,sK12,X0) | r3_lattices(sK12,X0,sK13)) ) | ~spl19_3),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f213])).
% 0.20/0.59  fof(f213,plain,(
% 0.20/0.59    ( ! [X0] : (r3_lattices(sK12,X0,sK13) | ~sP9(sK14,sK12,X0) | ~sP9(sK14,sK12,X0)) ) | ~spl19_3),
% 0.20/0.59    inference(superposition,[],[f210,f129])).
% 0.20/0.59  fof(f210,plain,(
% 0.20/0.59    ( ! [X1] : (r3_lattices(sK12,sK18(sK14,sK12,X1),sK13) | ~sP9(sK14,sK12,X1)) ) | ~spl19_3),
% 0.20/0.59    inference(subsumption_resolution,[],[f207,f128])).
% 0.20/0.59  fof(f207,plain,(
% 0.20/0.59    ( ! [X1] : (~m1_subset_1(sK18(sK14,sK12,X1),u1_struct_0(sK12)) | r3_lattices(sK12,sK18(sK14,sK12,X1),sK13) | ~sP9(sK14,sK12,X1)) ) | ~spl19_3),
% 0.20/0.59    inference(resolution,[],[f204,f130])).
% 0.20/0.59  fof(f204,plain,(
% 0.20/0.59    ( ! [X0] : (~r3_lattice3(sK12,X0,sK14) | ~m1_subset_1(X0,u1_struct_0(sK12)) | r3_lattices(sK12,X0,sK13)) ) | ~spl19_3),
% 0.20/0.59    inference(resolution,[],[f79,f146])).
% 0.20/0.59  fof(f146,plain,(
% 0.20/0.59    sP0(sK13,sK12,sK14) | ~spl19_3),
% 0.20/0.59    inference(avatar_component_clause,[],[f145])).
% 0.20/0.59  fof(f79,plain,(
% 0.20/0.59    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r3_lattices(X1,X4,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f46])).
% 0.20/0.59  fof(f235,plain,(
% 0.20/0.59    ( ! [X6,X8,X7] : (~r3_lattices(X6,sK16(X7,X6,X8),X7) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~l3_lattices(X6) | ~v9_lattices(X6) | ~v8_lattices(X6) | ~v6_lattices(X6) | v2_struct_0(X6) | sP5(X7,X6,X8)) )),
% 0.20/0.59    inference(subsumption_resolution,[],[f232,f113])).
% 0.20/0.59  fof(f113,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) | sP5(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f67])).
% 0.20/0.59  fof(f232,plain,(
% 0.20/0.59    ( ! [X6,X8,X7] : (~r3_lattices(X6,sK16(X7,X6,X8),X7) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~m1_subset_1(sK16(X7,X6,X8),u1_struct_0(X6)) | ~l3_lattices(X6) | ~v9_lattices(X6) | ~v8_lattices(X6) | ~v6_lattices(X6) | v2_struct_0(X6) | sP5(X7,X6,X8)) )),
% 0.20/0.59    inference(resolution,[],[f124,f115])).
% 0.20/0.59  fof(f636,plain,(
% 0.20/0.59    ( ! [X6,X4,X5] : (~r4_lattice3(X4,X6,a_2_1_lattice3(X4,X5)) | k16_lattice3(X4,X5) = X6 | ~m1_subset_1(X6,u1_struct_0(X4)) | ~v4_lattice3(X4) | ~v10_lattices(X4) | v2_struct_0(X4) | ~l3_lattices(X4) | ~r2_hidden(X6,a_2_1_lattice3(X4,X5))) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f635])).
% 0.20/0.59  fof(f635,plain,(
% 0.20/0.59    ( ! [X6,X4,X5] : (~l3_lattices(X4) | k16_lattice3(X4,X5) = X6 | ~m1_subset_1(X6,u1_struct_0(X4)) | ~v4_lattice3(X4) | ~v10_lattices(X4) | v2_struct_0(X4) | ~r4_lattice3(X4,X6,a_2_1_lattice3(X4,X5)) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~r2_hidden(X6,a_2_1_lattice3(X4,X5)) | ~l3_lattices(X4) | v2_struct_0(X4)) )),
% 0.20/0.59    inference(resolution,[],[f334,f347])).
% 0.20/0.59  fof(f347,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (sP2(X0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f346])).
% 0.20/0.59  fof(f346,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | sP2(X0,X2,X1) | ~l3_lattices(X2) | v2_struct_0(X2) | sP2(X0,X2,X1)) )),
% 0.20/0.59    inference(resolution,[],[f342,f162])).
% 0.20/0.59  fof(f162,plain,(
% 0.20/0.59    ( ! [X4,X5,X3] : (sP6(X3,sK15(X4,X3,X5)) | ~l3_lattices(X3) | v2_struct_0(X3) | sP2(X4,X3,X5)) )),
% 0.20/0.59    inference(resolution,[],[f116,f105])).
% 0.20/0.59  fof(f105,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) | sP2(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f62])).
% 0.20/0.59  fof(f342,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~sP6(X1,sK15(X0,X1,X2)) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | sP2(X0,X1,X2)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f338])).
% 0.20/0.59  fof(f338,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X2) | ~sP6(X1,sK15(X0,X1,X2)) | sP2(X0,X1,X2) | sP2(X0,X1,X2)) )),
% 0.20/0.59    inference(resolution,[],[f217,f107])).
% 0.20/0.59  fof(f107,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK15(X0,X1,X2)) | sP2(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f62])).
% 0.20/0.59  fof(f217,plain,(
% 0.20/0.59    ( ! [X2,X0,X3,X1] : (r1_lattices(X1,X0,sK15(X2,X1,X3)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X3) | ~sP6(X1,sK15(X2,X1,X3)) | sP2(X2,X1,X3)) )),
% 0.20/0.59    inference(resolution,[],[f196,f106])).
% 0.20/0.59  fof(f106,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK15(X0,X1,X2),X2) | sP2(X0,X1,X2)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f62])).
% 0.20/0.59  fof(f334,plain,(
% 0.20/0.59    ( ! [X4,X2,X3] : (~sP2(X4,X2,a_2_1_lattice3(X2,X3)) | ~l3_lattices(X2) | k16_lattice3(X2,X3) = X4 | ~m1_subset_1(X4,u1_struct_0(X2)) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | ~r4_lattice3(X2,X4,a_2_1_lattice3(X2,X3))) )),
% 0.20/0.59    inference(resolution,[],[f254,f103])).
% 0.20/0.59  fof(f103,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (sP3(X0,X1,X2) | ~sP2(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) )),
% 0.20/0.59    inference(cnf_transformation,[],[f58])).
% 0.20/0.59  fof(f254,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~sP3(a_2_1_lattice3(X0,X1),X0,X2) | v2_struct_0(X0) | ~l3_lattices(X0) | k16_lattice3(X0,X1) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v4_lattice3(X0) | ~v10_lattices(X0)) )),
% 0.20/0.59    inference(duplicate_literal_removal,[],[f253])).
% 0.20/0.59  fof(f253,plain,(
% 0.20/0.59    ( ! [X2,X0,X1] : (~l3_lattices(X0) | v2_struct_0(X0) | ~sP3(a_2_1_lattice3(X0,X1),X0,X2) | k16_lattice3(X0,X1) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.59    inference(resolution,[],[f189,f135])).
% 0.20/0.59  fof(f189,plain,(
% 0.20/0.59    ( ! [X4,X2,X3] : (~sP4(X4,X2,a_2_1_lattice3(X2,X3)) | ~l3_lattices(X2) | v2_struct_0(X2) | ~sP3(a_2_1_lattice3(X2,X3),X2,X4) | k16_lattice3(X2,X3) = X4) )),
% 0.20/0.59    inference(superposition,[],[f109,f100])).
% 0.20/0.59  fof(f292,plain,(
% 0.20/0.59    spl19_6),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f291])).
% 0.20/0.59  fof(f291,plain,(
% 0.20/0.59    $false | spl19_6),
% 0.20/0.59    inference(subsumption_resolution,[],[f290,f84])).
% 0.20/0.59  fof(f290,plain,(
% 0.20/0.59    ~v10_lattices(sK12) | spl19_6),
% 0.20/0.59    inference(subsumption_resolution,[],[f289,f86])).
% 0.20/0.59  fof(f289,plain,(
% 0.20/0.59    ~l3_lattices(sK12) | ~v10_lattices(sK12) | spl19_6),
% 0.20/0.59    inference(subsumption_resolution,[],[f288,f83])).
% 0.20/0.59  fof(f288,plain,(
% 0.20/0.59    v2_struct_0(sK12) | ~l3_lattices(sK12) | ~v10_lattices(sK12) | spl19_6),
% 0.20/0.59    inference(resolution,[],[f273,f157])).
% 0.20/0.59  fof(f273,plain,(
% 0.20/0.59    ~v9_lattices(sK12) | spl19_6),
% 0.20/0.59    inference(avatar_component_clause,[],[f271])).
% 0.20/0.59  fof(f287,plain,(
% 0.20/0.59    spl19_5),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f286])).
% 0.20/0.59  fof(f286,plain,(
% 0.20/0.59    $false | spl19_5),
% 0.20/0.59    inference(subsumption_resolution,[],[f285,f84])).
% 0.20/0.59  fof(f285,plain,(
% 0.20/0.59    ~v10_lattices(sK12) | spl19_5),
% 0.20/0.59    inference(subsumption_resolution,[],[f284,f86])).
% 0.20/0.59  fof(f284,plain,(
% 0.20/0.59    ~l3_lattices(sK12) | ~v10_lattices(sK12) | spl19_5),
% 0.20/0.59    inference(subsumption_resolution,[],[f283,f83])).
% 0.20/0.59  fof(f283,plain,(
% 0.20/0.59    v2_struct_0(sK12) | ~l3_lattices(sK12) | ~v10_lattices(sK12) | spl19_5),
% 0.20/0.59    inference(resolution,[],[f269,f156])).
% 0.20/0.59  fof(f269,plain,(
% 0.20/0.59    ~v8_lattices(sK12) | spl19_5),
% 0.20/0.59    inference(avatar_component_clause,[],[f267])).
% 0.20/0.59  fof(f282,plain,(
% 0.20/0.59    spl19_4),
% 0.20/0.59    inference(avatar_contradiction_clause,[],[f281])).
% 0.20/0.59  fof(f281,plain,(
% 0.20/0.59    $false | spl19_4),
% 0.20/0.59    inference(subsumption_resolution,[],[f280,f84])).
% 0.20/0.59  fof(f280,plain,(
% 0.20/0.59    ~v10_lattices(sK12) | spl19_4),
% 0.20/0.59    inference(subsumption_resolution,[],[f279,f86])).
% 0.20/0.59  fof(f279,plain,(
% 0.20/0.59    ~l3_lattices(sK12) | ~v10_lattices(sK12) | spl19_4),
% 0.20/0.59    inference(subsumption_resolution,[],[f278,f83])).
% 0.20/0.59  fof(f278,plain,(
% 0.20/0.59    v2_struct_0(sK12) | ~l3_lattices(sK12) | ~v10_lattices(sK12) | spl19_4),
% 0.20/0.59    inference(resolution,[],[f265,f154])).
% 0.20/0.59  fof(f265,plain,(
% 0.20/0.59    ~v6_lattices(sK12) | spl19_4),
% 0.20/0.59    inference(avatar_component_clause,[],[f263])).
% 0.20/0.59  fof(f150,plain,(
% 0.20/0.59    spl19_1 | spl19_2),
% 0.20/0.59    inference(avatar_split_clause,[],[f88,f141,f137])).
% 0.20/0.59  fof(f88,plain,(
% 0.20/0.59    r3_lattice3(sK12,sK13,sK14) | sK13 = k16_lattice3(sK12,sK14)),
% 0.20/0.59    inference(cnf_transformation,[],[f52])).
% 0.20/0.59  fof(f149,plain,(
% 0.20/0.59    spl19_1 | spl19_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f89,f145,f137])).
% 0.20/0.59  fof(f89,plain,(
% 0.20/0.59    sP0(sK13,sK12,sK14) | sK13 = k16_lattice3(sK12,sK14)),
% 0.20/0.59    inference(cnf_transformation,[],[f52])).
% 0.20/0.59  fof(f148,plain,(
% 0.20/0.59    ~spl19_1 | ~spl19_2 | ~spl19_3),
% 0.20/0.59    inference(avatar_split_clause,[],[f90,f145,f141,f137])).
% 0.20/0.59  fof(f90,plain,(
% 0.20/0.59    ~sP0(sK13,sK12,sK14) | ~r3_lattice3(sK12,sK13,sK14) | sK13 != k16_lattice3(sK12,sK14)),
% 0.20/0.59    inference(cnf_transformation,[],[f52])).
% 0.20/0.59  % SZS output end Proof for theBenchmark
% 0.20/0.59  % (6163)------------------------------
% 0.20/0.59  % (6163)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (6163)Termination reason: Refutation
% 0.20/0.59  
% 0.20/0.59  % (6163)Memory used [KB]: 6652
% 0.20/0.59  % (6163)Time elapsed: 0.174 s
% 0.20/0.59  % (6163)------------------------------
% 0.20/0.59  % (6163)------------------------------
% 0.20/0.59  % (6158)Success in time 0.229 s
%------------------------------------------------------------------------------
