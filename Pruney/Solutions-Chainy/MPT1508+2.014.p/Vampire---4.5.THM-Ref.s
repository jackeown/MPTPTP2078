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
% DateTime   : Thu Dec  3 13:15:45 EST 2020

% Result     : Theorem 2.42s
% Output     : Refutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :  296 (1522 expanded)
%              Number of leaves         :   32 ( 513 expanded)
%              Depth                    :   38
%              Number of atoms          : 1553 (9528 expanded)
%              Number of equality atoms :   89 (1098 expanded)
%              Maximal formula depth    :   20 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1836,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1068,f1121,f1141,f1144,f1206,f1835])).

fof(f1835,plain,(
    ~ spl19_6 ),
    inference(avatar_contradiction_clause,[],[f1834])).

fof(f1834,plain,
    ( $false
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1833,f192])).

fof(f192,plain,(
    sP2(sK12,sK11) ),
    inference(subsumption_resolution,[],[f191,f75])).

fof(f75,plain,(
    ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( sK12 != k16_lattice3(sK11,sK13)
    & r3_lattice3(sK11,sK12,sK13)
    & r2_hidden(sK12,sK13)
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
              ( k16_lattice3(sK11,X2) != X1
              & r3_lattice3(sK11,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK11)) )
      & l3_lattices(sK11)
      & v4_lattice3(sK11)
      & v10_lattices(sK11)
      & ~ v2_struct_0(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k16_lattice3(sK11,X2) != X1
            & r3_lattice3(sK11,X1,X2)
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK11)) )
   => ( ? [X2] :
          ( k16_lattice3(sK11,X2) != sK12
          & r3_lattice3(sK11,sK12,X2)
          & r2_hidden(sK12,X2) )
      & m1_subset_1(sK12,u1_struct_0(sK11)) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,
    ( ? [X2] :
        ( k16_lattice3(sK11,X2) != sK12
        & r3_lattice3(sK11,sK12,X2)
        & r2_hidden(sK12,X2) )
   => ( sK12 != k16_lattice3(sK11,sK13)
      & r3_lattice3(sK11,sK12,sK13)
      & r2_hidden(sK12,sK13) ) ),
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

fof(f191,plain,
    ( sP2(sK12,sK11)
    | v2_struct_0(sK11) ),
    inference(subsumption_resolution,[],[f190,f76])).

fof(f76,plain,(
    v10_lattices(sK11) ),
    inference(cnf_transformation,[],[f45])).

fof(f190,plain,
    ( sP2(sK12,sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11) ),
    inference(subsumption_resolution,[],[f189,f77])).

fof(f77,plain,(
    v4_lattice3(sK11) ),
    inference(cnf_transformation,[],[f45])).

fof(f189,plain,
    ( sP2(sK12,sK11)
    | ~ v4_lattice3(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11) ),
    inference(subsumption_resolution,[],[f183,f78])).

fof(f78,plain,(
    l3_lattices(sK11) ),
    inference(cnf_transformation,[],[f45])).

fof(f183,plain,
    ( sP2(sK12,sK11)
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11) ),
    inference(resolution,[],[f94,f79])).

fof(f79,plain,(
    m1_subset_1(sK12,u1_struct_0(sK11)) ),
    inference(cnf_transformation,[],[f45])).

fof(f94,plain,(
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
    inference(definition_folding,[],[f17,f28,f27,f26])).

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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f1833,plain,
    ( ~ sP2(sK12,sK11)
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1829,f81])).

fof(f81,plain,(
    r3_lattice3(sK11,sK12,sK13) ),
    inference(cnf_transformation,[],[f45])).

fof(f1829,plain,
    ( ~ r3_lattice3(sK11,sK12,sK13)
    | ~ sP2(sK12,sK11)
    | ~ spl19_6 ),
    inference(trivial_inequality_removal,[],[f1826])).

fof(f1826,plain,
    ( ~ r3_lattice3(sK11,sK12,sK13)
    | sK12 != sK12
    | ~ sP2(sK12,sK11)
    | ~ spl19_6 ),
    inference(resolution,[],[f1824,f168])).

fof(f168,plain,(
    ! [X6] :
      ( ~ sP0(X6,sK11,sK13)
      | ~ r3_lattice3(sK11,X6,sK13)
      | sK12 != X6
      | ~ sP2(X6,sK11) ) ),
    inference(resolution,[],[f89,f157])).

fof(f157,plain,(
    ! [X0] :
      ( ~ sP1(sK13,sK11,X0)
      | sK12 != X0
      | ~ sP2(X0,sK11) ) ),
    inference(superposition,[],[f82,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X1,X2) = X0
      | ~ sP1(X2,X1,X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k16_lattice3(X1,X2) = X0
            | ~ sP1(X2,X1,X0) )
          & ( sP1(X2,X1,X0)
            | k16_lattice3(X1,X2) != X0 ) )
      | ~ sP2(X0,X1) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( ( k16_lattice3(X0,X2) = X1
            | ~ sP1(X2,X0,X1) )
          & ( sP1(X2,X0,X1)
            | k16_lattice3(X0,X2) != X1 ) )
      | ~ sP2(X1,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f82,plain,(
    sK12 != k16_lattice3(sK11,sK13) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,X2)
      | ~ sP0(X2,X1,X0)
      | ~ r3_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ~ sP0(X2,X1,X0)
        | ~ r3_lattice3(X1,X2,X0) )
      & ( ( sP0(X2,X1,X0)
          & r3_lattice3(X1,X2,X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ~ sP0(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP0(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ( sP1(X2,X0,X1)
        | ~ sP0(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP0(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP1(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f1824,plain,
    ( sP0(sK12,sK11,sK13)
    | ~ spl19_6 ),
    inference(duplicate_literal_removal,[],[f1823])).

fof(f1823,plain,
    ( sP0(sK12,sK11,sK13)
    | sP0(sK12,sK11,sK13)
    | ~ spl19_6 ),
    inference(resolution,[],[f1822,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK14(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r3_lattices(X1,sK14(X0,X1,X2),X0)
          & r3_lattice3(X1,sK14(X0,X1,X2),X2)
          & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r3_lattices(X1,X4,X0)
            | ~ r3_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X1,X3,X0)
          & r3_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r3_lattices(X1,sK14(X0,X1,X2),X0)
        & r3_lattice3(X1,sK14(X0,X1,X2),X2)
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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

fof(f1822,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK11,sK14(sK12,sK11,X0),sK13)
        | sP0(sK12,sK11,X0) )
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1821,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1821,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK11,sK14(sK12,sK11,X0),sK13)
        | ~ m1_subset_1(sK14(sK12,sK11,X0),u1_struct_0(sK11))
        | sP0(sK12,sK11,X0) )
    | ~ spl19_6 ),
    inference(resolution,[],[f1814,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X1,sK14(X0,X1,X2),X0)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1814,plain,
    ( ! [X0] :
        ( r3_lattices(sK11,X0,sK12)
        | ~ r3_lattice3(sK11,X0,sK13)
        | ~ m1_subset_1(X0,u1_struct_0(sK11)) )
    | ~ spl19_6 ),
    inference(resolution,[],[f1812,f125])).

fof(f125,plain,(
    ! [X0,X3,X1] :
      ( sP9(X0,X1,X3)
      | ~ r3_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( sP9(X0,X1,X2)
      | ~ r3_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f72,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK18(X0,X1,X2),X0)
        & sK18(X0,X1,X2) = X2
        & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
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
    inference(rectify,[],[f71])).

fof(f71,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( sP9(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f1812,plain,
    ( ! [X0] :
        ( ~ sP9(sK13,sK11,X0)
        | r3_lattices(sK11,X0,sK12) )
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1811,f75])).

fof(f1811,plain,
    ( ! [X0] :
        ( ~ sP9(sK13,sK11,X0)
        | r3_lattices(sK11,X0,sK12)
        | v2_struct_0(sK11) )
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1809,f78])).

fof(f1809,plain,
    ( ! [X0] :
        ( ~ sP9(sK13,sK11,X0)
        | r3_lattices(sK11,X0,sK12)
        | ~ l3_lattices(sK11)
        | v2_struct_0(sK11) )
    | ~ spl19_6 ),
    inference(resolution,[],[f1808,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( sP10(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( sP10(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f25,f40,f39])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

fof(f1808,plain,
    ( ! [X0] :
        ( ~ sP10(X0,sK11,sK13)
        | ~ sP9(sK13,sK11,X0)
        | r3_lattices(sK11,X0,sK12) )
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1804,f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ sP9(X0,X1,X2)
      | m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f150])).

fof(f150,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X1))
      | ~ sP9(X0,X1,X2)
      | ~ sP9(X0,X1,X2) ) ),
    inference(superposition,[],[f118,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( sK18(X0,X1,X2) = X2
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1))
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f1804,plain,
    ( ! [X0] :
        ( r3_lattices(sK11,X0,sK12)
        | ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ sP9(sK13,sK11,X0)
        | ~ sP10(X0,sK11,sK13) )
    | ~ spl19_6 ),
    inference(resolution,[],[f1753,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ sP9(X2,X1,X0)
      | ~ sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ~ sP9(X2,X1,X0) )
        & ( sP9(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ sP10(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f1753,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | r3_lattices(sK11,X0,sK12)
        | ~ m1_subset_1(X0,u1_struct_0(sK11)) )
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1752,f76])).

fof(f1752,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK11))
        | r3_lattices(sK11,X0,sK12)
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ v10_lattices(sK11) )
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1751,f78])).

fof(f1751,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK11))
        | r3_lattices(sK11,X0,sK12)
        | ~ l3_lattices(sK11)
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ v10_lattices(sK11) )
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1750,f77])).

fof(f1750,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK11))
        | r3_lattices(sK11,X0,sK12)
        | ~ v4_lattice3(sK11)
        | ~ l3_lattices(sK11)
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ v10_lattices(sK11) )
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1748,f75])).

fof(f1748,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK11))
        | r3_lattices(sK11,X0,sK12)
        | v2_struct_0(sK11)
        | ~ v4_lattice3(sK11)
        | ~ l3_lattices(sK11)
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ v10_lattices(sK11) )
    | ~ spl19_6 ),
    inference(duplicate_literal_removal,[],[f1738])).

fof(f1738,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK11))
        | r3_lattices(sK11,X0,sK12)
        | v2_struct_0(sK11)
        | ~ v4_lattice3(sK11)
        | ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ l3_lattices(sK11)
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ v10_lattices(sK11) )
    | ~ spl19_6 ),
    inference(resolution,[],[f1277,f501])).

fof(f501,plain,(
    ! [X6,X4,X5] :
      ( r3_lattice3(X4,X5,a_2_2_lattice3(X4,X6))
      | v2_struct_0(X4)
      | ~ v4_lattice3(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ r2_hidden(X5,X6)
      | ~ v10_lattices(X4) ) ),
    inference(subsumption_resolution,[],[f500,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP6(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP6(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f34,f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( sP5(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP5(X1,X0,X2) )
      | ~ sP6(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

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

fof(f500,plain,(
    ! [X6,X4,X5] :
      ( ~ v10_lattices(X4)
      | v2_struct_0(X4)
      | ~ v4_lattice3(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ r2_hidden(X5,X6)
      | r3_lattice3(X4,X5,a_2_2_lattice3(X4,X6))
      | ~ sP6(X4,X5) ) ),
    inference(resolution,[],[f497,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X1,X0,X2)
      | r3_lattice3(X0,X1,X2)
      | ~ sP6(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP5(X1,X0,X2) )
          & ( sP5(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP6(X0,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f497,plain,(
    ! [X6,X7,X5] :
      ( sP5(X6,X5,a_2_2_lattice3(X5,X7))
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | ~ v4_lattice3(X5)
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ l3_lattices(X5)
      | ~ r2_hidden(X6,X7) ) ),
    inference(duplicate_literal_removal,[],[f496])).

fof(f496,plain,(
    ! [X6,X7,X5] :
      ( ~ v4_lattice3(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | sP5(X6,X5,a_2_2_lattice3(X5,X7))
      | ~ m1_subset_1(X6,u1_struct_0(X5))
      | ~ l3_lattices(X5)
      | ~ r2_hidden(X6,X7)
      | sP5(X6,X5,a_2_2_lattice3(X5,X7)) ) ),
    inference(resolution,[],[f339,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK16(X0,X1,X2))
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK16(X0,X1,X2))
          & r2_hidden(sK16(X0,X1,X2),X2)
          & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f62,f63])).

fof(f63,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK16(X0,X1,X2))
        & r2_hidden(sK16(X0,X1,X2),X2)
        & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X1,X0,X2] :
      ( ( sP5(X1,X0,X2)
        | ? [X3] :
            ( ~ r1_lattices(X0,X1,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X1,X3)
            | ~ r2_hidden(X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP5(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f339,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( r1_lattices(X5,X9,sK16(X6,X7,a_2_2_lattice3(X5,X8)))
      | ~ v4_lattice3(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | sP5(X6,X7,a_2_2_lattice3(X5,X8))
      | ~ m1_subset_1(X9,u1_struct_0(X5))
      | ~ l3_lattices(X5)
      | ~ r2_hidden(X9,X8) ) ),
    inference(subsumption_resolution,[],[f337,f292])).

fof(f292,plain,(
    ! [X6,X4,X7,X5] :
      ( sP4(X6,sK16(X4,X5,a_2_2_lattice3(X6,X7)))
      | ~ l3_lattices(X6)
      | ~ v4_lattice3(X6)
      | ~ v10_lattices(X6)
      | v2_struct_0(X6)
      | sP5(X4,X5,a_2_2_lattice3(X6,X7)) ) ),
    inference(duplicate_literal_removal,[],[f287])).

fof(f287,plain,(
    ! [X6,X4,X7,X5] :
      ( sP5(X4,X5,a_2_2_lattice3(X6,X7))
      | ~ l3_lattices(X6)
      | ~ v4_lattice3(X6)
      | ~ v10_lattices(X6)
      | v2_struct_0(X6)
      | sP4(X6,sK16(X4,X5,a_2_2_lattice3(X6,X7)))
      | ~ l3_lattices(X6)
      | v2_struct_0(X6) ) ),
    inference(resolution,[],[f285,f197])).

fof(f197,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | sP4(X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( sP4(X1,X2)
      | ~ sP7(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP7(X0,X1,X2) ) ),
    inference(superposition,[],[f143,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( sK17(X0,X1,X2) = X2
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r4_lattice3(X1,sK17(X0,X1,X2),X0)
          & sK17(X0,X1,X2) = X2
          & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK17(X0,X1,X2),X0)
        & sK17(X0,X1,X2) = X2
        & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r4_lattice3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ( sP7(X2,X1,X0)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP7(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( sP7(X2,X1,X0)
    <=> ? [X3] :
          ( r4_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f143,plain,(
    ! [X4,X5,X3] :
      ( sP4(X4,sK17(X3,X4,X5))
      | ~ sP7(X3,X4,X5)
      | ~ l3_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f111,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP4(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP4(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f31,f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP3(X1,X0,X2) )
      | ~ sP4(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

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

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f285,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X0,X1,sK16(X2,X3,a_2_2_lattice3(X1,X0)))
      | sP5(X2,X3,a_2_2_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f176,f115])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( sP8(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( sP8(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f23,f37,f36])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> sP7(X2,X1,X0) )
      | ~ sP8(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f176,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ sP8(sK16(X6,X7,a_2_2_lattice3(X5,X4)),X5,X4)
      | sP7(X4,X5,sK16(X6,X7,a_2_2_lattice3(X5,X4)))
      | sP5(X6,X7,a_2_2_lattice3(X5,X4)) ) ),
    inference(resolution,[],[f109,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK16(X0,X1,X2),X2)
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | sP7(X2,X1,X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ~ sP7(X2,X1,X0) )
        & ( sP7(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ sP8(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f337,plain,(
    ! [X6,X8,X7,X5,X9] :
      ( ~ l3_lattices(X5)
      | ~ v4_lattice3(X5)
      | ~ v10_lattices(X5)
      | v2_struct_0(X5)
      | sP5(X6,X7,a_2_2_lattice3(X5,X8))
      | ~ m1_subset_1(X9,u1_struct_0(X5))
      | r1_lattices(X5,X9,sK16(X6,X7,a_2_2_lattice3(X5,X8)))
      | ~ r2_hidden(X9,X8)
      | ~ sP4(X5,sK16(X6,X7,a_2_2_lattice3(X5,X8))) ) ),
    inference(resolution,[],[f289,f199])).

fof(f199,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_lattice3(X2,X3,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | r1_lattices(X2,X0,X3)
      | ~ r2_hidden(X0,X1)
      | ~ sP4(X2,X3) ) ),
    inference(resolution,[],[f97,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | ~ r4_lattice3(X0,X1,X2)
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
    inference(nnf_transformation,[],[f31])).

fof(f97,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK15(X0,X1,X2),X0)
          & r2_hidden(sK15(X0,X1,X2),X2)
          & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f57,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK15(X0,X1,X2),X0)
        & r2_hidden(sK15(X0,X1,X2),X2)
        & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) ) ),
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
    inference(nnf_transformation,[],[f30])).

fof(f289,plain,(
    ! [X14,X12,X15,X13] :
      ( r4_lattice3(X14,sK16(X12,X13,a_2_2_lattice3(X14,X15)),X15)
      | ~ l3_lattices(X14)
      | ~ v4_lattice3(X14)
      | ~ v10_lattices(X14)
      | v2_struct_0(X14)
      | sP5(X12,X13,a_2_2_lattice3(X14,X15)) ) ),
    inference(resolution,[],[f285,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | r4_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,X2,X0)
      | ~ sP7(X0,X1,X2)
      | ~ sP7(X0,X1,X2) ) ),
    inference(superposition,[],[f113,f112])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK17(X0,X1,X2),X0)
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f1277,plain,
    ( ! [X2] :
        ( ~ r3_lattice3(sK11,X2,a_2_2_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))
        | ~ m1_subset_1(X2,u1_struct_0(sK11))
        | r3_lattices(sK11,X2,sK12) )
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1276,f75])).

fof(f1276,plain,
    ( ! [X2] :
        ( r3_lattices(sK11,X2,sK12)
        | ~ m1_subset_1(X2,u1_struct_0(sK11))
        | ~ r3_lattice3(sK11,X2,a_2_2_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))
        | v2_struct_0(sK11) )
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1275,f76])).

fof(f1275,plain,
    ( ! [X2] :
        ( r3_lattices(sK11,X2,sK12)
        | ~ m1_subset_1(X2,u1_struct_0(sK11))
        | ~ r3_lattice3(sK11,X2,a_2_2_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))
        | ~ v10_lattices(sK11)
        | v2_struct_0(sK11) )
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1274,f77])).

fof(f1274,plain,
    ( ! [X2] :
        ( r3_lattices(sK11,X2,sK12)
        | ~ m1_subset_1(X2,u1_struct_0(sK11))
        | ~ r3_lattice3(sK11,X2,a_2_2_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))
        | ~ v4_lattice3(sK11)
        | ~ v10_lattices(sK11)
        | v2_struct_0(sK11) )
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1273,f78])).

fof(f1273,plain,
    ( ! [X2] :
        ( r3_lattices(sK11,X2,sK12)
        | ~ m1_subset_1(X2,u1_struct_0(sK11))
        | ~ r3_lattice3(sK11,X2,a_2_2_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))
        | ~ l3_lattices(sK11)
        | ~ v4_lattice3(sK11)
        | ~ v10_lattices(sK11)
        | v2_struct_0(sK11) )
    | ~ spl19_6 ),
    inference(subsumption_resolution,[],[f1231,f192])).

fof(f1231,plain,
    ( ! [X2] :
        ( r3_lattices(sK11,X2,sK12)
        | ~ m1_subset_1(X2,u1_struct_0(sK11))
        | ~ r3_lattice3(sK11,X2,a_2_2_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))
        | ~ sP2(sK12,sK11)
        | ~ l3_lattices(sK11)
        | ~ v4_lattice3(sK11)
        | ~ v10_lattices(sK11)
        | v2_struct_0(sK11) )
    | ~ spl19_6 ),
    inference(superposition,[],[f234,f1059])).

fof(f1059,plain,
    ( sK12 = k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))
    | ~ spl19_6 ),
    inference(avatar_component_clause,[],[f1057])).

fof(f1057,plain,
    ( spl19_6
  <=> sK12 = k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_6])])).

fof(f234,plain,(
    ! [X6,X4,X5] :
      ( r3_lattices(X4,X6,k15_lattice3(X4,X5))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ r3_lattice3(X4,X6,a_2_2_lattice3(X4,X5))
      | ~ sP2(k15_lattice3(X4,X5),X4)
      | ~ l3_lattices(X4)
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(superposition,[],[f207,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1))
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
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

fof(f207,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k16_lattice3(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP2(k16_lattice3(X0,X2),X0) ) ),
    inference(resolution,[],[f90,f154])).

fof(f154,plain,(
    ! [X0,X1] :
      ( sP0(k16_lattice3(X0,X1),X0,X1)
      | ~ sP2(k16_lattice3(X0,X1),X0) ) ),
    inference(resolution,[],[f123,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | sP0(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f123,plain,(
    ! [X2,X1] :
      ( sP1(X2,X1,k16_lattice3(X1,X2))
      | ~ sP2(k16_lattice3(X1,X2),X1) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( sP1(X2,X1,X0)
      | k16_lattice3(X1,X2) != X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | ~ r3_lattice3(X1,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r3_lattices(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f1206,plain,(
    spl19_5 ),
    inference(avatar_contradiction_clause,[],[f1205])).

fof(f1205,plain,
    ( $false
    | spl19_5 ),
    inference(subsumption_resolution,[],[f1204,f79])).

fof(f1204,plain,
    ( ~ m1_subset_1(sK12,u1_struct_0(sK11))
    | spl19_5 ),
    inference(subsumption_resolution,[],[f1197,f80])).

fof(f80,plain,(
    r2_hidden(sK12,sK13) ),
    inference(cnf_transformation,[],[f45])).

fof(f1197,plain,
    ( ~ r2_hidden(sK12,sK13)
    | ~ m1_subset_1(sK12,u1_struct_0(sK11))
    | spl19_5 ),
    inference(resolution,[],[f1190,f81])).

fof(f1190,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK11,X0,sK13)
        | ~ r2_hidden(X0,sK13)
        | ~ m1_subset_1(X0,u1_struct_0(sK11)) )
    | spl19_5 ),
    inference(resolution,[],[f1179,f125])).

fof(f1179,plain,
    ( ! [X0] :
        ( ~ sP9(sK13,sK11,X0)
        | ~ r2_hidden(X0,sK13) )
    | spl19_5 ),
    inference(subsumption_resolution,[],[f1178,f75])).

fof(f1178,plain,
    ( ! [X0] :
        ( ~ sP9(sK13,sK11,X0)
        | ~ r2_hidden(X0,sK13)
        | v2_struct_0(sK11) )
    | spl19_5 ),
    inference(subsumption_resolution,[],[f1177,f78])).

fof(f1177,plain,
    ( ! [X0] :
        ( ~ sP9(sK13,sK11,X0)
        | ~ r2_hidden(X0,sK13)
        | ~ l3_lattices(sK11)
        | v2_struct_0(sK11) )
    | spl19_5 ),
    inference(resolution,[],[f1176,f122])).

fof(f1176,plain,
    ( ! [X0] :
        ( ~ sP10(X0,sK11,sK13)
        | ~ sP9(sK13,sK11,X0)
        | ~ r2_hidden(X0,sK13) )
    | spl19_5 ),
    inference(subsumption_resolution,[],[f1173,f151])).

fof(f1173,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK13)
        | ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ sP9(sK13,sK11,X0)
        | ~ sP10(X0,sK11,sK13) )
    | spl19_5 ),
    inference(resolution,[],[f1163,f117])).

fof(f1163,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ r2_hidden(X0,sK13)
        | ~ m1_subset_1(X0,u1_struct_0(sK11)) )
    | spl19_5 ),
    inference(subsumption_resolution,[],[f1162,f75])).

fof(f1162,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK13)
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ m1_subset_1(X0,u1_struct_0(sK11))
        | v2_struct_0(sK11) )
    | spl19_5 ),
    inference(subsumption_resolution,[],[f1161,f78])).

fof(f1161,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK13)
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ l3_lattices(sK11)
        | v2_struct_0(sK11) )
    | spl19_5 ),
    inference(duplicate_literal_removal,[],[f1157])).

fof(f1157,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK13)
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ r2_hidden(X0,sK13)
        | ~ l3_lattices(sK11)
        | v2_struct_0(sK11)
        | ~ m1_subset_1(X0,u1_struct_0(sK11)) )
    | spl19_5 ),
    inference(resolution,[],[f1132,f360])).

fof(f360,plain,(
    ! [X6,X4,X5] :
      ( r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | ~ m1_subset_1(X4,u1_struct_0(X5)) ) ),
    inference(subsumption_resolution,[],[f359,f101])).

fof(f359,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(X5))
      | ~ r2_hidden(X4,X6)
      | ~ l3_lattices(X5)
      | v2_struct_0(X5)
      | r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6))
      | ~ sP4(X5,X4) ) ),
    inference(resolution,[],[f357,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f357,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(subsumption_resolution,[],[f356,f138])).

fof(f138,plain,(
    ! [X4,X5,X3] :
      ( sP6(X3,sK15(X4,X3,X5))
      | ~ l3_lattices(X3)
      | v2_struct_0(X3)
      | sP3(X4,X3,X5) ) ),
    inference(resolution,[],[f108,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f356,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ sP6(X2,sK15(X0,X2,a_2_1_lattice3(X2,X1)))
      | sP3(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f355])).

fof(f355,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ sP6(X2,sK15(X0,X2,a_2_1_lattice3(X2,X1)))
      | sP3(X0,X2,a_2_1_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP3(X0,X2,a_2_1_lattice3(X2,X1)) ) ),
    inference(resolution,[],[f225,f298])).

fof(f298,plain,(
    ! [X14,X12,X15,X13] :
      ( r3_lattice3(X14,sK15(X12,X13,a_2_1_lattice3(X14,X15)),X15)
      | ~ l3_lattices(X14)
      | v2_struct_0(X14)
      | sP3(X12,X13,a_2_1_lattice3(X14,X15)) ) ),
    inference(resolution,[],[f294,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ sP9(X0,X1,X2)
      | r3_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f152])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,X2,X0)
      | ~ sP9(X0,X1,X2)
      | ~ sP9(X0,X1,X2) ) ),
    inference(superposition,[],[f120,f119])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK18(X0,X1,X2),X0)
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f294,plain,(
    ! [X2,X0,X3,X1] :
      ( sP9(X0,X1,sK15(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP3(X2,X3,a_2_1_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f179,f122])).

fof(f179,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP10(sK15(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0)
      | sP9(X0,X1,sK15(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP3(X2,X3,a_2_1_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f116,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK15(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | sP9(X2,X1,X0)
      | ~ sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f225,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X1,sK15(X0,X1,X3),X2)
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ sP6(X1,sK15(X0,X1,X3))
      | sP3(X0,X1,X3) ) ),
    inference(resolution,[],[f206,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK15(X0,X1,X2),X0)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f206,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X2,X3,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ r3_lattice3(X2,X3,X1)
      | ~ sP6(X2,X3) ) ),
    inference(resolution,[],[f104,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( sP5(X1,X0,X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP6(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f104,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f1132,plain,
    ( ! [X0] :
        ( ~ r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13))
        | ~ r2_hidden(X0,sK13)
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ m1_subset_1(X0,u1_struct_0(sK11)) )
    | spl19_5 ),
    inference(subsumption_resolution,[],[f1131,f75])).

fof(f1131,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK13)
        | ~ r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ m1_subset_1(X0,u1_struct_0(sK11))
        | v2_struct_0(sK11) )
    | spl19_5 ),
    inference(subsumption_resolution,[],[f1130,f76])).

fof(f1130,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK13)
        | ~ r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ v10_lattices(sK11)
        | v2_struct_0(sK11) )
    | spl19_5 ),
    inference(subsumption_resolution,[],[f1129,f77])).

fof(f1129,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK13)
        | ~ r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ v4_lattice3(sK11)
        | ~ v10_lattices(sK11)
        | v2_struct_0(sK11) )
    | spl19_5 ),
    inference(subsumption_resolution,[],[f1128,f78])).

fof(f1128,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK13)
        | ~ r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ l3_lattices(sK11)
        | ~ v4_lattice3(sK11)
        | ~ v10_lattices(sK11)
        | v2_struct_0(sK11) )
    | spl19_5 ),
    inference(superposition,[],[f1055,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X2) = X1
      | ~ r4_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
              ( ( r4_lattice3(X0,X1,X2)
                & r2_hidden(X1,X2) )
             => k15_lattice3(X0,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).

fof(f1055,plain,
    ( ~ r2_hidden(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK13)
    | spl19_5 ),
    inference(avatar_component_clause,[],[f1053])).

fof(f1053,plain,
    ( spl19_5
  <=> r2_hidden(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK13) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_5])])).

fof(f1144,plain,
    ( spl19_8
    | ~ spl19_4 ),
    inference(avatar_split_clause,[],[f1143,f1049,f1065])).

fof(f1065,plain,
    ( spl19_8
  <=> sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_8])])).

fof(f1049,plain,
    ( spl19_4
  <=> m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).

fof(f1143,plain,
    ( sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f1142,f75])).

fof(f1142,plain,
    ( sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))
    | v2_struct_0(sK11)
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f1134,f78])).

fof(f1134,plain,
    ( sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))
    | ~ l3_lattices(sK11)
    | v2_struct_0(sK11)
    | ~ spl19_4 ),
    inference(resolution,[],[f1050,f108])).

fof(f1050,plain,
    ( m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11))
    | ~ spl19_4 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f1141,plain,
    ( spl19_7
    | ~ spl19_4 ),
    inference(avatar_split_clause,[],[f1140,f1049,f1061])).

fof(f1061,plain,
    ( spl19_7
  <=> sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl19_7])])).

fof(f1140,plain,
    ( sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11)
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f1139,f75])).

fof(f1139,plain,
    ( sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11)
    | v2_struct_0(sK11)
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f1138,f76])).

fof(f1138,plain,
    ( sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f1137,f77])).

fof(f1137,plain,
    ( sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11)
    | ~ v4_lattice3(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | ~ spl19_4 ),
    inference(subsumption_resolution,[],[f1133,f78])).

fof(f1133,plain,
    ( sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11)
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | ~ spl19_4 ),
    inference(resolution,[],[f1050,f94])).

fof(f1121,plain,(
    spl19_4 ),
    inference(avatar_contradiction_clause,[],[f1120])).

fof(f1120,plain,
    ( $false
    | spl19_4 ),
    inference(subsumption_resolution,[],[f1119,f79])).

fof(f1119,plain,
    ( ~ m1_subset_1(sK12,u1_struct_0(sK11))
    | spl19_4 ),
    inference(subsumption_resolution,[],[f1112,f80])).

fof(f1112,plain,
    ( ~ r2_hidden(sK12,sK13)
    | ~ m1_subset_1(sK12,u1_struct_0(sK11))
    | spl19_4 ),
    inference(resolution,[],[f1105,f81])).

fof(f1105,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK11,X0,sK13)
        | ~ r2_hidden(X0,sK13)
        | ~ m1_subset_1(X0,u1_struct_0(sK11)) )
    | spl19_4 ),
    inference(resolution,[],[f1104,f125])).

fof(f1104,plain,
    ( ! [X0] :
        ( ~ sP9(sK13,sK11,X0)
        | ~ r2_hidden(X0,sK13) )
    | spl19_4 ),
    inference(subsumption_resolution,[],[f1103,f75])).

fof(f1103,plain,
    ( ! [X0] :
        ( ~ sP9(sK13,sK11,X0)
        | ~ r2_hidden(X0,sK13)
        | v2_struct_0(sK11) )
    | spl19_4 ),
    inference(subsumption_resolution,[],[f1102,f78])).

fof(f1102,plain,
    ( ! [X0] :
        ( ~ sP9(sK13,sK11,X0)
        | ~ r2_hidden(X0,sK13)
        | ~ l3_lattices(sK11)
        | v2_struct_0(sK11) )
    | spl19_4 ),
    inference(resolution,[],[f1101,f122])).

fof(f1101,plain,
    ( ! [X0] :
        ( ~ sP10(X0,sK11,sK13)
        | ~ sP9(sK13,sK11,X0)
        | ~ r2_hidden(X0,sK13) )
    | spl19_4 ),
    inference(subsumption_resolution,[],[f1098,f151])).

fof(f1098,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ r2_hidden(X0,sK13)
        | ~ sP9(sK13,sK11,X0)
        | ~ sP10(X0,sK11,sK13) )
    | spl19_4 ),
    inference(resolution,[],[f1083,f117])).

fof(f1083,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ r2_hidden(X0,sK13) )
    | spl19_4 ),
    inference(subsumption_resolution,[],[f1082,f75])).

fof(f1082,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ r2_hidden(X0,sK13)
        | v2_struct_0(sK11) )
    | spl19_4 ),
    inference(subsumption_resolution,[],[f1081,f78])).

fof(f1081,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ r2_hidden(X0,sK13)
        | ~ l3_lattices(sK11)
        | v2_struct_0(sK11) )
    | spl19_4 ),
    inference(duplicate_literal_removal,[],[f1077])).

fof(f1077,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ r2_hidden(X0,sK13)
        | ~ l3_lattices(sK11)
        | v2_struct_0(sK11)
        | ~ m1_subset_1(X0,u1_struct_0(sK11)) )
    | spl19_4 ),
    inference(resolution,[],[f1076,f360])).

fof(f1076,plain,
    ( ! [X0] :
        ( ~ r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13))
        | ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) )
    | spl19_4 ),
    inference(subsumption_resolution,[],[f1075,f75])).

fof(f1075,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | v2_struct_0(sK11) )
    | spl19_4 ),
    inference(subsumption_resolution,[],[f1074,f76])).

fof(f1074,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ v10_lattices(sK11)
        | v2_struct_0(sK11) )
    | spl19_4 ),
    inference(subsumption_resolution,[],[f1073,f77])).

fof(f1073,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ v4_lattice3(sK11)
        | ~ v10_lattices(sK11)
        | v2_struct_0(sK11) )
    | spl19_4 ),
    inference(subsumption_resolution,[],[f1072,f78])).

fof(f1072,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ l3_lattices(sK11)
        | ~ v4_lattice3(sK11)
        | ~ v10_lattices(sK11)
        | v2_struct_0(sK11) )
    | spl19_4 ),
    inference(duplicate_literal_removal,[],[f1071])).

fof(f1071,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13))
        | ~ r2_hidden(X0,a_2_1_lattice3(sK11,sK13))
        | ~ m1_subset_1(X0,u1_struct_0(sK11))
        | ~ l3_lattices(sK11)
        | ~ v4_lattice3(sK11)
        | ~ v10_lattices(sK11)
        | v2_struct_0(sK11) )
    | spl19_4 ),
    inference(superposition,[],[f1051,f84])).

fof(f1051,plain,
    ( ~ m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11))
    | spl19_4 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f1068,plain,
    ( ~ spl19_4
    | ~ spl19_5
    | spl19_6
    | ~ spl19_7
    | ~ spl19_8 ),
    inference(avatar_split_clause,[],[f1047,f1065,f1061,f1057,f1053,f1049])).

fof(f1047,plain,
    ( ~ sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))
    | ~ sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11)
    | sK12 = k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))
    | ~ r2_hidden(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK13)
    | ~ m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11)) ),
    inference(subsumption_resolution,[],[f1046,f77])).

fof(f1046,plain,
    ( ~ sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))
    | ~ sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11)
    | ~ v4_lattice3(sK11)
    | sK12 = k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))
    | ~ r2_hidden(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK13)
    | ~ m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11)) ),
    inference(subsumption_resolution,[],[f1045,f78])).

fof(f1045,plain,
    ( ~ l3_lattices(sK11)
    | ~ sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))
    | ~ sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11)
    | ~ v4_lattice3(sK11)
    | sK12 = k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))
    | ~ r2_hidden(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK13)
    | ~ m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11)) ),
    inference(subsumption_resolution,[],[f1044,f75])).

fof(f1044,plain,
    ( v2_struct_0(sK11)
    | ~ l3_lattices(sK11)
    | ~ sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))
    | ~ sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11)
    | ~ v4_lattice3(sK11)
    | sK12 = k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))
    | ~ r2_hidden(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK13)
    | ~ m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11)) ),
    inference(subsumption_resolution,[],[f1030,f76])).

fof(f1030,plain,
    ( ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | ~ l3_lattices(sK11)
    | ~ sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))
    | ~ sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11)
    | ~ v4_lattice3(sK11)
    | sK12 = k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))
    | ~ r2_hidden(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK13)
    | ~ m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11)) ),
    inference(resolution,[],[f1024,f859])).

fof(f859,plain,(
    ! [X0] :
      ( ~ r3_lattice3(sK11,X0,sK13)
      | sK12 = X0
      | ~ r2_hidden(X0,sK13)
      | ~ m1_subset_1(X0,u1_struct_0(sK11)) ) ),
    inference(subsumption_resolution,[],[f858,f79])).

fof(f858,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK13)
      | sK12 = X0
      | ~ m1_subset_1(sK12,u1_struct_0(sK11))
      | ~ r3_lattice3(sK11,X0,sK13)
      | ~ m1_subset_1(X0,u1_struct_0(sK11)) ) ),
    inference(subsumption_resolution,[],[f857,f77])).

fof(f857,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK13)
      | sK12 = X0
      | ~ v4_lattice3(sK11)
      | ~ m1_subset_1(sK12,u1_struct_0(sK11))
      | ~ r3_lattice3(sK11,X0,sK13)
      | ~ m1_subset_1(X0,u1_struct_0(sK11)) ) ),
    inference(subsumption_resolution,[],[f856,f75])).

fof(f856,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK13)
      | sK12 = X0
      | v2_struct_0(sK11)
      | ~ v4_lattice3(sK11)
      | ~ m1_subset_1(sK12,u1_struct_0(sK11))
      | ~ r3_lattice3(sK11,X0,sK13)
      | ~ m1_subset_1(X0,u1_struct_0(sK11)) ) ),
    inference(subsumption_resolution,[],[f855,f80])).

fof(f855,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK13)
      | ~ r2_hidden(sK12,sK13)
      | sK12 = X0
      | v2_struct_0(sK11)
      | ~ v4_lattice3(sK11)
      | ~ m1_subset_1(sK12,u1_struct_0(sK11))
      | ~ r3_lattice3(sK11,X0,sK13)
      | ~ m1_subset_1(X0,u1_struct_0(sK11)) ) ),
    inference(subsumption_resolution,[],[f854,f78])).

fof(f854,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK13)
      | ~ l3_lattices(sK11)
      | ~ r2_hidden(sK12,sK13)
      | sK12 = X0
      | v2_struct_0(sK11)
      | ~ v4_lattice3(sK11)
      | ~ m1_subset_1(sK12,u1_struct_0(sK11))
      | ~ r3_lattice3(sK11,X0,sK13)
      | ~ m1_subset_1(X0,u1_struct_0(sK11)) ) ),
    inference(subsumption_resolution,[],[f840,f76])).

fof(f840,plain,(
    ! [X0] :
      ( ~ v10_lattices(sK11)
      | ~ r2_hidden(X0,sK13)
      | ~ l3_lattices(sK11)
      | ~ r2_hidden(sK12,sK13)
      | sK12 = X0
      | v2_struct_0(sK11)
      | ~ v4_lattice3(sK11)
      | ~ m1_subset_1(sK12,u1_struct_0(sK11))
      | ~ r3_lattice3(sK11,X0,sK13)
      | ~ m1_subset_1(X0,u1_struct_0(sK11)) ) ),
    inference(resolution,[],[f835,f81])).

fof(f835,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X0,X3,X2)
      | ~ v10_lattices(X0)
      | ~ r2_hidden(X1,X2)
      | ~ l3_lattices(X0)
      | ~ r2_hidden(X3,X2)
      | X1 = X3
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f830,f125])).

fof(f830,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP9(X2,X0,X1)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | ~ r2_hidden(X1,X2)
      | ~ l3_lattices(X0)
      | ~ r2_hidden(X3,X2)
      | X1 = X3
      | v2_struct_0(X0)
      | ~ r3_lattice3(X0,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f825,f125])).

fof(f825,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP9(X3,X1,X2)
      | v2_struct_0(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | ~ r2_hidden(X0,X3)
      | ~ l3_lattices(X1)
      | ~ r2_hidden(X2,X3)
      | X0 = X2
      | ~ sP9(X3,X1,X0) ) ),
    inference(subsumption_resolution,[],[f824,f122])).

fof(f824,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | v2_struct_0(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | ~ r2_hidden(X0,X3)
      | ~ l3_lattices(X1)
      | ~ r2_hidden(X2,X3)
      | ~ sP9(X3,X1,X2)
      | ~ sP9(X3,X1,X0)
      | ~ sP10(X0,X1,X3) ) ),
    inference(subsumption_resolution,[],[f823,f151])).

fof(f823,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X2
      | v2_struct_0(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | ~ r2_hidden(X0,X3)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r2_hidden(X2,X3)
      | ~ sP9(X3,X1,X2)
      | ~ sP9(X3,X1,X0)
      | ~ sP10(X0,X1,X3) ) ),
    inference(subsumption_resolution,[],[f820,f151])).

fof(f820,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | X0 = X2
      | v2_struct_0(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | ~ r2_hidden(X0,X3)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ r2_hidden(X2,X3)
      | ~ sP9(X3,X1,X2)
      | ~ sP9(X3,X1,X0)
      | ~ sP10(X0,X1,X3) ) ),
    inference(resolution,[],[f817,f117])).

fof(f817,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X1,a_2_1_lattice3(X0,X3))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | X1 = X2
      | v2_struct_0(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | ~ r2_hidden(X1,X3)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X3)
      | ~ sP9(X3,X0,X2) ) ),
    inference(subsumption_resolution,[],[f814,f122])).

fof(f814,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | X1 = X2
      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X3))
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | ~ r2_hidden(X1,X3)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X3)
      | ~ sP9(X3,X0,X2)
      | ~ sP10(X2,X0,X3) ) ),
    inference(resolution,[],[f810,f117])).

fof(f810,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,a_2_1_lattice3(X0,X3))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | X1 = X2
      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X3))
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | ~ r2_hidden(X1,X3)
      | ~ l3_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f804])).

fof(f804,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | X1 = X2
      | ~ r2_hidden(X1,a_2_1_lattice3(X0,X3))
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X2,a_2_1_lattice3(X0,X3))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X2,X3)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(resolution,[],[f363,f360])).

fof(f363,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_lattice3(X2,X3,a_2_1_lattice3(X2,X1))
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | X0 = X3
      | ~ r2_hidden(X0,a_2_1_lattice3(X2,X1))
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X3,a_2_1_lattice3(X2,X1))
      | ~ m1_subset_1(X3,u1_struct_0(X2)) ) ),
    inference(duplicate_literal_removal,[],[f361])).

fof(f361,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | X0 = X3
      | ~ r2_hidden(X0,a_2_1_lattice3(X2,X1))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ r4_lattice3(X2,X3,a_2_1_lattice3(X2,X1))
      | ~ r2_hidden(X3,a_2_1_lattice3(X2,X1))
      | ~ m1_subset_1(X3,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f360,f220])).

fof(f220,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r4_lattice3(X0,X3,X1)
      | X2 = X3
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r4_lattice3(X0,X3,X1)
      | ~ r2_hidden(X3,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ r4_lattice3(X0,X2,X1)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f84,f84])).

fof(f1024,plain,(
    ! [X4,X3] :
      ( r3_lattice3(X3,k15_lattice3(X3,a_2_1_lattice3(X3,X4)),X4)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ sP6(X3,k15_lattice3(X3,a_2_1_lattice3(X3,X4)))
      | ~ sP2(k15_lattice3(X3,a_2_1_lattice3(X3,X4)),X3)
      | ~ v4_lattice3(X3) ) ),
    inference(duplicate_literal_removal,[],[f1021])).

fof(f1021,plain,(
    ! [X4,X3] :
      ( ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ sP6(X3,k15_lattice3(X3,a_2_1_lattice3(X3,X4)))
      | ~ sP2(k15_lattice3(X3,a_2_1_lattice3(X3,X4)),X3)
      | r3_lattice3(X3,k15_lattice3(X3,a_2_1_lattice3(X3,X4)),X4)
      | ~ sP6(X3,k15_lattice3(X3,a_2_1_lattice3(X3,X4))) ) ),
    inference(resolution,[],[f1019,f103])).

fof(f1019,plain,(
    ! [X0,X1] :
      ( sP5(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ sP6(X0,k15_lattice3(X0,a_2_1_lattice3(X0,X1)))
      | ~ sP2(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0) ) ),
    inference(duplicate_literal_removal,[],[f1014])).

fof(f1014,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP5(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1)
      | ~ sP6(X0,k15_lattice3(X0,a_2_1_lattice3(X0,X1)))
      | ~ sP2(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0)
      | sP5(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1) ) ),
    inference(resolution,[],[f739,f106])).

fof(f739,plain,(
    ! [X14,X12,X13] :
      ( ~ r2_hidden(sK16(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14),X13)
      | ~ l3_lattices(X12)
      | ~ v4_lattice3(X12)
      | ~ v10_lattices(X12)
      | v2_struct_0(X12)
      | sP5(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14)
      | ~ sP6(X12,k15_lattice3(X12,a_2_1_lattice3(X12,X13)))
      | ~ sP2(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12) ) ),
    inference(subsumption_resolution,[],[f732,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))
      | sP5(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f732,plain,(
    ! [X14,X12,X13] :
      ( ~ sP6(X12,k15_lattice3(X12,a_2_1_lattice3(X12,X13)))
      | ~ l3_lattices(X12)
      | ~ v4_lattice3(X12)
      | ~ v10_lattices(X12)
      | v2_struct_0(X12)
      | sP5(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14)
      | ~ m1_subset_1(sK16(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14),u1_struct_0(X12))
      | ~ r2_hidden(sK16(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14),X13)
      | ~ sP2(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12) ) ),
    inference(duplicate_literal_removal,[],[f727])).

fof(f727,plain,(
    ! [X14,X12,X13] :
      ( ~ sP6(X12,k15_lattice3(X12,a_2_1_lattice3(X12,X13)))
      | ~ l3_lattices(X12)
      | ~ v4_lattice3(X12)
      | ~ v10_lattices(X12)
      | v2_struct_0(X12)
      | sP5(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14)
      | ~ m1_subset_1(sK16(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14),u1_struct_0(X12))
      | ~ r2_hidden(sK16(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14),X13)
      | ~ sP2(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12)
      | ~ l3_lattices(X12)
      | ~ v4_lattice3(X12)
      | ~ v10_lattices(X12)
      | v2_struct_0(X12) ) ),
    inference(resolution,[],[f708,f210])).

fof(f210,plain,(
    ! [X4,X3] :
      ( r3_lattice3(X3,k15_lattice3(X3,X4),a_2_2_lattice3(X3,X4))
      | ~ sP2(k15_lattice3(X3,X4),X3)
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ v10_lattices(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f155,f83])).

fof(f155,plain,(
    ! [X2,X3] :
      ( r3_lattice3(X2,k16_lattice3(X2,X3),X3)
      | ~ sP2(k16_lattice3(X2,X3),X2) ) ),
    inference(resolution,[],[f123,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | r3_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f708,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ r3_lattice3(X4,X5,a_2_2_lattice3(X6,a_2_1_lattice3(X6,X7)))
      | ~ sP6(X4,X5)
      | ~ l3_lattices(X6)
      | ~ v4_lattice3(X6)
      | ~ v10_lattices(X6)
      | v2_struct_0(X6)
      | sP5(X5,X4,X8)
      | ~ m1_subset_1(sK16(X5,X4,X8),u1_struct_0(X6))
      | ~ r2_hidden(sK16(X5,X4,X8),X7) ) ),
    inference(duplicate_literal_removal,[],[f707])).

fof(f707,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ sP6(X4,X5)
      | ~ r3_lattice3(X4,X5,a_2_2_lattice3(X6,a_2_1_lattice3(X6,X7)))
      | ~ l3_lattices(X6)
      | ~ v4_lattice3(X6)
      | ~ v10_lattices(X6)
      | v2_struct_0(X6)
      | sP5(X5,X4,X8)
      | ~ m1_subset_1(sK16(X5,X4,X8),u1_struct_0(X6))
      | ~ r2_hidden(sK16(X5,X4,X8),X7)
      | ~ l3_lattices(X6)
      | v2_struct_0(X6)
      | ~ m1_subset_1(sK16(X5,X4,X8),u1_struct_0(X6)) ) ),
    inference(resolution,[],[f475,f360])).

fof(f475,plain,(
    ! [X6,X4,X8,X7,X5] :
      ( ~ r4_lattice3(X7,sK16(X4,X5,X6),X8)
      | ~ sP6(X5,X4)
      | ~ r3_lattice3(X5,X4,a_2_2_lattice3(X7,X8))
      | ~ l3_lattices(X7)
      | ~ v4_lattice3(X7)
      | ~ v10_lattices(X7)
      | v2_struct_0(X7)
      | sP5(X4,X5,X6)
      | ~ m1_subset_1(sK16(X4,X5,X6),u1_struct_0(X7)) ) ),
    inference(resolution,[],[f459,f124])).

fof(f124,plain,(
    ! [X0,X3,X1] :
      ( sP7(X0,X1,X3)
      | ~ r4_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X0,X1,X2)
      | ~ r4_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f459,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP7(X3,X4,sK16(X1,X0,X2))
      | sP5(X1,X0,X2)
      | ~ sP6(X0,X1)
      | ~ r3_lattice3(X0,X1,a_2_2_lattice3(X4,X3))
      | ~ l3_lattices(X4)
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f229,f115])).

fof(f229,plain,(
    ! [X6,X4,X7,X5,X3] :
      ( ~ sP8(sK16(X4,X3,X7),X5,X6)
      | ~ sP6(X3,X4)
      | sP5(X4,X3,X7)
      | ~ sP7(X6,X5,sK16(X4,X3,X7))
      | ~ r3_lattice3(X3,X4,a_2_2_lattice3(X5,X6)) ) ),
    inference(resolution,[],[f227,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ sP7(X2,X1,X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f227,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(sK16(X4,X5,X6),X7)
      | ~ r3_lattice3(X5,X4,X7)
      | ~ sP6(X5,X4)
      | sP5(X4,X5,X6) ) ),
    inference(subsumption_resolution,[],[f226,f105])).

fof(f226,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ m1_subset_1(sK16(X4,X5,X6),u1_struct_0(X5))
      | ~ r2_hidden(sK16(X4,X5,X6),X7)
      | ~ r3_lattice3(X5,X4,X7)
      | ~ sP6(X5,X4)
      | sP5(X4,X5,X6) ) ),
    inference(resolution,[],[f206,f107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:10:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.44  % (24960)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.45  % (24952)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.46  % (24944)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.46  % (24944)Refutation not found, incomplete strategy% (24944)------------------------------
% 0.20/0.46  % (24944)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (24944)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.46  
% 0.20/0.46  % (24944)Memory used [KB]: 1663
% 0.20/0.46  % (24944)Time elapsed: 0.052 s
% 0.20/0.46  % (24944)------------------------------
% 0.20/0.46  % (24944)------------------------------
% 0.20/0.47  % (24945)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.48  % (24949)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (24948)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.49  % (24948)Refutation not found, incomplete strategy% (24948)------------------------------
% 0.20/0.49  % (24948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (24948)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (24948)Memory used [KB]: 10490
% 0.20/0.49  % (24948)Time elapsed: 0.084 s
% 0.20/0.49  % (24948)------------------------------
% 0.20/0.49  % (24948)------------------------------
% 0.20/0.49  % (24937)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.49  % (24957)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.49  % (24939)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.50  % (24941)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (24947)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.50  % (24946)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (24940)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.50  % (24959)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (24937)Refutation not found, incomplete strategy% (24937)------------------------------
% 0.20/0.50  % (24937)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (24937)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (24937)Memory used [KB]: 10490
% 0.20/0.50  % (24937)Time elapsed: 0.089 s
% 0.20/0.50  % (24937)------------------------------
% 0.20/0.50  % (24937)------------------------------
% 0.20/0.50  % (24942)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (24950)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (24938)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.51  % (24950)Refutation not found, incomplete strategy% (24950)------------------------------
% 0.20/0.51  % (24950)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (24950)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (24950)Memory used [KB]: 6140
% 0.20/0.51  % (24950)Time elapsed: 0.107 s
% 0.20/0.51  % (24950)------------------------------
% 0.20/0.51  % (24950)------------------------------
% 0.20/0.51  % (24951)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (24955)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (24943)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (24956)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (24962)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.52  % (24954)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.53  % (24961)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.54  % (24958)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.54  % (24953)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 2.16/0.63  % (24946)Refutation not found, incomplete strategy% (24946)------------------------------
% 2.16/0.63  % (24946)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.63  % (24946)Termination reason: Refutation not found, incomplete strategy
% 2.16/0.63  
% 2.16/0.63  % (24946)Memory used [KB]: 6012
% 2.16/0.63  % (24946)Time elapsed: 0.228 s
% 2.16/0.63  % (24946)------------------------------
% 2.16/0.63  % (24946)------------------------------
% 2.42/0.68  % (24941)Refutation found. Thanks to Tanya!
% 2.42/0.68  % SZS status Theorem for theBenchmark
% 2.42/0.68  % SZS output start Proof for theBenchmark
% 2.42/0.68  fof(f1836,plain,(
% 2.42/0.68    $false),
% 2.42/0.68    inference(avatar_sat_refutation,[],[f1068,f1121,f1141,f1144,f1206,f1835])).
% 2.42/0.68  fof(f1835,plain,(
% 2.42/0.68    ~spl19_6),
% 2.42/0.68    inference(avatar_contradiction_clause,[],[f1834])).
% 2.42/0.68  fof(f1834,plain,(
% 2.42/0.68    $false | ~spl19_6),
% 2.42/0.68    inference(subsumption_resolution,[],[f1833,f192])).
% 2.42/0.68  fof(f192,plain,(
% 2.42/0.68    sP2(sK12,sK11)),
% 2.42/0.68    inference(subsumption_resolution,[],[f191,f75])).
% 2.42/0.68  fof(f75,plain,(
% 2.42/0.68    ~v2_struct_0(sK11)),
% 2.42/0.68    inference(cnf_transformation,[],[f45])).
% 2.42/0.68  fof(f45,plain,(
% 2.42/0.68    ((sK12 != k16_lattice3(sK11,sK13) & r3_lattice3(sK11,sK12,sK13) & r2_hidden(sK12,sK13)) & m1_subset_1(sK12,u1_struct_0(sK11))) & l3_lattices(sK11) & v4_lattice3(sK11) & v10_lattices(sK11) & ~v2_struct_0(sK11)),
% 2.42/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12,sK13])],[f11,f44,f43,f42])).
% 2.42/0.68  fof(f42,plain,(
% 2.42/0.68    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK11,X2) != X1 & r3_lattice3(sK11,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK11))) & l3_lattices(sK11) & v4_lattice3(sK11) & v10_lattices(sK11) & ~v2_struct_0(sK11))),
% 2.42/0.68    introduced(choice_axiom,[])).
% 2.42/0.68  fof(f43,plain,(
% 2.42/0.68    ? [X1] : (? [X2] : (k16_lattice3(sK11,X2) != X1 & r3_lattice3(sK11,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK11))) => (? [X2] : (k16_lattice3(sK11,X2) != sK12 & r3_lattice3(sK11,sK12,X2) & r2_hidden(sK12,X2)) & m1_subset_1(sK12,u1_struct_0(sK11)))),
% 2.42/0.68    introduced(choice_axiom,[])).
% 2.42/0.68  fof(f44,plain,(
% 2.42/0.68    ? [X2] : (k16_lattice3(sK11,X2) != sK12 & r3_lattice3(sK11,sK12,X2) & r2_hidden(sK12,X2)) => (sK12 != k16_lattice3(sK11,sK13) & r3_lattice3(sK11,sK12,sK13) & r2_hidden(sK12,sK13))),
% 2.42/0.68    introduced(choice_axiom,[])).
% 2.42/0.68  fof(f11,plain,(
% 2.42/0.68    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 2.42/0.68    inference(flattening,[],[f10])).
% 2.42/0.68  fof(f10,plain,(
% 2.42/0.68    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 2.42/0.68    inference(ennf_transformation,[],[f9])).
% 2.42/0.68  fof(f9,negated_conjecture,(
% 2.42/0.68    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 2.42/0.68    inference(negated_conjecture,[],[f8])).
% 2.42/0.68  fof(f8,conjecture,(
% 2.42/0.68    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 2.42/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_lattice3)).
% 2.42/0.68  fof(f191,plain,(
% 2.42/0.68    sP2(sK12,sK11) | v2_struct_0(sK11)),
% 2.42/0.68    inference(subsumption_resolution,[],[f190,f76])).
% 2.42/0.68  fof(f76,plain,(
% 2.42/0.68    v10_lattices(sK11)),
% 2.42/0.68    inference(cnf_transformation,[],[f45])).
% 2.42/0.68  fof(f190,plain,(
% 2.42/0.68    sP2(sK12,sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11)),
% 2.42/0.68    inference(subsumption_resolution,[],[f189,f77])).
% 2.42/0.68  fof(f77,plain,(
% 2.42/0.68    v4_lattice3(sK11)),
% 2.42/0.68    inference(cnf_transformation,[],[f45])).
% 2.42/0.69  fof(f189,plain,(
% 2.42/0.69    sP2(sK12,sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11)),
% 2.42/0.69    inference(subsumption_resolution,[],[f183,f78])).
% 2.42/0.69  fof(f78,plain,(
% 2.42/0.69    l3_lattices(sK11)),
% 2.42/0.69    inference(cnf_transformation,[],[f45])).
% 2.42/0.69  fof(f183,plain,(
% 2.42/0.69    sP2(sK12,sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11)),
% 2.42/0.69    inference(resolution,[],[f94,f79])).
% 2.42/0.69  fof(f79,plain,(
% 2.42/0.69    m1_subset_1(sK12,u1_struct_0(sK11))),
% 2.42/0.69    inference(cnf_transformation,[],[f45])).
% 2.42/0.69  fof(f94,plain,(
% 2.42/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP2(X1,X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f29])).
% 2.42/0.69  fof(f29,plain,(
% 2.42/0.69    ! [X0] : (! [X1] : (sP2(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.69    inference(definition_folding,[],[f17,f28,f27,f26])).
% 2.42/0.69  fof(f26,plain,(
% 2.42/0.69    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 2.42/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.42/0.69  fof(f27,plain,(
% 2.42/0.69    ! [X2,X0,X1] : (sP1(X2,X0,X1) <=> (sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)))),
% 2.42/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.42/0.69  fof(f28,plain,(
% 2.42/0.69    ! [X1,X0] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> sP1(X2,X0,X1)) | ~sP2(X1,X0))),
% 2.42/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.42/0.69  fof(f17,plain,(
% 2.42/0.69    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.69    inference(flattening,[],[f16])).
% 2.42/0.69  fof(f16,plain,(
% 2.42/0.69    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.69    inference(ennf_transformation,[],[f5])).
% 2.42/0.69  fof(f5,axiom,(
% 2.42/0.69    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 2.42/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 2.42/0.69  fof(f1833,plain,(
% 2.42/0.69    ~sP2(sK12,sK11) | ~spl19_6),
% 2.42/0.69    inference(subsumption_resolution,[],[f1829,f81])).
% 2.42/0.69  fof(f81,plain,(
% 2.42/0.69    r3_lattice3(sK11,sK12,sK13)),
% 2.42/0.69    inference(cnf_transformation,[],[f45])).
% 2.42/0.69  fof(f1829,plain,(
% 2.42/0.69    ~r3_lattice3(sK11,sK12,sK13) | ~sP2(sK12,sK11) | ~spl19_6),
% 2.42/0.69    inference(trivial_inequality_removal,[],[f1826])).
% 2.42/0.69  fof(f1826,plain,(
% 2.42/0.69    ~r3_lattice3(sK11,sK12,sK13) | sK12 != sK12 | ~sP2(sK12,sK11) | ~spl19_6),
% 2.42/0.69    inference(resolution,[],[f1824,f168])).
% 2.42/0.69  fof(f168,plain,(
% 2.42/0.69    ( ! [X6] : (~sP0(X6,sK11,sK13) | ~r3_lattice3(sK11,X6,sK13) | sK12 != X6 | ~sP2(X6,sK11)) )),
% 2.42/0.69    inference(resolution,[],[f89,f157])).
% 2.42/0.69  fof(f157,plain,(
% 2.42/0.69    ( ! [X0] : (~sP1(sK13,sK11,X0) | sK12 != X0 | ~sP2(X0,sK11)) )),
% 2.42/0.69    inference(superposition,[],[f82,f86])).
% 2.42/0.69  fof(f86,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (k16_lattice3(X1,X2) = X0 | ~sP1(X2,X1,X0) | ~sP2(X0,X1)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f47])).
% 2.42/0.69  fof(f47,plain,(
% 2.42/0.69    ! [X0,X1] : (! [X2] : ((k16_lattice3(X1,X2) = X0 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k16_lattice3(X1,X2) != X0)) | ~sP2(X0,X1))),
% 2.42/0.69    inference(rectify,[],[f46])).
% 2.42/0.69  fof(f46,plain,(
% 2.42/0.69    ! [X1,X0] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ~sP1(X2,X0,X1)) & (sP1(X2,X0,X1) | k16_lattice3(X0,X2) != X1)) | ~sP2(X1,X0))),
% 2.42/0.69    inference(nnf_transformation,[],[f28])).
% 2.42/0.69  fof(f82,plain,(
% 2.42/0.69    sK12 != k16_lattice3(sK11,sK13)),
% 2.42/0.69    inference(cnf_transformation,[],[f45])).
% 2.42/0.69  fof(f89,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f50])).
% 2.42/0.69  fof(f50,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) & ((sP0(X2,X1,X0) & r3_lattice3(X1,X2,X0)) | ~sP1(X0,X1,X2)))),
% 2.42/0.69    inference(rectify,[],[f49])).
% 2.42/0.69  fof(f49,plain,(
% 2.42/0.69    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | ~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2)) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP1(X2,X0,X1)))),
% 2.42/0.69    inference(flattening,[],[f48])).
% 2.42/0.69  fof(f48,plain,(
% 2.42/0.69    ! [X2,X0,X1] : ((sP1(X2,X0,X1) | (~sP0(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) & ((sP0(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP1(X2,X0,X1)))),
% 2.42/0.69    inference(nnf_transformation,[],[f27])).
% 2.42/0.69  fof(f1824,plain,(
% 2.42/0.69    sP0(sK12,sK11,sK13) | ~spl19_6),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f1823])).
% 2.42/0.69  fof(f1823,plain,(
% 2.42/0.69    sP0(sK12,sK11,sK13) | sP0(sK12,sK11,sK13) | ~spl19_6),
% 2.42/0.69    inference(resolution,[],[f1822,f92])).
% 2.42/0.69  fof(f92,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK14(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f54])).
% 2.42/0.69  fof(f54,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r3_lattices(X1,sK14(X0,X1,X2),X0) & r3_lattice3(X1,sK14(X0,X1,X2),X2) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 2.42/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f52,f53])).
% 2.42/0.69  fof(f53,plain,(
% 2.42/0.69    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r3_lattices(X1,sK14(X0,X1,X2),X0) & r3_lattice3(X1,sK14(X0,X1,X2),X2) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1))))),
% 2.42/0.69    introduced(choice_axiom,[])).
% 2.42/0.69  fof(f52,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 2.42/0.69    inference(rectify,[],[f51])).
% 2.42/0.69  fof(f51,plain,(
% 2.42/0.69    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X1,X0,X2)))),
% 2.42/0.69    inference(nnf_transformation,[],[f26])).
% 2.42/0.69  fof(f1822,plain,(
% 2.42/0.69    ( ! [X0] : (~r3_lattice3(sK11,sK14(sK12,sK11,X0),sK13) | sP0(sK12,sK11,X0)) ) | ~spl19_6),
% 2.42/0.69    inference(subsumption_resolution,[],[f1821,f91])).
% 2.42/0.69  fof(f91,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f54])).
% 2.42/0.69  fof(f1821,plain,(
% 2.42/0.69    ( ! [X0] : (~r3_lattice3(sK11,sK14(sK12,sK11,X0),sK13) | ~m1_subset_1(sK14(sK12,sK11,X0),u1_struct_0(sK11)) | sP0(sK12,sK11,X0)) ) | ~spl19_6),
% 2.42/0.69    inference(resolution,[],[f1814,f93])).
% 2.42/0.69  fof(f93,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~r3_lattices(X1,sK14(X0,X1,X2),X0) | sP0(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f54])).
% 2.42/0.69  fof(f1814,plain,(
% 2.42/0.69    ( ! [X0] : (r3_lattices(sK11,X0,sK12) | ~r3_lattice3(sK11,X0,sK13) | ~m1_subset_1(X0,u1_struct_0(sK11))) ) | ~spl19_6),
% 2.42/0.69    inference(resolution,[],[f1812,f125])).
% 2.42/0.69  fof(f125,plain,(
% 2.42/0.69    ( ! [X0,X3,X1] : (sP9(X0,X1,X3) | ~r3_lattice3(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.42/0.69    inference(equality_resolution,[],[f121])).
% 2.42/0.69  fof(f121,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (sP9(X0,X1,X2) | ~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.42/0.69    inference(cnf_transformation,[],[f74])).
% 2.42/0.69  fof(f74,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((sP9(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK18(X0,X1,X2),X0) & sK18(X0,X1,X2) = X2 & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1))) | ~sP9(X0,X1,X2)))),
% 2.42/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK18])],[f72,f73])).
% 2.42/0.69  fof(f73,plain,(
% 2.42/0.69    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK18(X0,X1,X2),X0) & sK18(X0,X1,X2) = X2 & m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1))))),
% 2.42/0.69    introduced(choice_axiom,[])).
% 2.42/0.69  fof(f72,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((sP9(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP9(X0,X1,X2)))),
% 2.42/0.69    inference(rectify,[],[f71])).
% 2.42/0.69  fof(f71,plain,(
% 2.42/0.69    ! [X2,X1,X0] : ((sP9(X2,X1,X0) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP9(X2,X1,X0)))),
% 2.42/0.69    inference(nnf_transformation,[],[f39])).
% 2.42/0.69  fof(f39,plain,(
% 2.42/0.69    ! [X2,X1,X0] : (sP9(X2,X1,X0) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 2.42/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 2.42/0.69  fof(f1812,plain,(
% 2.42/0.69    ( ! [X0] : (~sP9(sK13,sK11,X0) | r3_lattices(sK11,X0,sK12)) ) | ~spl19_6),
% 2.42/0.69    inference(subsumption_resolution,[],[f1811,f75])).
% 2.42/0.69  fof(f1811,plain,(
% 2.42/0.69    ( ! [X0] : (~sP9(sK13,sK11,X0) | r3_lattices(sK11,X0,sK12) | v2_struct_0(sK11)) ) | ~spl19_6),
% 2.42/0.69    inference(subsumption_resolution,[],[f1809,f78])).
% 2.42/0.69  fof(f1809,plain,(
% 2.42/0.69    ( ! [X0] : (~sP9(sK13,sK11,X0) | r3_lattices(sK11,X0,sK12) | ~l3_lattices(sK11) | v2_struct_0(sK11)) ) | ~spl19_6),
% 2.42/0.69    inference(resolution,[],[f1808,f122])).
% 2.42/0.69  fof(f122,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (sP10(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f41])).
% 2.42/0.69  fof(f41,plain,(
% 2.42/0.69    ! [X0,X1,X2] : (sP10(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 2.42/0.69    inference(definition_folding,[],[f25,f40,f39])).
% 2.42/0.69  fof(f40,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> sP9(X2,X1,X0)) | ~sP10(X0,X1,X2))),
% 2.42/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).
% 2.42/0.69  fof(f25,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 2.42/0.69    inference(flattening,[],[f24])).
% 2.42/0.69  fof(f24,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 2.42/0.69    inference(ennf_transformation,[],[f3])).
% 2.42/0.69  fof(f3,axiom,(
% 2.42/0.69    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.42/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).
% 2.42/0.69  fof(f1808,plain,(
% 2.42/0.69    ( ! [X0] : (~sP10(X0,sK11,sK13) | ~sP9(sK13,sK11,X0) | r3_lattices(sK11,X0,sK12)) ) | ~spl19_6),
% 2.42/0.69    inference(subsumption_resolution,[],[f1804,f151])).
% 2.42/0.69  fof(f151,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~sP9(X0,X1,X2) | m1_subset_1(X2,u1_struct_0(X1))) )),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f150])).
% 2.42/0.69  fof(f150,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (m1_subset_1(X2,u1_struct_0(X1)) | ~sP9(X0,X1,X2) | ~sP9(X0,X1,X2)) )),
% 2.42/0.69    inference(superposition,[],[f118,f119])).
% 2.42/0.69  fof(f119,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (sK18(X0,X1,X2) = X2 | ~sP9(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f74])).
% 2.42/0.69  fof(f118,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (m1_subset_1(sK18(X0,X1,X2),u1_struct_0(X1)) | ~sP9(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f74])).
% 2.42/0.69  fof(f1804,plain,(
% 2.42/0.69    ( ! [X0] : (r3_lattices(sK11,X0,sK12) | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~sP9(sK13,sK11,X0) | ~sP10(X0,sK11,sK13)) ) | ~spl19_6),
% 2.42/0.69    inference(resolution,[],[f1753,f117])).
% 2.42/0.69  fof(f117,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP9(X2,X1,X0) | ~sP10(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f70])).
% 2.42/0.69  fof(f70,plain,(
% 2.42/0.69    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP9(X2,X1,X0)) & (sP9(X2,X1,X0) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~sP10(X0,X1,X2))),
% 2.42/0.69    inference(nnf_transformation,[],[f40])).
% 2.42/0.69  fof(f1753,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | r3_lattices(sK11,X0,sK12) | ~m1_subset_1(X0,u1_struct_0(sK11))) ) | ~spl19_6),
% 2.42/0.69    inference(subsumption_resolution,[],[f1752,f76])).
% 2.42/0.69  fof(f1752,plain,(
% 2.42/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK11)) | r3_lattices(sK11,X0,sK12) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~v10_lattices(sK11)) ) | ~spl19_6),
% 2.42/0.69    inference(subsumption_resolution,[],[f1751,f78])).
% 2.42/0.69  fof(f1751,plain,(
% 2.42/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK11)) | r3_lattices(sK11,X0,sK12) | ~l3_lattices(sK11) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~v10_lattices(sK11)) ) | ~spl19_6),
% 2.42/0.69    inference(subsumption_resolution,[],[f1750,f77])).
% 2.42/0.69  fof(f1750,plain,(
% 2.42/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK11)) | r3_lattices(sK11,X0,sK12) | ~v4_lattice3(sK11) | ~l3_lattices(sK11) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~v10_lattices(sK11)) ) | ~spl19_6),
% 2.42/0.69    inference(subsumption_resolution,[],[f1748,f75])).
% 2.42/0.69  fof(f1748,plain,(
% 2.42/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK11)) | r3_lattices(sK11,X0,sK12) | v2_struct_0(sK11) | ~v4_lattice3(sK11) | ~l3_lattices(sK11) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~v10_lattices(sK11)) ) | ~spl19_6),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f1738])).
% 2.42/0.69  fof(f1738,plain,(
% 2.42/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK11)) | r3_lattices(sK11,X0,sK12) | v2_struct_0(sK11) | ~v4_lattice3(sK11) | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~l3_lattices(sK11) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~v10_lattices(sK11)) ) | ~spl19_6),
% 2.42/0.69    inference(resolution,[],[f1277,f501])).
% 2.42/0.69  fof(f501,plain,(
% 2.42/0.69    ( ! [X6,X4,X5] : (r3_lattice3(X4,X5,a_2_2_lattice3(X4,X6)) | v2_struct_0(X4) | ~v4_lattice3(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l3_lattices(X4) | ~r2_hidden(X5,X6) | ~v10_lattices(X4)) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f500,f108])).
% 2.42/0.69  fof(f108,plain,(
% 2.42/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP6(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f35])).
% 2.42/0.69  fof(f35,plain,(
% 2.42/0.69    ! [X0] : (! [X1] : (sP6(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.69    inference(definition_folding,[],[f21,f34,f33])).
% 2.42/0.69  fof(f33,plain,(
% 2.42/0.69    ! [X1,X0,X2] : (sP5(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 2.42/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 2.42/0.69  fof(f34,plain,(
% 2.42/0.69    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP5(X1,X0,X2)) | ~sP6(X0,X1))),
% 2.42/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 2.42/0.69  fof(f21,plain,(
% 2.42/0.69    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.69    inference(flattening,[],[f20])).
% 2.42/0.69  fof(f20,plain,(
% 2.42/0.69    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.69    inference(ennf_transformation,[],[f1])).
% 2.42/0.69  fof(f1,axiom,(
% 2.42/0.69    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 2.42/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 2.42/0.69  fof(f500,plain,(
% 2.42/0.69    ( ! [X6,X4,X5] : (~v10_lattices(X4) | v2_struct_0(X4) | ~v4_lattice3(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l3_lattices(X4) | ~r2_hidden(X5,X6) | r3_lattice3(X4,X5,a_2_2_lattice3(X4,X6)) | ~sP6(X4,X5)) )),
% 2.42/0.69    inference(resolution,[],[f497,f103])).
% 2.42/0.69  fof(f103,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~sP5(X1,X0,X2) | r3_lattice3(X0,X1,X2) | ~sP6(X0,X1)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f60])).
% 2.42/0.69  fof(f60,plain,(
% 2.42/0.69    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP5(X1,X0,X2)) & (sP5(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP6(X0,X1))),
% 2.42/0.69    inference(nnf_transformation,[],[f34])).
% 2.42/0.69  fof(f497,plain,(
% 2.42/0.69    ( ! [X6,X7,X5] : (sP5(X6,X5,a_2_2_lattice3(X5,X7)) | ~v10_lattices(X5) | v2_struct_0(X5) | ~v4_lattice3(X5) | ~m1_subset_1(X6,u1_struct_0(X5)) | ~l3_lattices(X5) | ~r2_hidden(X6,X7)) )),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f496])).
% 2.42/0.69  fof(f496,plain,(
% 2.42/0.69    ( ! [X6,X7,X5] : (~v4_lattice3(X5) | ~v10_lattices(X5) | v2_struct_0(X5) | sP5(X6,X5,a_2_2_lattice3(X5,X7)) | ~m1_subset_1(X6,u1_struct_0(X5)) | ~l3_lattices(X5) | ~r2_hidden(X6,X7) | sP5(X6,X5,a_2_2_lattice3(X5,X7))) )),
% 2.42/0.69    inference(resolution,[],[f339,f107])).
% 2.42/0.69  fof(f107,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK16(X0,X1,X2)) | sP5(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f64])).
% 2.42/0.69  fof(f64,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | (~r1_lattices(X1,X0,sK16(X0,X1,X2)) & r2_hidden(sK16(X0,X1,X2),X2) & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP5(X0,X1,X2)))),
% 2.42/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f62,f63])).
% 2.42/0.69  fof(f63,plain,(
% 2.42/0.69    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK16(X0,X1,X2)) & r2_hidden(sK16(X0,X1,X2),X2) & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))))),
% 2.42/0.69    introduced(choice_axiom,[])).
% 2.42/0.69  fof(f62,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP5(X0,X1,X2)))),
% 2.42/0.69    inference(rectify,[],[f61])).
% 2.42/0.69  fof(f61,plain,(
% 2.42/0.69    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP5(X1,X0,X2)))),
% 2.42/0.69    inference(nnf_transformation,[],[f33])).
% 2.42/0.69  fof(f339,plain,(
% 2.42/0.69    ( ! [X6,X8,X7,X5,X9] : (r1_lattices(X5,X9,sK16(X6,X7,a_2_2_lattice3(X5,X8))) | ~v4_lattice3(X5) | ~v10_lattices(X5) | v2_struct_0(X5) | sP5(X6,X7,a_2_2_lattice3(X5,X8)) | ~m1_subset_1(X9,u1_struct_0(X5)) | ~l3_lattices(X5) | ~r2_hidden(X9,X8)) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f337,f292])).
% 2.42/0.69  fof(f292,plain,(
% 2.42/0.69    ( ! [X6,X4,X7,X5] : (sP4(X6,sK16(X4,X5,a_2_2_lattice3(X6,X7))) | ~l3_lattices(X6) | ~v4_lattice3(X6) | ~v10_lattices(X6) | v2_struct_0(X6) | sP5(X4,X5,a_2_2_lattice3(X6,X7))) )),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f287])).
% 2.42/0.69  fof(f287,plain,(
% 2.42/0.69    ( ! [X6,X4,X7,X5] : (sP5(X4,X5,a_2_2_lattice3(X6,X7)) | ~l3_lattices(X6) | ~v4_lattice3(X6) | ~v10_lattices(X6) | v2_struct_0(X6) | sP4(X6,sK16(X4,X5,a_2_2_lattice3(X6,X7))) | ~l3_lattices(X6) | v2_struct_0(X6)) )),
% 2.42/0.69    inference(resolution,[],[f285,f197])).
% 2.42/0.69  fof(f197,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~sP7(X0,X1,X2) | sP4(X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f196])).
% 2.42/0.69  fof(f196,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (sP4(X1,X2) | ~sP7(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1) | ~sP7(X0,X1,X2)) )),
% 2.42/0.69    inference(superposition,[],[f143,f112])).
% 2.42/0.69  fof(f112,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (sK17(X0,X1,X2) = X2 | ~sP7(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f69])).
% 2.42/0.69  fof(f69,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ! [X3] : (~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK17(X0,X1,X2),X0) & sK17(X0,X1,X2) = X2 & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 2.42/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK17])],[f67,f68])).
% 2.42/0.69  fof(f68,plain,(
% 2.42/0.69    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK17(X0,X1,X2),X0) & sK17(X0,X1,X2) = X2 & m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1))))),
% 2.42/0.69    introduced(choice_axiom,[])).
% 2.42/0.69  fof(f67,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ! [X3] : (~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 2.42/0.69    inference(rectify,[],[f66])).
% 2.42/0.69  fof(f66,plain,(
% 2.42/0.69    ! [X2,X1,X0] : ((sP7(X2,X1,X0) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP7(X2,X1,X0)))),
% 2.42/0.69    inference(nnf_transformation,[],[f36])).
% 2.42/0.69  fof(f36,plain,(
% 2.42/0.69    ! [X2,X1,X0] : (sP7(X2,X1,X0) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 2.42/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 2.42/0.69  fof(f143,plain,(
% 2.42/0.69    ( ! [X4,X5,X3] : (sP4(X4,sK17(X3,X4,X5)) | ~sP7(X3,X4,X5) | ~l3_lattices(X4) | v2_struct_0(X4)) )),
% 2.42/0.69    inference(resolution,[],[f111,f101])).
% 2.42/0.69  fof(f101,plain,(
% 2.42/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP4(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f32])).
% 2.42/0.69  fof(f32,plain,(
% 2.42/0.69    ! [X0] : (! [X1] : (sP4(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.69    inference(definition_folding,[],[f19,f31,f30])).
% 2.42/0.69  fof(f30,plain,(
% 2.42/0.69    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 2.42/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.42/0.69  fof(f31,plain,(
% 2.42/0.69    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP3(X1,X0,X2)) | ~sP4(X0,X1))),
% 2.42/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 2.42/0.69  fof(f19,plain,(
% 2.42/0.69    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.69    inference(flattening,[],[f18])).
% 2.42/0.69  fof(f18,plain,(
% 2.42/0.69    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.69    inference(ennf_transformation,[],[f2])).
% 2.42/0.69  fof(f2,axiom,(
% 2.42/0.69    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 2.42/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 2.42/0.69  fof(f111,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (m1_subset_1(sK17(X0,X1,X2),u1_struct_0(X1)) | ~sP7(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f69])).
% 2.42/0.69  fof(f285,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (sP7(X0,X1,sK16(X2,X3,a_2_2_lattice3(X1,X0))) | sP5(X2,X3,a_2_2_lattice3(X1,X0)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 2.42/0.69    inference(resolution,[],[f176,f115])).
% 2.42/0.69  fof(f115,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (sP8(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f38])).
% 2.42/0.69  fof(f38,plain,(
% 2.42/0.69    ! [X0,X1,X2] : (sP8(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 2.42/0.69    inference(definition_folding,[],[f23,f37,f36])).
% 2.42/0.69  fof(f37,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> sP7(X2,X1,X0)) | ~sP8(X0,X1,X2))),
% 2.42/0.69    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 2.42/0.69  fof(f23,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 2.42/0.69    inference(flattening,[],[f22])).
% 2.42/0.69  fof(f22,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 2.42/0.69    inference(ennf_transformation,[],[f4])).
% 2.42/0.69  fof(f4,axiom,(
% 2.42/0.69    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 2.42/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 2.42/0.69  fof(f176,plain,(
% 2.42/0.69    ( ! [X6,X4,X7,X5] : (~sP8(sK16(X6,X7,a_2_2_lattice3(X5,X4)),X5,X4) | sP7(X4,X5,sK16(X6,X7,a_2_2_lattice3(X5,X4))) | sP5(X6,X7,a_2_2_lattice3(X5,X4))) )),
% 2.42/0.69    inference(resolution,[],[f109,f106])).
% 2.42/0.69  fof(f106,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (r2_hidden(sK16(X0,X1,X2),X2) | sP5(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f64])).
% 2.42/0.69  fof(f109,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | sP7(X2,X1,X0) | ~sP8(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f65])).
% 2.42/0.69  fof(f65,plain,(
% 2.42/0.69    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~sP7(X2,X1,X0)) & (sP7(X2,X1,X0) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~sP8(X0,X1,X2))),
% 2.42/0.69    inference(nnf_transformation,[],[f37])).
% 2.42/0.69  fof(f337,plain,(
% 2.42/0.69    ( ! [X6,X8,X7,X5,X9] : (~l3_lattices(X5) | ~v4_lattice3(X5) | ~v10_lattices(X5) | v2_struct_0(X5) | sP5(X6,X7,a_2_2_lattice3(X5,X8)) | ~m1_subset_1(X9,u1_struct_0(X5)) | r1_lattices(X5,X9,sK16(X6,X7,a_2_2_lattice3(X5,X8))) | ~r2_hidden(X9,X8) | ~sP4(X5,sK16(X6,X7,a_2_2_lattice3(X5,X8)))) )),
% 2.42/0.69    inference(resolution,[],[f289,f199])).
% 2.42/0.69  fof(f199,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (~r4_lattice3(X2,X3,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | r1_lattices(X2,X0,X3) | ~r2_hidden(X0,X1) | ~sP4(X2,X3)) )),
% 2.42/0.69    inference(resolution,[],[f97,f95])).
% 2.42/0.69  fof(f95,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | ~r4_lattice3(X0,X1,X2) | ~sP4(X0,X1)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f55])).
% 2.42/0.69  fof(f55,plain,(
% 2.42/0.69    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP4(X0,X1))),
% 2.42/0.69    inference(nnf_transformation,[],[f31])).
% 2.42/0.69  fof(f97,plain,(
% 2.42/0.69    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X4,X0)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f59])).
% 2.42/0.69  fof(f59,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (~r1_lattices(X1,sK15(X0,X1,X2),X0) & r2_hidden(sK15(X0,X1,X2),X2) & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 2.42/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f57,f58])).
% 2.42/0.69  fof(f58,plain,(
% 2.42/0.69    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK15(X0,X1,X2),X0) & r2_hidden(sK15(X0,X1,X2),X2) & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))))),
% 2.42/0.69    introduced(choice_axiom,[])).
% 2.42/0.69  fof(f57,plain,(
% 2.42/0.69    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 2.42/0.69    inference(rectify,[],[f56])).
% 2.42/0.69  fof(f56,plain,(
% 2.42/0.69    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP3(X1,X0,X2)))),
% 2.42/0.69    inference(nnf_transformation,[],[f30])).
% 2.42/0.69  fof(f289,plain,(
% 2.42/0.69    ( ! [X14,X12,X15,X13] : (r4_lattice3(X14,sK16(X12,X13,a_2_2_lattice3(X14,X15)),X15) | ~l3_lattices(X14) | ~v4_lattice3(X14) | ~v10_lattices(X14) | v2_struct_0(X14) | sP5(X12,X13,a_2_2_lattice3(X14,X15))) )),
% 2.42/0.69    inference(resolution,[],[f285,f147])).
% 2.42/0.69  fof(f147,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~sP7(X0,X1,X2) | r4_lattice3(X1,X2,X0)) )),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f146])).
% 2.42/0.69  fof(f146,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (r4_lattice3(X1,X2,X0) | ~sP7(X0,X1,X2) | ~sP7(X0,X1,X2)) )),
% 2.42/0.69    inference(superposition,[],[f113,f112])).
% 2.42/0.69  fof(f113,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK17(X0,X1,X2),X0) | ~sP7(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f69])).
% 2.42/0.69  fof(f1277,plain,(
% 2.42/0.69    ( ! [X2] : (~r3_lattice3(sK11,X2,a_2_2_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) | ~m1_subset_1(X2,u1_struct_0(sK11)) | r3_lattices(sK11,X2,sK12)) ) | ~spl19_6),
% 2.42/0.69    inference(subsumption_resolution,[],[f1276,f75])).
% 2.42/0.69  fof(f1276,plain,(
% 2.42/0.69    ( ! [X2] : (r3_lattices(sK11,X2,sK12) | ~m1_subset_1(X2,u1_struct_0(sK11)) | ~r3_lattice3(sK11,X2,a_2_2_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) | v2_struct_0(sK11)) ) | ~spl19_6),
% 2.42/0.69    inference(subsumption_resolution,[],[f1275,f76])).
% 2.42/0.69  fof(f1275,plain,(
% 2.42/0.69    ( ! [X2] : (r3_lattices(sK11,X2,sK12) | ~m1_subset_1(X2,u1_struct_0(sK11)) | ~r3_lattice3(sK11,X2,a_2_2_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) | ~v10_lattices(sK11) | v2_struct_0(sK11)) ) | ~spl19_6),
% 2.42/0.69    inference(subsumption_resolution,[],[f1274,f77])).
% 2.42/0.69  fof(f1274,plain,(
% 2.42/0.69    ( ! [X2] : (r3_lattices(sK11,X2,sK12) | ~m1_subset_1(X2,u1_struct_0(sK11)) | ~r3_lattice3(sK11,X2,a_2_2_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11)) ) | ~spl19_6),
% 2.42/0.69    inference(subsumption_resolution,[],[f1273,f78])).
% 2.42/0.69  fof(f1273,plain,(
% 2.42/0.69    ( ! [X2] : (r3_lattices(sK11,X2,sK12) | ~m1_subset_1(X2,u1_struct_0(sK11)) | ~r3_lattice3(sK11,X2,a_2_2_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11)) ) | ~spl19_6),
% 2.42/0.69    inference(subsumption_resolution,[],[f1231,f192])).
% 2.42/0.69  fof(f1231,plain,(
% 2.42/0.69    ( ! [X2] : (r3_lattices(sK11,X2,sK12) | ~m1_subset_1(X2,u1_struct_0(sK11)) | ~r3_lattice3(sK11,X2,a_2_2_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) | ~sP2(sK12,sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11)) ) | ~spl19_6),
% 2.42/0.69    inference(superposition,[],[f234,f1059])).
% 2.42/0.69  fof(f1059,plain,(
% 2.42/0.69    sK12 = k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)) | ~spl19_6),
% 2.42/0.69    inference(avatar_component_clause,[],[f1057])).
% 2.42/0.69  fof(f1057,plain,(
% 2.42/0.69    spl19_6 <=> sK12 = k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))),
% 2.42/0.69    introduced(avatar_definition,[new_symbols(naming,[spl19_6])])).
% 2.42/0.69  fof(f234,plain,(
% 2.42/0.69    ( ! [X6,X4,X5] : (r3_lattices(X4,X6,k15_lattice3(X4,X5)) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~r3_lattice3(X4,X6,a_2_2_lattice3(X4,X5)) | ~sP2(k15_lattice3(X4,X5),X4) | ~l3_lattices(X4) | ~v4_lattice3(X4) | ~v10_lattices(X4) | v2_struct_0(X4)) )),
% 2.42/0.69    inference(superposition,[],[f207,f83])).
% 2.42/0.69  fof(f83,plain,(
% 2.42/0.69    ( ! [X0,X1] : (k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f13])).
% 2.42/0.69  fof(f13,plain,(
% 2.42/0.69    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.69    inference(flattening,[],[f12])).
% 2.42/0.69  fof(f12,plain,(
% 2.42/0.69    ! [X0] : (! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.69    inference(ennf_transformation,[],[f6])).
% 2.42/0.69  fof(f6,axiom,(
% 2.42/0.69    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 2.42/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).
% 2.42/0.69  fof(f207,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (r3_lattices(X0,X1,k16_lattice3(X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~sP2(k16_lattice3(X0,X2),X0)) )),
% 2.42/0.69    inference(resolution,[],[f90,f154])).
% 2.42/0.69  fof(f154,plain,(
% 2.42/0.69    ( ! [X0,X1] : (sP0(k16_lattice3(X0,X1),X0,X1) | ~sP2(k16_lattice3(X0,X1),X0)) )),
% 2.42/0.69    inference(resolution,[],[f123,f88])).
% 2.42/0.69  fof(f88,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | sP0(X2,X1,X0)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f50])).
% 2.42/0.69  fof(f123,plain,(
% 2.42/0.69    ( ! [X2,X1] : (sP1(X2,X1,k16_lattice3(X1,X2)) | ~sP2(k16_lattice3(X1,X2),X1)) )),
% 2.42/0.69    inference(equality_resolution,[],[f85])).
% 2.42/0.69  fof(f85,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (sP1(X2,X1,X0) | k16_lattice3(X1,X2) != X0 | ~sP2(X0,X1)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f47])).
% 2.42/0.69  fof(f90,plain,(
% 2.42/0.69    ( ! [X4,X2,X0,X1] : (~sP0(X0,X1,X2) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r3_lattices(X1,X4,X0)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f54])).
% 2.42/0.69  fof(f1206,plain,(
% 2.42/0.69    spl19_5),
% 2.42/0.69    inference(avatar_contradiction_clause,[],[f1205])).
% 2.42/0.69  fof(f1205,plain,(
% 2.42/0.69    $false | spl19_5),
% 2.42/0.69    inference(subsumption_resolution,[],[f1204,f79])).
% 2.42/0.69  fof(f1204,plain,(
% 2.42/0.69    ~m1_subset_1(sK12,u1_struct_0(sK11)) | spl19_5),
% 2.42/0.69    inference(subsumption_resolution,[],[f1197,f80])).
% 2.42/0.69  fof(f80,plain,(
% 2.42/0.69    r2_hidden(sK12,sK13)),
% 2.42/0.69    inference(cnf_transformation,[],[f45])).
% 2.42/0.69  fof(f1197,plain,(
% 2.42/0.69    ~r2_hidden(sK12,sK13) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | spl19_5),
% 2.42/0.69    inference(resolution,[],[f1190,f81])).
% 2.42/0.69  fof(f1190,plain,(
% 2.42/0.69    ( ! [X0] : (~r3_lattice3(sK11,X0,sK13) | ~r2_hidden(X0,sK13) | ~m1_subset_1(X0,u1_struct_0(sK11))) ) | spl19_5),
% 2.42/0.69    inference(resolution,[],[f1179,f125])).
% 2.42/0.69  fof(f1179,plain,(
% 2.42/0.69    ( ! [X0] : (~sP9(sK13,sK11,X0) | ~r2_hidden(X0,sK13)) ) | spl19_5),
% 2.42/0.69    inference(subsumption_resolution,[],[f1178,f75])).
% 2.42/0.69  fof(f1178,plain,(
% 2.42/0.69    ( ! [X0] : (~sP9(sK13,sK11,X0) | ~r2_hidden(X0,sK13) | v2_struct_0(sK11)) ) | spl19_5),
% 2.42/0.69    inference(subsumption_resolution,[],[f1177,f78])).
% 2.42/0.69  fof(f1177,plain,(
% 2.42/0.69    ( ! [X0] : (~sP9(sK13,sK11,X0) | ~r2_hidden(X0,sK13) | ~l3_lattices(sK11) | v2_struct_0(sK11)) ) | spl19_5),
% 2.42/0.69    inference(resolution,[],[f1176,f122])).
% 2.42/0.69  fof(f1176,plain,(
% 2.42/0.69    ( ! [X0] : (~sP10(X0,sK11,sK13) | ~sP9(sK13,sK11,X0) | ~r2_hidden(X0,sK13)) ) | spl19_5),
% 2.42/0.69    inference(subsumption_resolution,[],[f1173,f151])).
% 2.42/0.69  fof(f1173,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,sK13) | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~sP9(sK13,sK11,X0) | ~sP10(X0,sK11,sK13)) ) | spl19_5),
% 2.42/0.69    inference(resolution,[],[f1163,f117])).
% 2.42/0.69  fof(f1163,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(X0,sK13) | ~m1_subset_1(X0,u1_struct_0(sK11))) ) | spl19_5),
% 2.42/0.69    inference(subsumption_resolution,[],[f1162,f75])).
% 2.42/0.69  fof(f1162,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,sK13) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~m1_subset_1(X0,u1_struct_0(sK11)) | v2_struct_0(sK11)) ) | spl19_5),
% 2.42/0.69    inference(subsumption_resolution,[],[f1161,f78])).
% 2.42/0.69  fof(f1161,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,sK13) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~l3_lattices(sK11) | v2_struct_0(sK11)) ) | spl19_5),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f1157])).
% 2.42/0.69  fof(f1157,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,sK13) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~r2_hidden(X0,sK13) | ~l3_lattices(sK11) | v2_struct_0(sK11) | ~m1_subset_1(X0,u1_struct_0(sK11))) ) | spl19_5),
% 2.42/0.69    inference(resolution,[],[f1132,f360])).
% 2.42/0.69  fof(f360,plain,(
% 2.42/0.69    ( ! [X6,X4,X5] : (r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | v2_struct_0(X5) | ~m1_subset_1(X4,u1_struct_0(X5))) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f359,f101])).
% 2.42/0.69  fof(f359,plain,(
% 2.42/0.69    ( ! [X6,X4,X5] : (~m1_subset_1(X4,u1_struct_0(X5)) | ~r2_hidden(X4,X6) | ~l3_lattices(X5) | v2_struct_0(X5) | r4_lattice3(X5,X4,a_2_1_lattice3(X5,X6)) | ~sP4(X5,X4)) )),
% 2.42/0.69    inference(resolution,[],[f357,f96])).
% 2.42/0.69  fof(f96,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~sP3(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP4(X0,X1)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f55])).
% 2.42/0.69  fof(f357,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (sP3(X0,X2,a_2_1_lattice3(X2,X1)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f356,f138])).
% 2.42/0.69  fof(f138,plain,(
% 2.42/0.69    ( ! [X4,X5,X3] : (sP6(X3,sK15(X4,X3,X5)) | ~l3_lattices(X3) | v2_struct_0(X3) | sP3(X4,X3,X5)) )),
% 2.42/0.69    inference(resolution,[],[f108,f98])).
% 2.42/0.69  fof(f98,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) | sP3(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f59])).
% 2.42/0.69  fof(f356,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~sP6(X2,sK15(X0,X2,a_2_1_lattice3(X2,X1))) | sP3(X0,X2,a_2_1_lattice3(X2,X1)) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f355])).
% 2.42/0.69  fof(f355,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~sP6(X2,sK15(X0,X2,a_2_1_lattice3(X2,X1))) | sP3(X0,X2,a_2_1_lattice3(X2,X1)) | ~l3_lattices(X2) | v2_struct_0(X2) | sP3(X0,X2,a_2_1_lattice3(X2,X1))) )),
% 2.42/0.69    inference(resolution,[],[f225,f298])).
% 2.42/0.69  fof(f298,plain,(
% 2.42/0.69    ( ! [X14,X12,X15,X13] : (r3_lattice3(X14,sK15(X12,X13,a_2_1_lattice3(X14,X15)),X15) | ~l3_lattices(X14) | v2_struct_0(X14) | sP3(X12,X13,a_2_1_lattice3(X14,X15))) )),
% 2.42/0.69    inference(resolution,[],[f294,f153])).
% 2.42/0.69  fof(f153,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~sP9(X0,X1,X2) | r3_lattice3(X1,X2,X0)) )),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f152])).
% 2.42/0.69  fof(f152,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (r3_lattice3(X1,X2,X0) | ~sP9(X0,X1,X2) | ~sP9(X0,X1,X2)) )),
% 2.42/0.69    inference(superposition,[],[f120,f119])).
% 2.42/0.69  fof(f120,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK18(X0,X1,X2),X0) | ~sP9(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f74])).
% 2.42/0.69  fof(f294,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (sP9(X0,X1,sK15(X2,X3,a_2_1_lattice3(X1,X0))) | sP3(X2,X3,a_2_1_lattice3(X1,X0)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 2.42/0.69    inference(resolution,[],[f179,f122])).
% 2.42/0.69  fof(f179,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (~sP10(sK15(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0) | sP9(X0,X1,sK15(X2,X3,a_2_1_lattice3(X1,X0))) | sP3(X2,X3,a_2_1_lattice3(X1,X0))) )),
% 2.42/0.69    inference(resolution,[],[f116,f99])).
% 2.42/0.69  fof(f99,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (r2_hidden(sK15(X0,X1,X2),X2) | sP3(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f59])).
% 2.42/0.69  fof(f116,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | sP9(X2,X1,X0) | ~sP10(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f70])).
% 2.42/0.69  fof(f225,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X1,sK15(X0,X1,X3),X2) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~sP6(X1,sK15(X0,X1,X3)) | sP3(X0,X1,X3)) )),
% 2.42/0.69    inference(resolution,[],[f206,f100])).
% 2.42/0.69  fof(f100,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK15(X0,X1,X2),X0) | sP3(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f59])).
% 2.42/0.69  fof(f206,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (r1_lattices(X2,X3,X0) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | ~r3_lattice3(X2,X3,X1) | ~sP6(X2,X3)) )),
% 2.42/0.69    inference(resolution,[],[f104,f102])).
% 2.42/0.69  fof(f102,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (sP5(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | ~sP6(X0,X1)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f60])).
% 2.42/0.69  fof(f104,plain,(
% 2.42/0.69    ( ! [X4,X2,X0,X1] : (~sP5(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f64])).
% 2.42/0.69  fof(f1132,plain,(
% 2.42/0.69    ( ! [X0] : (~r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(X0,sK13) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~m1_subset_1(X0,u1_struct_0(sK11))) ) | spl19_5),
% 2.42/0.69    inference(subsumption_resolution,[],[f1131,f75])).
% 2.42/0.69  fof(f1131,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,sK13) | ~r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~m1_subset_1(X0,u1_struct_0(sK11)) | v2_struct_0(sK11)) ) | spl19_5),
% 2.42/0.69    inference(subsumption_resolution,[],[f1130,f76])).
% 2.42/0.69  fof(f1130,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,sK13) | ~r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~v10_lattices(sK11) | v2_struct_0(sK11)) ) | spl19_5),
% 2.42/0.69    inference(subsumption_resolution,[],[f1129,f77])).
% 2.42/0.69  fof(f1129,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,sK13) | ~r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11)) ) | spl19_5),
% 2.42/0.69    inference(subsumption_resolution,[],[f1128,f78])).
% 2.42/0.69  fof(f1128,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,sK13) | ~r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11)) ) | spl19_5),
% 2.42/0.69    inference(superposition,[],[f1055,f84])).
% 2.42/0.69  fof(f84,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f15])).
% 2.42/0.69  fof(f15,plain,(
% 2.42/0.69    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 2.42/0.69    inference(flattening,[],[f14])).
% 2.42/0.69  fof(f14,plain,(
% 2.42/0.69    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | (~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 2.42/0.69    inference(ennf_transformation,[],[f7])).
% 2.42/0.69  fof(f7,axiom,(
% 2.42/0.69    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 2.42/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).
% 2.42/0.69  fof(f1055,plain,(
% 2.42/0.69    ~r2_hidden(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK13) | spl19_5),
% 2.42/0.69    inference(avatar_component_clause,[],[f1053])).
% 2.42/0.69  fof(f1053,plain,(
% 2.42/0.69    spl19_5 <=> r2_hidden(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK13)),
% 2.42/0.69    introduced(avatar_definition,[new_symbols(naming,[spl19_5])])).
% 2.42/0.69  fof(f1144,plain,(
% 2.42/0.69    spl19_8 | ~spl19_4),
% 2.42/0.69    inference(avatar_split_clause,[],[f1143,f1049,f1065])).
% 2.42/0.69  fof(f1065,plain,(
% 2.42/0.69    spl19_8 <=> sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)))),
% 2.42/0.69    introduced(avatar_definition,[new_symbols(naming,[spl19_8])])).
% 2.42/0.69  fof(f1049,plain,(
% 2.42/0.69    spl19_4 <=> m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11))),
% 2.42/0.69    introduced(avatar_definition,[new_symbols(naming,[spl19_4])])).
% 2.42/0.69  fof(f1143,plain,(
% 2.42/0.69    sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) | ~spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1142,f75])).
% 2.42/0.69  fof(f1142,plain,(
% 2.42/0.69    sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) | v2_struct_0(sK11) | ~spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1134,f78])).
% 2.42/0.69  fof(f1134,plain,(
% 2.42/0.69    sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) | ~l3_lattices(sK11) | v2_struct_0(sK11) | ~spl19_4),
% 2.42/0.69    inference(resolution,[],[f1050,f108])).
% 2.42/0.69  fof(f1050,plain,(
% 2.42/0.69    m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11)) | ~spl19_4),
% 2.42/0.69    inference(avatar_component_clause,[],[f1049])).
% 2.42/0.69  fof(f1141,plain,(
% 2.42/0.69    spl19_7 | ~spl19_4),
% 2.42/0.69    inference(avatar_split_clause,[],[f1140,f1049,f1061])).
% 2.42/0.69  fof(f1061,plain,(
% 2.42/0.69    spl19_7 <=> sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11)),
% 2.42/0.69    introduced(avatar_definition,[new_symbols(naming,[spl19_7])])).
% 2.42/0.69  fof(f1140,plain,(
% 2.42/0.69    sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11) | ~spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1139,f75])).
% 2.42/0.69  fof(f1139,plain,(
% 2.42/0.69    sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11) | v2_struct_0(sK11) | ~spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1138,f76])).
% 2.42/0.69  fof(f1138,plain,(
% 2.42/0.69    sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | ~spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1137,f77])).
% 2.42/0.69  fof(f1137,plain,(
% 2.42/0.69    sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | ~spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1133,f78])).
% 2.42/0.69  fof(f1133,plain,(
% 2.42/0.69    sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | ~spl19_4),
% 2.42/0.69    inference(resolution,[],[f1050,f94])).
% 2.42/0.69  fof(f1121,plain,(
% 2.42/0.69    spl19_4),
% 2.42/0.69    inference(avatar_contradiction_clause,[],[f1120])).
% 2.42/0.69  fof(f1120,plain,(
% 2.42/0.69    $false | spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1119,f79])).
% 2.42/0.69  fof(f1119,plain,(
% 2.42/0.69    ~m1_subset_1(sK12,u1_struct_0(sK11)) | spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1112,f80])).
% 2.42/0.69  fof(f1112,plain,(
% 2.42/0.69    ~r2_hidden(sK12,sK13) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | spl19_4),
% 2.42/0.69    inference(resolution,[],[f1105,f81])).
% 2.42/0.69  fof(f1105,plain,(
% 2.42/0.69    ( ! [X0] : (~r3_lattice3(sK11,X0,sK13) | ~r2_hidden(X0,sK13) | ~m1_subset_1(X0,u1_struct_0(sK11))) ) | spl19_4),
% 2.42/0.69    inference(resolution,[],[f1104,f125])).
% 2.42/0.69  fof(f1104,plain,(
% 2.42/0.69    ( ! [X0] : (~sP9(sK13,sK11,X0) | ~r2_hidden(X0,sK13)) ) | spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1103,f75])).
% 2.42/0.69  fof(f1103,plain,(
% 2.42/0.69    ( ! [X0] : (~sP9(sK13,sK11,X0) | ~r2_hidden(X0,sK13) | v2_struct_0(sK11)) ) | spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1102,f78])).
% 2.42/0.69  fof(f1102,plain,(
% 2.42/0.69    ( ! [X0] : (~sP9(sK13,sK11,X0) | ~r2_hidden(X0,sK13) | ~l3_lattices(sK11) | v2_struct_0(sK11)) ) | spl19_4),
% 2.42/0.69    inference(resolution,[],[f1101,f122])).
% 2.42/0.69  fof(f1101,plain,(
% 2.42/0.69    ( ! [X0] : (~sP10(X0,sK11,sK13) | ~sP9(sK13,sK11,X0) | ~r2_hidden(X0,sK13)) ) | spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1098,f151])).
% 2.42/0.69  fof(f1098,plain,(
% 2.42/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK11)) | ~r2_hidden(X0,sK13) | ~sP9(sK13,sK11,X0) | ~sP10(X0,sK11,sK13)) ) | spl19_4),
% 2.42/0.69    inference(resolution,[],[f1083,f117])).
% 2.42/0.69  fof(f1083,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~r2_hidden(X0,sK13)) ) | spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1082,f75])).
% 2.42/0.69  fof(f1082,plain,(
% 2.42/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK11)) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(X0,sK13) | v2_struct_0(sK11)) ) | spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1081,f78])).
% 2.42/0.69  fof(f1081,plain,(
% 2.42/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK11)) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(X0,sK13) | ~l3_lattices(sK11) | v2_struct_0(sK11)) ) | spl19_4),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f1077])).
% 2.42/0.69  fof(f1077,plain,(
% 2.42/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK11)) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(X0,sK13) | ~l3_lattices(sK11) | v2_struct_0(sK11) | ~m1_subset_1(X0,u1_struct_0(sK11))) ) | spl19_4),
% 2.42/0.69    inference(resolution,[],[f1076,f360])).
% 2.42/0.69  fof(f1076,plain,(
% 2.42/0.69    ( ! [X0] : (~r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13)) | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13))) ) | spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1075,f75])).
% 2.42/0.69  fof(f1075,plain,(
% 2.42/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK11)) | ~r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | v2_struct_0(sK11)) ) | spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1074,f76])).
% 2.42/0.69  fof(f1074,plain,(
% 2.42/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK11)) | ~r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~v10_lattices(sK11) | v2_struct_0(sK11)) ) | spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1073,f77])).
% 2.42/0.69  fof(f1073,plain,(
% 2.42/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK11)) | ~r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11)) ) | spl19_4),
% 2.42/0.69    inference(subsumption_resolution,[],[f1072,f78])).
% 2.42/0.69  fof(f1072,plain,(
% 2.42/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK11)) | ~r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11)) ) | spl19_4),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f1071])).
% 2.42/0.69  fof(f1071,plain,(
% 2.42/0.69    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK11)) | ~r4_lattice3(sK11,X0,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(X0,a_2_1_lattice3(sK11,sK13)) | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11)) ) | spl19_4),
% 2.42/0.69    inference(superposition,[],[f1051,f84])).
% 2.42/0.69  fof(f1051,plain,(
% 2.42/0.69    ~m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11)) | spl19_4),
% 2.42/0.69    inference(avatar_component_clause,[],[f1049])).
% 2.42/0.69  fof(f1068,plain,(
% 2.42/0.69    ~spl19_4 | ~spl19_5 | spl19_6 | ~spl19_7 | ~spl19_8),
% 2.42/0.69    inference(avatar_split_clause,[],[f1047,f1065,f1061,f1057,f1053,f1049])).
% 2.42/0.69  fof(f1047,plain,(
% 2.42/0.69    ~sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) | ~sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11) | sK12 = k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK13) | ~m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11))),
% 2.42/0.69    inference(subsumption_resolution,[],[f1046,f77])).
% 2.42/0.69  fof(f1046,plain,(
% 2.42/0.69    ~sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) | ~sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11) | ~v4_lattice3(sK11) | sK12 = k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK13) | ~m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11))),
% 2.42/0.69    inference(subsumption_resolution,[],[f1045,f78])).
% 2.42/0.69  fof(f1045,plain,(
% 2.42/0.69    ~l3_lattices(sK11) | ~sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) | ~sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11) | ~v4_lattice3(sK11) | sK12 = k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK13) | ~m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11))),
% 2.42/0.69    inference(subsumption_resolution,[],[f1044,f75])).
% 2.42/0.69  fof(f1044,plain,(
% 2.42/0.69    v2_struct_0(sK11) | ~l3_lattices(sK11) | ~sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) | ~sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11) | ~v4_lattice3(sK11) | sK12 = k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK13) | ~m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11))),
% 2.42/0.69    inference(subsumption_resolution,[],[f1030,f76])).
% 2.42/0.69  fof(f1030,plain,(
% 2.42/0.69    ~v10_lattices(sK11) | v2_struct_0(sK11) | ~l3_lattices(sK11) | ~sP6(sK11,k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13))) | ~sP2(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK11) | ~v4_lattice3(sK11) | sK12 = k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)) | ~r2_hidden(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),sK13) | ~m1_subset_1(k15_lattice3(sK11,a_2_1_lattice3(sK11,sK13)),u1_struct_0(sK11))),
% 2.42/0.69    inference(resolution,[],[f1024,f859])).
% 2.42/0.69  fof(f859,plain,(
% 2.42/0.69    ( ! [X0] : (~r3_lattice3(sK11,X0,sK13) | sK12 = X0 | ~r2_hidden(X0,sK13) | ~m1_subset_1(X0,u1_struct_0(sK11))) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f858,f79])).
% 2.42/0.69  fof(f858,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,sK13) | sK12 = X0 | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~r3_lattice3(sK11,X0,sK13) | ~m1_subset_1(X0,u1_struct_0(sK11))) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f857,f77])).
% 2.42/0.69  fof(f857,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,sK13) | sK12 = X0 | ~v4_lattice3(sK11) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~r3_lattice3(sK11,X0,sK13) | ~m1_subset_1(X0,u1_struct_0(sK11))) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f856,f75])).
% 2.42/0.69  fof(f856,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,sK13) | sK12 = X0 | v2_struct_0(sK11) | ~v4_lattice3(sK11) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~r3_lattice3(sK11,X0,sK13) | ~m1_subset_1(X0,u1_struct_0(sK11))) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f855,f80])).
% 2.42/0.69  fof(f855,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,sK13) | ~r2_hidden(sK12,sK13) | sK12 = X0 | v2_struct_0(sK11) | ~v4_lattice3(sK11) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~r3_lattice3(sK11,X0,sK13) | ~m1_subset_1(X0,u1_struct_0(sK11))) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f854,f78])).
% 2.42/0.69  fof(f854,plain,(
% 2.42/0.69    ( ! [X0] : (~r2_hidden(X0,sK13) | ~l3_lattices(sK11) | ~r2_hidden(sK12,sK13) | sK12 = X0 | v2_struct_0(sK11) | ~v4_lattice3(sK11) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~r3_lattice3(sK11,X0,sK13) | ~m1_subset_1(X0,u1_struct_0(sK11))) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f840,f76])).
% 2.42/0.69  fof(f840,plain,(
% 2.42/0.69    ( ! [X0] : (~v10_lattices(sK11) | ~r2_hidden(X0,sK13) | ~l3_lattices(sK11) | ~r2_hidden(sK12,sK13) | sK12 = X0 | v2_struct_0(sK11) | ~v4_lattice3(sK11) | ~m1_subset_1(sK12,u1_struct_0(sK11)) | ~r3_lattice3(sK11,X0,sK13) | ~m1_subset_1(X0,u1_struct_0(sK11))) )),
% 2.42/0.69    inference(resolution,[],[f835,f81])).
% 2.42/0.69  fof(f835,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X0,X3,X2) | ~v10_lattices(X0) | ~r2_hidden(X1,X2) | ~l3_lattices(X0) | ~r2_hidden(X3,X2) | X1 = X3 | v2_struct_0(X0) | ~v4_lattice3(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 2.42/0.69    inference(resolution,[],[f830,f125])).
% 2.42/0.69  fof(f830,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (~sP9(X2,X0,X1) | ~v4_lattice3(X0) | ~v10_lattices(X0) | ~r2_hidden(X1,X2) | ~l3_lattices(X0) | ~r2_hidden(X3,X2) | X1 = X3 | v2_struct_0(X0) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 2.42/0.69    inference(resolution,[],[f825,f125])).
% 2.42/0.69  fof(f825,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (~sP9(X3,X1,X2) | v2_struct_0(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | ~r2_hidden(X0,X3) | ~l3_lattices(X1) | ~r2_hidden(X2,X3) | X0 = X2 | ~sP9(X3,X1,X0)) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f824,f122])).
% 2.42/0.69  fof(f824,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (X0 = X2 | v2_struct_0(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | ~r2_hidden(X0,X3) | ~l3_lattices(X1) | ~r2_hidden(X2,X3) | ~sP9(X3,X1,X2) | ~sP9(X3,X1,X0) | ~sP10(X0,X1,X3)) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f823,f151])).
% 2.42/0.69  fof(f823,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (X0 = X2 | v2_struct_0(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | ~r2_hidden(X0,X3) | ~l3_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r2_hidden(X2,X3) | ~sP9(X3,X1,X2) | ~sP9(X3,X1,X0) | ~sP10(X0,X1,X3)) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f820,f151])).
% 2.42/0.69  fof(f820,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | X0 = X2 | v2_struct_0(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | ~r2_hidden(X0,X3) | ~l3_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~r2_hidden(X2,X3) | ~sP9(X3,X1,X2) | ~sP9(X3,X1,X0) | ~sP10(X0,X1,X3)) )),
% 2.42/0.69    inference(resolution,[],[f817,f117])).
% 2.42/0.69  fof(f817,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (~r2_hidden(X1,a_2_1_lattice3(X0,X3)) | ~m1_subset_1(X1,u1_struct_0(X0)) | X1 = X2 | v2_struct_0(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | ~r2_hidden(X1,X3) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X3) | ~sP9(X3,X0,X2)) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f814,f122])).
% 2.42/0.69  fof(f814,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | X1 = X2 | ~r2_hidden(X1,a_2_1_lattice3(X0,X3)) | ~v4_lattice3(X0) | ~v10_lattices(X0) | ~r2_hidden(X1,X3) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X3) | ~sP9(X3,X0,X2) | ~sP10(X2,X0,X3)) )),
% 2.42/0.69    inference(resolution,[],[f810,f117])).
% 2.42/0.69  fof(f810,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (~r2_hidden(X2,a_2_1_lattice3(X0,X3)) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | X1 = X2 | ~r2_hidden(X1,a_2_1_lattice3(X0,X3)) | ~v4_lattice3(X0) | ~v10_lattices(X0) | ~r2_hidden(X1,X3) | ~l3_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X3)) )),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f804])).
% 2.42/0.69  fof(f804,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | X1 = X2 | ~r2_hidden(X1,a_2_1_lattice3(X0,X3)) | ~v4_lattice3(X0) | ~v10_lattices(X0) | ~r2_hidden(X1,X3) | ~r2_hidden(X2,a_2_1_lattice3(X0,X3)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X2,X3) | ~l3_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 2.42/0.69    inference(resolution,[],[f363,f360])).
% 2.42/0.69  fof(f363,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (~r4_lattice3(X2,X3,a_2_1_lattice3(X2,X1)) | ~l3_lattices(X2) | v2_struct_0(X2) | ~m1_subset_1(X0,u1_struct_0(X2)) | X0 = X3 | ~r2_hidden(X0,a_2_1_lattice3(X2,X1)) | ~v4_lattice3(X2) | ~v10_lattices(X2) | ~r2_hidden(X0,X1) | ~r2_hidden(X3,a_2_1_lattice3(X2,X1)) | ~m1_subset_1(X3,u1_struct_0(X2))) )),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f361])).
% 2.42/0.69  fof(f361,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X1) | ~l3_lattices(X2) | v2_struct_0(X2) | ~m1_subset_1(X0,u1_struct_0(X2)) | X0 = X3 | ~r2_hidden(X0,a_2_1_lattice3(X2,X1)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | ~r4_lattice3(X2,X3,a_2_1_lattice3(X2,X1)) | ~r2_hidden(X3,a_2_1_lattice3(X2,X1)) | ~m1_subset_1(X3,u1_struct_0(X2))) )),
% 2.42/0.69    inference(resolution,[],[f360,f220])).
% 2.42/0.69  fof(f220,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (~r4_lattice3(X0,X3,X1) | X2 = X3 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~r4_lattice3(X0,X2,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f219])).
% 2.42/0.69  fof(f219,plain,(
% 2.42/0.69    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r4_lattice3(X0,X3,X1) | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~r4_lattice3(X0,X2,X1) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 2.42/0.69    inference(superposition,[],[f84,f84])).
% 2.42/0.69  fof(f1024,plain,(
% 2.42/0.69    ( ! [X4,X3] : (r3_lattice3(X3,k15_lattice3(X3,a_2_1_lattice3(X3,X4)),X4) | ~v10_lattices(X3) | v2_struct_0(X3) | ~l3_lattices(X3) | ~sP6(X3,k15_lattice3(X3,a_2_1_lattice3(X3,X4))) | ~sP2(k15_lattice3(X3,a_2_1_lattice3(X3,X4)),X3) | ~v4_lattice3(X3)) )),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f1021])).
% 2.42/0.69  fof(f1021,plain,(
% 2.42/0.69    ( ! [X4,X3] : (~v4_lattice3(X3) | ~v10_lattices(X3) | v2_struct_0(X3) | ~l3_lattices(X3) | ~sP6(X3,k15_lattice3(X3,a_2_1_lattice3(X3,X4))) | ~sP2(k15_lattice3(X3,a_2_1_lattice3(X3,X4)),X3) | r3_lattice3(X3,k15_lattice3(X3,a_2_1_lattice3(X3,X4)),X4) | ~sP6(X3,k15_lattice3(X3,a_2_1_lattice3(X3,X4)))) )),
% 2.42/0.69    inference(resolution,[],[f1019,f103])).
% 2.42/0.69  fof(f1019,plain,(
% 2.42/0.69    ( ! [X0,X1] : (sP5(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~sP6(X0,k15_lattice3(X0,a_2_1_lattice3(X0,X1))) | ~sP2(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0)) )),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f1014])).
% 2.42/0.69  fof(f1014,plain,(
% 2.42/0.69    ( ! [X0,X1] : (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP5(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1) | ~sP6(X0,k15_lattice3(X0,a_2_1_lattice3(X0,X1))) | ~sP2(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0) | sP5(k15_lattice3(X0,a_2_1_lattice3(X0,X1)),X0,X1)) )),
% 2.42/0.69    inference(resolution,[],[f739,f106])).
% 2.42/0.69  fof(f739,plain,(
% 2.42/0.69    ( ! [X14,X12,X13] : (~r2_hidden(sK16(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14),X13) | ~l3_lattices(X12) | ~v4_lattice3(X12) | ~v10_lattices(X12) | v2_struct_0(X12) | sP5(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14) | ~sP6(X12,k15_lattice3(X12,a_2_1_lattice3(X12,X13))) | ~sP2(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12)) )),
% 2.42/0.69    inference(subsumption_resolution,[],[f732,f105])).
% 2.42/0.69  fof(f105,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) | sP5(X0,X1,X2)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f64])).
% 2.42/0.69  fof(f732,plain,(
% 2.42/0.69    ( ! [X14,X12,X13] : (~sP6(X12,k15_lattice3(X12,a_2_1_lattice3(X12,X13))) | ~l3_lattices(X12) | ~v4_lattice3(X12) | ~v10_lattices(X12) | v2_struct_0(X12) | sP5(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14) | ~m1_subset_1(sK16(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14),u1_struct_0(X12)) | ~r2_hidden(sK16(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14),X13) | ~sP2(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12)) )),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f727])).
% 2.42/0.69  fof(f727,plain,(
% 2.42/0.69    ( ! [X14,X12,X13] : (~sP6(X12,k15_lattice3(X12,a_2_1_lattice3(X12,X13))) | ~l3_lattices(X12) | ~v4_lattice3(X12) | ~v10_lattices(X12) | v2_struct_0(X12) | sP5(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14) | ~m1_subset_1(sK16(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14),u1_struct_0(X12)) | ~r2_hidden(sK16(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12,X14),X13) | ~sP2(k15_lattice3(X12,a_2_1_lattice3(X12,X13)),X12) | ~l3_lattices(X12) | ~v4_lattice3(X12) | ~v10_lattices(X12) | v2_struct_0(X12)) )),
% 2.42/0.69    inference(resolution,[],[f708,f210])).
% 2.42/0.69  fof(f210,plain,(
% 2.42/0.69    ( ! [X4,X3] : (r3_lattice3(X3,k15_lattice3(X3,X4),a_2_2_lattice3(X3,X4)) | ~sP2(k15_lattice3(X3,X4),X3) | ~l3_lattices(X3) | ~v4_lattice3(X3) | ~v10_lattices(X3) | v2_struct_0(X3)) )),
% 2.42/0.69    inference(superposition,[],[f155,f83])).
% 2.42/0.69  fof(f155,plain,(
% 2.42/0.69    ( ! [X2,X3] : (r3_lattice3(X2,k16_lattice3(X2,X3),X3) | ~sP2(k16_lattice3(X2,X3),X2)) )),
% 2.42/0.69    inference(resolution,[],[f123,f87])).
% 2.42/0.69  fof(f87,plain,(
% 2.42/0.69    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | r3_lattice3(X1,X2,X0)) )),
% 2.42/0.69    inference(cnf_transformation,[],[f50])).
% 2.42/0.69  fof(f708,plain,(
% 2.42/0.69    ( ! [X6,X4,X8,X7,X5] : (~r3_lattice3(X4,X5,a_2_2_lattice3(X6,a_2_1_lattice3(X6,X7))) | ~sP6(X4,X5) | ~l3_lattices(X6) | ~v4_lattice3(X6) | ~v10_lattices(X6) | v2_struct_0(X6) | sP5(X5,X4,X8) | ~m1_subset_1(sK16(X5,X4,X8),u1_struct_0(X6)) | ~r2_hidden(sK16(X5,X4,X8),X7)) )),
% 2.42/0.69    inference(duplicate_literal_removal,[],[f707])).
% 2.42/0.69  fof(f707,plain,(
% 2.42/0.69    ( ! [X6,X4,X8,X7,X5] : (~sP6(X4,X5) | ~r3_lattice3(X4,X5,a_2_2_lattice3(X6,a_2_1_lattice3(X6,X7))) | ~l3_lattices(X6) | ~v4_lattice3(X6) | ~v10_lattices(X6) | v2_struct_0(X6) | sP5(X5,X4,X8) | ~m1_subset_1(sK16(X5,X4,X8),u1_struct_0(X6)) | ~r2_hidden(sK16(X5,X4,X8),X7) | ~l3_lattices(X6) | v2_struct_0(X6) | ~m1_subset_1(sK16(X5,X4,X8),u1_struct_0(X6))) )),
% 2.42/0.69    inference(resolution,[],[f475,f360])).
% 2.42/0.69  fof(f475,plain,(
% 2.42/0.69    ( ! [X6,X4,X8,X7,X5] : (~r4_lattice3(X7,sK16(X4,X5,X6),X8) | ~sP6(X5,X4) | ~r3_lattice3(X5,X4,a_2_2_lattice3(X7,X8)) | ~l3_lattices(X7) | ~v4_lattice3(X7) | ~v10_lattices(X7) | v2_struct_0(X7) | sP5(X4,X5,X6) | ~m1_subset_1(sK16(X4,X5,X6),u1_struct_0(X7))) )),
% 2.42/0.69    inference(resolution,[],[f459,f124])).
% 2.42/0.69  fof(f124,plain,(
% 2.42/0.69    ( ! [X0,X3,X1] : (sP7(X0,X1,X3) | ~r4_lattice3(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.42/0.69    inference(equality_resolution,[],[f114])).
% 2.42/0.70  fof(f114,plain,(
% 2.42/0.70    ( ! [X2,X0,X3,X1] : (sP7(X0,X1,X2) | ~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 2.42/0.70    inference(cnf_transformation,[],[f69])).
% 2.42/0.70  fof(f459,plain,(
% 2.42/0.70    ( ! [X4,X2,X0,X3,X1] : (~sP7(X3,X4,sK16(X1,X0,X2)) | sP5(X1,X0,X2) | ~sP6(X0,X1) | ~r3_lattice3(X0,X1,a_2_2_lattice3(X4,X3)) | ~l3_lattices(X4) | ~v4_lattice3(X4) | ~v10_lattices(X4) | v2_struct_0(X4)) )),
% 2.42/0.70    inference(resolution,[],[f229,f115])).
% 2.42/0.70  fof(f229,plain,(
% 2.42/0.70    ( ! [X6,X4,X7,X5,X3] : (~sP8(sK16(X4,X3,X7),X5,X6) | ~sP6(X3,X4) | sP5(X4,X3,X7) | ~sP7(X6,X5,sK16(X4,X3,X7)) | ~r3_lattice3(X3,X4,a_2_2_lattice3(X5,X6))) )),
% 2.42/0.70    inference(resolution,[],[f227,f110])).
% 2.42/0.70  fof(f110,plain,(
% 2.42/0.70    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~sP7(X2,X1,X0) | ~sP8(X0,X1,X2)) )),
% 2.42/0.70    inference(cnf_transformation,[],[f65])).
% 2.42/0.70  fof(f227,plain,(
% 2.42/0.70    ( ! [X6,X4,X7,X5] : (~r2_hidden(sK16(X4,X5,X6),X7) | ~r3_lattice3(X5,X4,X7) | ~sP6(X5,X4) | sP5(X4,X5,X6)) )),
% 2.42/0.70    inference(subsumption_resolution,[],[f226,f105])).
% 2.42/0.70  fof(f226,plain,(
% 2.42/0.70    ( ! [X6,X4,X7,X5] : (~m1_subset_1(sK16(X4,X5,X6),u1_struct_0(X5)) | ~r2_hidden(sK16(X4,X5,X6),X7) | ~r3_lattice3(X5,X4,X7) | ~sP6(X5,X4) | sP5(X4,X5,X6)) )),
% 2.42/0.70    inference(resolution,[],[f206,f107])).
% 2.42/0.70  % SZS output end Proof for theBenchmark
% 2.42/0.70  % (24941)------------------------------
% 2.42/0.70  % (24941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.42/0.70  % (24941)Termination reason: Refutation
% 2.42/0.70  
% 2.42/0.70  % (24941)Memory used [KB]: 7164
% 2.42/0.70  % (24941)Time elapsed: 0.253 s
% 2.42/0.70  % (24941)------------------------------
% 2.42/0.70  % (24941)------------------------------
% 2.42/0.70  % (24936)Success in time 0.349 s
%------------------------------------------------------------------------------
