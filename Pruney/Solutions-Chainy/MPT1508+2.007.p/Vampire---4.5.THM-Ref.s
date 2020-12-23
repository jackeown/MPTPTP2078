%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:43 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  180 (1160 expanded)
%              Number of leaves         :   27 ( 416 expanded)
%              Depth                    :   29
%              Number of atoms          :  735 (7313 expanded)
%              Number of equality atoms :   63 ( 912 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f516,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f398,f417,f423,f437,f493,f515])).

fof(f515,plain,
    ( ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_11 ),
    inference(avatar_contradiction_clause,[],[f514])).

fof(f514,plain,
    ( $false
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f513,f411])).

fof(f411,plain,
    ( r2_hidden(sK10,a_2_1_lattice3(sK9,sK11))
    | ~ spl16_5 ),
    inference(avatar_component_clause,[],[f410])).

fof(f410,plain,
    ( spl16_5
  <=> r2_hidden(sK10,a_2_1_lattice3(sK9,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).

fof(f513,plain,
    ( ~ r2_hidden(sK10,a_2_1_lattice3(sK9,sK11))
    | ~ spl16_4
    | spl16_6
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f509,f415])).

fof(f415,plain,
    ( ~ sP1(a_2_1_lattice3(sK9,sK11),sK9,sK10)
    | spl16_6 ),
    inference(avatar_component_clause,[],[f414])).

fof(f414,plain,
    ( spl16_6
  <=> sP1(a_2_1_lattice3(sK9,sK11),sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f509,plain,
    ( sP1(a_2_1_lattice3(sK9,sK11),sK9,sK10)
    | ~ r2_hidden(sK10,a_2_1_lattice3(sK9,sK11))
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(resolution,[],[f508,f218])).

fof(f218,plain,(
    ! [X2] :
      ( ~ r4_lattice3(sK9,sK10,X2)
      | sP1(X2,sK9,sK10)
      | ~ r2_hidden(sK10,X2) ) ),
    inference(resolution,[],[f216,f73])).

% (25834)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X2,X1,X0)
      | sP1(X0,X1,X2)
      | ~ r4_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ~ sP0(X2,X1,X0)
        | ~ r4_lattice3(X1,X2,X0) )
      & ( ( sP0(X2,X1,X0)
          & r4_lattice3(X1,X2,X0) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ~ sP0(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP0(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ~ sP0(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP0(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ( sP0(X2,X0,X1)
        & r4_lattice3(X0,X2,X1) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f216,plain,(
    ! [X0] :
      ( sP0(sK10,sK9,X0)
      | ~ r2_hidden(sK10,X0) ) ),
    inference(subsumption_resolution,[],[f215,f61])).

fof(f61,plain,(
    ~ v2_struct_0(sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK10 != k16_lattice3(sK9,sK11)
    & r3_lattice3(sK9,sK10,sK11)
    & r2_hidden(sK10,sK11)
    & m1_subset_1(sK10,u1_struct_0(sK9))
    & l3_lattices(sK9)
    & v4_lattice3(sK9)
    & v10_lattices(sK9)
    & ~ v2_struct_0(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f9,f35,f34,f33])).

fof(f33,plain,
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
              ( k16_lattice3(sK9,X2) != X1
              & r3_lattice3(sK9,X1,X2)
              & r2_hidden(X1,X2) )
          & m1_subset_1(X1,u1_struct_0(sK9)) )
      & l3_lattices(sK9)
      & v4_lattice3(sK9)
      & v10_lattices(sK9)
      & ~ v2_struct_0(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k16_lattice3(sK9,X2) != X1
            & r3_lattice3(sK9,X1,X2)
            & r2_hidden(X1,X2) )
        & m1_subset_1(X1,u1_struct_0(sK9)) )
   => ( ? [X2] :
          ( k16_lattice3(sK9,X2) != sK10
          & r3_lattice3(sK9,sK10,X2)
          & r2_hidden(sK10,X2) )
      & m1_subset_1(sK10,u1_struct_0(sK9)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( k16_lattice3(sK9,X2) != sK10
        & r3_lattice3(sK9,sK10,X2)
        & r2_hidden(sK10,X2) )
   => ( sK10 != k16_lattice3(sK9,sK11)
      & r3_lattice3(sK9,sK10,sK11)
      & r2_hidden(sK10,sK11) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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

fof(f215,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK10,X0)
      | sP0(sK10,sK9,X0)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f210,f64])).

fof(f64,plain,(
    l3_lattices(sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f210,plain,(
    ! [X0] :
      ( ~ r2_hidden(sK10,X0)
      | sP0(sK10,sK9,X0)
      | ~ l3_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(resolution,[],[f209,f65])).

fof(f65,plain,(
    m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(cnf_transformation,[],[f36])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | sP0(X0,X2,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f208])).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | sP0(X0,X2,X1)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2)
      | sP0(X0,X2,X1) ) ),
    inference(resolution,[],[f206,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( sP4(X0,sK12(X1,X0,X2))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | sP0(X1,X0,X2) ) ),
    inference(resolution,[],[f86,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK12(X0,X1,X2))
          & r4_lattice3(X1,sK12(X0,X1,X2),X2)
          & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f43,f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r4_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK12(X0,X1,X2))
        & r4_lattice3(X1,sK12(X0,X1,X2),X2)
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ? [X3] :
            ( ~ r1_lattices(X1,X0,X3)
            & r4_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ( sP0(X2,X0,X1)
        | ? [X3] :
            ( ~ r1_lattices(X0,X2,X3)
            & r4_lattice3(X0,X3,X1)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r1_lattices(X0,X2,X3)
            | ~ r4_lattice3(X0,X3,X1)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP0(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X0,X1)
    <=> ! [X3] :
          ( r1_lattices(X0,X2,X3)
          | ~ r4_lattice3(X0,X3,X1)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP4(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP4(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f25,f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP3(X1,X0,X2) )
      | ~ sP4(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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

fof(f206,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X1,sK12(X0,X1,X2))
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | sP0(X0,X1,X2) ) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_hidden(X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ sP4(X1,sK12(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f180,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK12(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f180,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X0,X3,sK12(X1,X0,X2))
      | sP0(X1,X0,X2)
      | ~ r2_hidden(X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ sP4(X0,sK12(X1,X0,X2)) ) ),
    inference(resolution,[],[f104,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK13(X0,X1,X2),X0)
          & r2_hidden(sK13(X0,X1,X2),X2)
          & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f48,f49])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK13(X0,X1,X2),X0)
        & r2_hidden(sK13(X0,X1,X2),X2)
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(rectify,[],[f47])).

fof(f47,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( sP3(sK12(X0,X1,X2),X1,X2)
      | ~ sP4(X1,sK12(X0,X1,X2))
      | sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f80,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK12(X0,X1,X2),X2)
      | sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_lattice3(X0,X1,X2)
      | sP3(X1,X0,X2)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP3(X1,X0,X2) )
          & ( sP3(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP4(X0,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f508,plain,
    ( r4_lattice3(sK9,sK10,a_2_1_lattice3(sK9,sK11))
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f507,f109])).

fof(f109,plain,(
    sP4(sK9,sK10) ),
    inference(subsumption_resolution,[],[f108,f61])).

fof(f108,plain,
    ( sP4(sK9,sK10)
    | v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f105,f64])).

fof(f105,plain,
    ( sP4(sK9,sK10)
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(resolution,[],[f86,f65])).

fof(f507,plain,
    ( r4_lattice3(sK9,sK10,a_2_1_lattice3(sK9,sK11))
    | ~ sP4(sK9,sK10)
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(resolution,[],[f503,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f503,plain,
    ( sP3(sK10,sK9,a_2_1_lattice3(sK9,sK11))
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f502,f66])).

fof(f66,plain,(
    r2_hidden(sK10,sK11) ),
    inference(cnf_transformation,[],[f36])).

fof(f502,plain,
    ( ~ r2_hidden(sK10,sK11)
    | sP3(sK10,sK9,a_2_1_lattice3(sK9,sK11))
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f499,f65])).

fof(f499,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK9))
    | ~ r2_hidden(sK10,sK11)
    | sP3(sK10,sK9,a_2_1_lattice3(sK9,sK11))
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(resolution,[],[f497,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK13(X0,X1,X2),X0)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f497,plain,
    ( ! [X0] :
        ( r1_lattices(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK9))
        | ~ r2_hidden(X0,sK11) )
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(resolution,[],[f496,f89])).

fof(f89,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK14(X0,X1,X2))
          & r2_hidden(sK14(X0,X1,X2),X2)
          & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK14(X0,X1,X2))
        & r2_hidden(sK14(X0,X1,X2),X2)
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( sP5(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f496,plain,
    ( sP5(sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)),sK9,sK11)
    | ~ spl16_4
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f495,f397])).

fof(f397,plain,
    ( sP6(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))
    | ~ spl16_4 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl16_4
  <=> sP6(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f495,plain,
    ( sP5(sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)),sK9,sK11)
    | ~ sP6(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))
    | ~ spl16_11 ),
    inference(resolution,[],[f492,f87])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattice3(X0,X1,X2)
      | sP5(X1,X0,X2)
      | ~ sP6(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

% (25828)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP5(X1,X0,X2) )
          & ( sP5(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP6(X0,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP5(X1,X0,X2) )
      | ~ sP6(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f492,plain,
    ( r3_lattice3(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)),sK11)
    | ~ spl16_11 ),
    inference(avatar_component_clause,[],[f490])).

fof(f490,plain,
    ( spl16_11
  <=> r3_lattice3(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)),sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).

fof(f493,plain,
    ( ~ spl16_3
    | spl16_11 ),
    inference(avatar_split_clause,[],[f355,f490,f391])).

fof(f391,plain,
    ( spl16_3
  <=> sP7(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).

fof(f355,plain,
    ( r3_lattice3(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)),sK11)
    | ~ sP7(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) ),
    inference(superposition,[],[f98,f352])).

fof(f352,plain,(
    sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)) = sK15(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) ),
    inference(subsumption_resolution,[],[f351,f68])).

fof(f68,plain,(
    sK10 != k16_lattice3(sK9,sK11) ),
    inference(cnf_transformation,[],[f36])).

fof(f351,plain,
    ( sK10 = k16_lattice3(sK9,sK11)
    | sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)) = sK15(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) ),
    inference(forward_demodulation,[],[f350,f145])).

fof(f145,plain,(
    ! [X0] : k16_lattice3(sK9,X0) = k15_lattice3(sK9,a_2_1_lattice3(sK9,X0)) ),
    inference(subsumption_resolution,[],[f144,f61])).

fof(f144,plain,(
    ! [X0] :
      ( k16_lattice3(sK9,X0) = k15_lattice3(sK9,a_2_1_lattice3(sK9,X0))
      | v2_struct_0(sK9) ) ),
    inference(resolution,[],[f79,f64])).

% (25821)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
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

fof(f350,plain,
    ( sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)) = sK15(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))
    | sK10 = k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)) ),
    inference(subsumption_resolution,[],[f349,f64])).

fof(f349,plain,
    ( sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)) = sK15(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))
    | sK10 = k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11))
    | ~ l3_lattices(sK9) ),
    inference(subsumption_resolution,[],[f348,f61])).

fof(f348,plain,
    ( v2_struct_0(sK9)
    | sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)) = sK15(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))
    | sK10 = k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11))
    | ~ l3_lattices(sK9) ),
    inference(resolution,[],[f347,f137])).

fof(f137,plain,(
    sP7(sK11,sK9,sK10) ),
    inference(subsumption_resolution,[],[f135,f65])).

fof(f135,plain,
    ( sP7(sK11,sK9,sK10)
    | ~ m1_subset_1(sK10,u1_struct_0(sK9)) ),
    inference(resolution,[],[f102,f67])).

fof(f67,plain,(
    r3_lattice3(sK9,sK10,sK11) ),
    inference(cnf_transformation,[],[f36])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( ~ r3_lattice3(X1,X3,X0)
      | sP7(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X0,X1,X2)
      | ~ r3_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r3_lattice3(X1,sK15(X0,X1,X2),X0)
          & sK15(X0,X1,X2) = X2
          & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f58,f59])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r3_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r3_lattice3(X1,sK15(X0,X1,X2),X0)
        & sK15(X0,X1,X2) = X2
        & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattice3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X2,X1,X0] :
      ( ( sP7(X2,X1,X0)
        | ! [X3] :
            ( ~ r3_lattice3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP7(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( sP7(X2,X1,X0)
    <=> ? [X3] :
          ( r3_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f347,plain,(
    ! [X0,X1] :
      ( ~ sP7(X1,X0,sK10)
      | v2_struct_0(X0)
      | sK13(sK10,sK9,a_2_1_lattice3(X0,X1)) = sK15(X1,X0,sK13(sK10,sK9,a_2_1_lattice3(X0,X1)))
      | sK10 = k15_lattice3(sK9,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f346,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( sP8(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( sP8(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f19,f31,f30])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> sP7(X2,X1,X0) )
      | ~ sP8(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      <=> ? [X3] :
            ( r3_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).

fof(f346,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | sK13(sK10,sK9,a_2_1_lattice3(X0,X1)) = sK15(X1,X0,sK13(sK10,sK9,a_2_1_lattice3(X0,X1)))
      | sK10 = k15_lattice3(sK9,a_2_1_lattice3(X0,X1))
      | ~ sP7(X1,X0,sK10)
      | ~ sP8(sK10,X0,X1) ) ),
    inference(resolution,[],[f281,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | ~ sP7(X2,X1,X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_lattice3(X1,X2))
          | ~ sP7(X2,X1,X0) )
        & ( sP7(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_lattice3(X1,X2)) ) )
      | ~ sP8(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f281,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK10,a_2_1_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | sK13(sK10,sK9,a_2_1_lattice3(X0,X1)) = sK15(X1,X0,sK13(sK10,sK9,a_2_1_lattice3(X0,X1)))
      | sK10 = k15_lattice3(sK9,a_2_1_lattice3(X0,X1)) ) ),
    inference(resolution,[],[f280,f176])).

fof(f176,plain,(
    ! [X0] :
      ( ~ sP1(X0,sK9,sK10)
      | sK10 = k15_lattice3(sK9,X0) ) ),
    inference(resolution,[],[f175,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ sP1(X2,X1,X0)
      | k15_lattice3(X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( ( k15_lattice3(X1,X2) = X0
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | k15_lattice3(X1,X2) != X0 ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ( ( k15_lattice3(X0,X1) = X2
          | ~ sP1(X1,X0,X2) )
        & ( sP1(X1,X0,X2)
          | k15_lattice3(X0,X1) != X2 ) )
      | ~ sP2(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ( k15_lattice3(X0,X1) = X2
      <=> sP1(X1,X0,X2) )
      | ~ sP2(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f175,plain,(
    ! [X0] : sP2(sK10,sK9,X0) ),
    inference(subsumption_resolution,[],[f174,f61])).

fof(f174,plain,(
    ! [X0] :
      ( sP2(sK10,sK9,X0)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f173,f62])).

fof(f62,plain,(
    v10_lattices(sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f173,plain,(
    ! [X0] :
      ( sP2(sK10,sK9,X0)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f172,f63])).

fof(f63,plain,(
    v4_lattice3(sK9) ),
    inference(cnf_transformation,[],[f36])).

fof(f172,plain,(
    ! [X0] :
      ( sP2(sK10,sK9,X0)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(subsumption_resolution,[],[f167,f64])).

fof(f167,plain,(
    ! [X0] :
      ( sP2(sK10,sK9,X0)
      | ~ l3_lattices(sK9)
      | ~ v4_lattice3(sK9)
      | ~ v10_lattices(sK9)
      | v2_struct_0(sK9) ) ),
    inference(resolution,[],[f103,f65])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP2(X2,X0,X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( sP2(X2,X0,X1)
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f11,f22,f21,f20])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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

fof(f280,plain,(
    ! [X24,X25] :
      ( sP1(a_2_1_lattice3(X24,X25),sK9,sK10)
      | sK13(sK10,sK9,a_2_1_lattice3(X24,X25)) = sK15(X25,X24,sK13(sK10,sK9,a_2_1_lattice3(X24,X25)))
      | ~ l3_lattices(X24)
      | v2_struct_0(X24)
      | ~ r2_hidden(sK10,a_2_1_lattice3(X24,X25)) ) ),
    inference(subsumption_resolution,[],[f273,f109])).

fof(f273,plain,(
    ! [X24,X25] :
      ( v2_struct_0(X24)
      | sK13(sK10,sK9,a_2_1_lattice3(X24,X25)) = sK15(X25,X24,sK13(sK10,sK9,a_2_1_lattice3(X24,X25)))
      | ~ l3_lattices(X24)
      | ~ sP4(sK9,sK10)
      | sP1(a_2_1_lattice3(X24,X25),sK9,sK10)
      | ~ r2_hidden(sK10,a_2_1_lattice3(X24,X25)) ) ),
    inference(resolution,[],[f238,f218])).

fof(f238,plain,(
    ! [X6,X8,X7,X5] :
      ( r4_lattice3(X7,X6,a_2_1_lattice3(X5,X8))
      | v2_struct_0(X5)
      | sK13(X6,X7,a_2_1_lattice3(X5,X8)) = sK15(X8,X5,sK13(X6,X7,a_2_1_lattice3(X5,X8)))
      | ~ l3_lattices(X5)
      | ~ sP4(X7,X6) ) ),
    inference(resolution,[],[f199,f81])).

fof(f199,plain,(
    ! [X10,X8,X11,X9] :
      ( sP3(X8,X9,a_2_1_lattice3(X10,X11))
      | ~ l3_lattices(X10)
      | v2_struct_0(X10)
      | sK13(X8,X9,a_2_1_lattice3(X10,X11)) = sK15(X11,X10,sK13(X8,X9,a_2_1_lattice3(X10,X11))) ) ),
    inference(resolution,[],[f196,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | sK15(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f196,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X0,X1,sK13(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP3(X2,X3,a_2_1_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f147,f100])).

fof(f147,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP8(sK13(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0)
      | sP7(X0,X1,sK13(X2,X3,a_2_1_lattice3(X1,X0)))
      | sP3(X2,X3,a_2_1_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f94,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK13(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_lattice3(X1,X2))
      | sP7(X2,X1,X0)
      | ~ sP8(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK15(X0,X1,X2),X0)
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f437,plain,(
    ~ spl16_6 ),
    inference(avatar_contradiction_clause,[],[f436])).

fof(f436,plain,
    ( $false
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f432,f68])).

fof(f432,plain,
    ( sK10 = k16_lattice3(sK9,sK11)
    | ~ spl16_6 ),
    inference(superposition,[],[f145,f426])).

fof(f426,plain,
    ( sK10 = k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11))
    | ~ spl16_6 ),
    inference(resolution,[],[f416,f176])).

fof(f416,plain,
    ( sP1(a_2_1_lattice3(sK9,sK11),sK9,sK10)
    | ~ spl16_6 ),
    inference(avatar_component_clause,[],[f414])).

fof(f423,plain,(
    spl16_5 ),
    inference(avatar_contradiction_clause,[],[f422])).

fof(f422,plain,
    ( $false
    | spl16_5 ),
    inference(subsumption_resolution,[],[f421,f61])).

fof(f421,plain,
    ( v2_struct_0(sK9)
    | spl16_5 ),
    inference(subsumption_resolution,[],[f420,f64])).

fof(f420,plain,
    ( ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | spl16_5 ),
    inference(resolution,[],[f419,f100])).

fof(f419,plain,
    ( ~ sP8(sK10,sK9,sK11)
    | spl16_5 ),
    inference(subsumption_resolution,[],[f418,f137])).

fof(f418,plain,
    ( ~ sP7(sK11,sK9,sK10)
    | ~ sP8(sK10,sK9,sK11)
    | spl16_5 ),
    inference(resolution,[],[f412,f95])).

fof(f412,plain,
    ( ~ r2_hidden(sK10,a_2_1_lattice3(sK9,sK11))
    | spl16_5 ),
    inference(avatar_component_clause,[],[f410])).

fof(f417,plain,
    ( ~ spl16_5
    | spl16_6
    | spl16_3 ),
    inference(avatar_split_clause,[],[f405,f391,f414,f410])).

fof(f405,plain,
    ( sP1(a_2_1_lattice3(sK9,sK11),sK9,sK10)
    | ~ r2_hidden(sK10,a_2_1_lattice3(sK9,sK11))
    | spl16_3 ),
    inference(resolution,[],[f404,f218])).

fof(f404,plain,
    ( r4_lattice3(sK9,sK10,a_2_1_lattice3(sK9,sK11))
    | spl16_3 ),
    inference(subsumption_resolution,[],[f403,f109])).

fof(f403,plain,
    ( r4_lattice3(sK9,sK10,a_2_1_lattice3(sK9,sK11))
    | ~ sP4(sK9,sK10)
    | spl16_3 ),
    inference(resolution,[],[f401,f81])).

fof(f401,plain,
    ( sP3(sK10,sK9,a_2_1_lattice3(sK9,sK11))
    | spl16_3 ),
    inference(subsumption_resolution,[],[f400,f61])).

fof(f400,plain,
    ( sP3(sK10,sK9,a_2_1_lattice3(sK9,sK11))
    | v2_struct_0(sK9)
    | spl16_3 ),
    inference(subsumption_resolution,[],[f399,f64])).

fof(f399,plain,
    ( sP3(sK10,sK9,a_2_1_lattice3(sK9,sK11))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9)
    | spl16_3 ),
    inference(resolution,[],[f393,f196])).

fof(f393,plain,
    ( ~ sP7(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))
    | spl16_3 ),
    inference(avatar_component_clause,[],[f391])).

fof(f398,plain,
    ( ~ spl16_3
    | spl16_4 ),
    inference(avatar_split_clause,[],[f369,f395,f391])).

fof(f369,plain,
    ( sP6(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))
    | ~ sP7(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) ),
    inference(subsumption_resolution,[],[f368,f61])).

fof(f368,plain,
    ( sP6(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))
    | ~ sP7(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))
    | v2_struct_0(sK9) ),
    inference(subsumption_resolution,[],[f356,f64])).

fof(f356,plain,
    ( sP6(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))
    | ~ sP7(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))
    | ~ l3_lattices(sK9)
    | v2_struct_0(sK9) ),
    inference(superposition,[],[f132,f352])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( sP6(X1,sK15(X0,X1,X2))
      | ~ sP7(X0,X1,X2)
      | ~ l3_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f96,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP6(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP6(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f28,f27])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (25816)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.46  % (25815)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.47  % (25813)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.47  % (25813)Refutation not found, incomplete strategy% (25813)------------------------------
% 0.20/0.47  % (25813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (25813)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (25813)Memory used [KB]: 10618
% 0.20/0.47  % (25813)Time elapsed: 0.036 s
% 0.20/0.47  % (25813)------------------------------
% 0.20/0.47  % (25813)------------------------------
% 0.20/0.48  % (25830)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.48  % (25825)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.49  % (25824)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.49  % (25818)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.50  % (25838)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.50  % (25822)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.50  % (25819)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.50  % (25835)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.50  % (25831)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (25833)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (25823)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.51  % (25826)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % (25827)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.51  % (25838)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f516,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f398,f417,f423,f437,f493,f515])).
% 0.20/0.52  fof(f515,plain,(
% 0.20/0.52    ~spl16_4 | ~spl16_5 | spl16_6 | ~spl16_11),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f514])).
% 0.20/0.52  fof(f514,plain,(
% 0.20/0.52    $false | (~spl16_4 | ~spl16_5 | spl16_6 | ~spl16_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f513,f411])).
% 0.20/0.52  fof(f411,plain,(
% 0.20/0.52    r2_hidden(sK10,a_2_1_lattice3(sK9,sK11)) | ~spl16_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f410])).
% 0.20/0.52  fof(f410,plain,(
% 0.20/0.52    spl16_5 <=> r2_hidden(sK10,a_2_1_lattice3(sK9,sK11))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).
% 0.20/0.52  fof(f513,plain,(
% 0.20/0.52    ~r2_hidden(sK10,a_2_1_lattice3(sK9,sK11)) | (~spl16_4 | spl16_6 | ~spl16_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f509,f415])).
% 0.20/0.52  fof(f415,plain,(
% 0.20/0.52    ~sP1(a_2_1_lattice3(sK9,sK11),sK9,sK10) | spl16_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f414])).
% 0.20/0.52  fof(f414,plain,(
% 0.20/0.52    spl16_6 <=> sP1(a_2_1_lattice3(sK9,sK11),sK9,sK10)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).
% 0.20/0.52  fof(f509,plain,(
% 0.20/0.52    sP1(a_2_1_lattice3(sK9,sK11),sK9,sK10) | ~r2_hidden(sK10,a_2_1_lattice3(sK9,sK11)) | (~spl16_4 | ~spl16_11)),
% 0.20/0.52    inference(resolution,[],[f508,f218])).
% 0.20/0.52  fof(f218,plain,(
% 0.20/0.52    ( ! [X2] : (~r4_lattice3(sK9,sK10,X2) | sP1(X2,sK9,sK10) | ~r2_hidden(sK10,X2)) )),
% 0.20/0.52    inference(resolution,[],[f216,f73])).
% 0.20/0.52  % (25834)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~sP0(X2,X1,X0) | sP1(X0,X1,X2) | ~r4_lattice3(X1,X2,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f41])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ~sP0(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) & ((sP0(X2,X1,X0) & r4_lattice3(X1,X2,X0)) | ~sP1(X0,X1,X2)))),
% 0.20/0.52    inference(rectify,[],[f40])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ~sP0(X2,X0,X1) | ~r4_lattice3(X0,X2,X1)) & ((sP0(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP1(X1,X0,X2)))),
% 0.20/0.52    inference(flattening,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | (~sP0(X2,X0,X1) | ~r4_lattice3(X0,X2,X1))) & ((sP0(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP1(X1,X0,X2)))),
% 0.20/0.52    inference(nnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> (sP0(X2,X0,X1) & r4_lattice3(X0,X2,X1)))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.52  fof(f216,plain,(
% 0.20/0.52    ( ! [X0] : (sP0(sK10,sK9,X0) | ~r2_hidden(sK10,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f215,f61])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ~v2_struct_0(sK9)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ((sK10 != k16_lattice3(sK9,sK11) & r3_lattice3(sK9,sK10,sK11) & r2_hidden(sK10,sK11)) & m1_subset_1(sK10,u1_struct_0(sK9))) & l3_lattices(sK9) & v4_lattice3(sK9) & v10_lattices(sK9) & ~v2_struct_0(sK9)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9,sK10,sK11])],[f9,f35,f34,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k16_lattice3(sK9,X2) != X1 & r3_lattice3(sK9,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK9))) & l3_lattices(sK9) & v4_lattice3(sK9) & v10_lattices(sK9) & ~v2_struct_0(sK9))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ? [X1] : (? [X2] : (k16_lattice3(sK9,X2) != X1 & r3_lattice3(sK9,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(sK9))) => (? [X2] : (k16_lattice3(sK9,X2) != sK10 & r3_lattice3(sK9,sK10,X2) & r2_hidden(sK10,X2)) & m1_subset_1(sK10,u1_struct_0(sK9)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ? [X2] : (k16_lattice3(sK9,X2) != sK10 & r3_lattice3(sK9,sK10,X2) & r2_hidden(sK10,X2)) => (sK10 != k16_lattice3(sK9,sK11) & r3_lattice3(sK9,sK10,sK11) & r2_hidden(sK10,sK11))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f8])).
% 0.20/0.52  fof(f8,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (k16_lattice3(X0,X2) != X1 & (r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.20/0.52    inference(negated_conjecture,[],[f6])).
% 0.20/0.52  fof(f6,conjecture,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).
% 0.20/0.52  fof(f215,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK10,X0) | sP0(sK10,sK9,X0) | v2_struct_0(sK9)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f210,f64])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    l3_lattices(sK9)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f210,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK10,X0) | sP0(sK10,sK9,X0) | ~l3_lattices(sK9) | v2_struct_0(sK9)) )),
% 0.20/0.52    inference(resolution,[],[f209,f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    m1_subset_1(sK10,u1_struct_0(sK9))),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f209,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X2)) | ~r2_hidden(X0,X1) | sP0(X0,X2,X1) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f208])).
% 0.20/0.52  fof(f208,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | sP0(X0,X2,X1) | ~l3_lattices(X2) | v2_struct_0(X2) | sP0(X0,X2,X1)) )),
% 0.20/0.52    inference(resolution,[],[f206,f106])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (sP4(X0,sK12(X1,X0,X2)) | ~l3_lattices(X0) | v2_struct_0(X0) | sP0(X1,X0,X2)) )),
% 0.20/0.52    inference(resolution,[],[f86,f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) | sP0(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f45])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (~r1_lattices(X1,X0,sK12(X0,X1,X2)) & r4_lattice3(X1,sK12(X0,X1,X2),X2) & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f43,f44])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK12(X0,X1,X2)) & r4_lattice3(X1,sK12(X0,X1,X2),X2) & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP0(X0,X1,X2)))),
% 0.20/0.52    inference(rectify,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ! [X2,X0,X1] : ((sP0(X2,X0,X1) | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP0(X2,X0,X1)))),
% 0.20/0.52    inference(nnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X2,X0,X1] : (sP0(X2,X0,X1) <=> ! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP4(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (sP4(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(definition_folding,[],[f15,f25,f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP3(X1,X0,X2)) | ~sP4(X0,X1))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 0.20/0.52  fof(f206,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~sP4(X1,sK12(X0,X1,X2)) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | sP0(X0,X1,X2)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f204])).
% 0.20/0.52  fof(f204,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (sP0(X0,X1,X2) | ~r2_hidden(X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~sP4(X1,sK12(X0,X1,X2)) | sP0(X0,X1,X2)) )),
% 0.20/0.52    inference(resolution,[],[f180,f77])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK12(X0,X1,X2)) | sP0(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f45])).
% 0.20/0.52  fof(f180,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (r1_lattices(X0,X3,sK12(X1,X0,X2)) | sP0(X1,X0,X2) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~sP4(X0,sK12(X1,X0,X2))) )),
% 0.20/0.52    inference(resolution,[],[f104,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X4,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (~r1_lattices(X1,sK13(X0,X1,X2),X0) & r2_hidden(sK13(X0,X1,X2),X2) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f48,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK13(X0,X1,X2),X0) & r2_hidden(sK13(X0,X1,X2),X2) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP3(X0,X1,X2)))),
% 0.20/0.52    inference(rectify,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP3(X1,X0,X2)))),
% 0.20/0.52    inference(nnf_transformation,[],[f24])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (sP3(sK12(X0,X1,X2),X1,X2) | ~sP4(X1,sK12(X0,X1,X2)) | sP0(X0,X1,X2)) )),
% 0.20/0.52    inference(resolution,[],[f80,f76])).
% 0.20/0.52  fof(f76,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK12(X0,X1,X2),X2) | sP0(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f45])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r4_lattice3(X0,X1,X2) | sP3(X1,X0,X2) | ~sP4(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP4(X0,X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f25])).
% 0.20/0.52  fof(f508,plain,(
% 0.20/0.52    r4_lattice3(sK9,sK10,a_2_1_lattice3(sK9,sK11)) | (~spl16_4 | ~spl16_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f507,f109])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    sP4(sK9,sK10)),
% 0.20/0.52    inference(subsumption_resolution,[],[f108,f61])).
% 0.20/0.52  fof(f108,plain,(
% 0.20/0.52    sP4(sK9,sK10) | v2_struct_0(sK9)),
% 0.20/0.52    inference(subsumption_resolution,[],[f105,f64])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    sP4(sK9,sK10) | ~l3_lattices(sK9) | v2_struct_0(sK9)),
% 0.20/0.52    inference(resolution,[],[f86,f65])).
% 0.20/0.52  fof(f507,plain,(
% 0.20/0.52    r4_lattice3(sK9,sK10,a_2_1_lattice3(sK9,sK11)) | ~sP4(sK9,sK10) | (~spl16_4 | ~spl16_11)),
% 0.20/0.52    inference(resolution,[],[f503,f81])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~sP3(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP4(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f46])).
% 0.20/0.52  fof(f503,plain,(
% 0.20/0.52    sP3(sK10,sK9,a_2_1_lattice3(sK9,sK11)) | (~spl16_4 | ~spl16_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f502,f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    r2_hidden(sK10,sK11)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f502,plain,(
% 0.20/0.52    ~r2_hidden(sK10,sK11) | sP3(sK10,sK9,a_2_1_lattice3(sK9,sK11)) | (~spl16_4 | ~spl16_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f499,f65])).
% 0.20/0.52  fof(f499,plain,(
% 0.20/0.52    ~m1_subset_1(sK10,u1_struct_0(sK9)) | ~r2_hidden(sK10,sK11) | sP3(sK10,sK9,a_2_1_lattice3(sK9,sK11)) | (~spl16_4 | ~spl16_11)),
% 0.20/0.52    inference(resolution,[],[f497,f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK13(X0,X1,X2),X0) | sP3(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f50])).
% 0.20/0.52  fof(f497,plain,(
% 0.20/0.52    ( ! [X0] : (r1_lattices(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)),X0) | ~m1_subset_1(X0,u1_struct_0(sK9)) | ~r2_hidden(X0,sK11)) ) | (~spl16_4 | ~spl16_11)),
% 0.20/0.52    inference(resolution,[],[f496,f89])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    ( ! [X4,X2,X0,X1] : (~sP5(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | (~r1_lattices(X1,X0,sK14(X0,X1,X2)) & r2_hidden(sK14(X0,X1,X2),X2) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP5(X0,X1,X2)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f53,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK14(X0,X1,X2)) & r2_hidden(sK14(X0,X1,X2),X2) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP5(X0,X1,X2)))),
% 0.20/0.52    inference(rectify,[],[f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP5(X1,X0,X2)))),
% 0.20/0.52    inference(nnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X1,X0,X2] : (sP5(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.52  fof(f496,plain,(
% 0.20/0.52    sP5(sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)),sK9,sK11) | (~spl16_4 | ~spl16_11)),
% 0.20/0.52    inference(subsumption_resolution,[],[f495,f397])).
% 0.20/0.52  fof(f397,plain,(
% 0.20/0.52    sP6(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) | ~spl16_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f395])).
% 0.20/0.52  fof(f395,plain,(
% 0.20/0.52    spl16_4 <=> sP6(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).
% 0.20/0.52  fof(f495,plain,(
% 0.20/0.52    sP5(sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)),sK9,sK11) | ~sP6(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) | ~spl16_11),
% 0.20/0.52    inference(resolution,[],[f492,f87])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r3_lattice3(X0,X1,X2) | sP5(X1,X0,X2) | ~sP6(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f51])).
% 0.20/0.52  % (25828)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP5(X1,X0,X2)) & (sP5(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP6(X0,X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP5(X1,X0,X2)) | ~sP6(X0,X1))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.52  fof(f492,plain,(
% 0.20/0.52    r3_lattice3(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)),sK11) | ~spl16_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f490])).
% 0.20/0.52  fof(f490,plain,(
% 0.20/0.52    spl16_11 <=> r3_lattice3(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)),sK11)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).
% 0.20/0.52  fof(f493,plain,(
% 0.20/0.52    ~spl16_3 | spl16_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f355,f490,f391])).
% 0.20/0.52  fof(f391,plain,(
% 0.20/0.52    spl16_3 <=> sP7(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).
% 0.20/0.52  fof(f355,plain,(
% 0.20/0.52    r3_lattice3(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)),sK11) | ~sP7(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))),
% 0.20/0.52    inference(superposition,[],[f98,f352])).
% 0.20/0.52  fof(f352,plain,(
% 0.20/0.52    sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)) = sK15(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f351,f68])).
% 0.20/0.52  fof(f68,plain,(
% 0.20/0.52    sK10 != k16_lattice3(sK9,sK11)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f351,plain,(
% 0.20/0.52    sK10 = k16_lattice3(sK9,sK11) | sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)) = sK15(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))),
% 0.20/0.52    inference(forward_demodulation,[],[f350,f145])).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    ( ! [X0] : (k16_lattice3(sK9,X0) = k15_lattice3(sK9,a_2_1_lattice3(sK9,X0))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f144,f61])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    ( ! [X0] : (k16_lattice3(sK9,X0) = k15_lattice3(sK9,a_2_1_lattice3(sK9,X0)) | v2_struct_0(sK9)) )),
% 0.20/0.52    inference(resolution,[],[f79,f64])).
% 0.20/0.52  % (25821)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l3_lattices(X0) | k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k16_lattice3(X0,X1) = k15_lattice3(X0,a_2_1_lattice3(X0,X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d22_lattice3)).
% 0.20/0.52  fof(f350,plain,(
% 0.20/0.52    sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)) = sK15(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) | sK10 = k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11))),
% 0.20/0.52    inference(subsumption_resolution,[],[f349,f64])).
% 0.20/0.52  fof(f349,plain,(
% 0.20/0.52    sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)) = sK15(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) | sK10 = k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)) | ~l3_lattices(sK9)),
% 0.20/0.52    inference(subsumption_resolution,[],[f348,f61])).
% 0.20/0.52  fof(f348,plain,(
% 0.20/0.52    v2_struct_0(sK9) | sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)) = sK15(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) | sK10 = k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)) | ~l3_lattices(sK9)),
% 0.20/0.52    inference(resolution,[],[f347,f137])).
% 0.20/0.52  fof(f137,plain,(
% 0.20/0.52    sP7(sK11,sK9,sK10)),
% 0.20/0.52    inference(subsumption_resolution,[],[f135,f65])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    sP7(sK11,sK9,sK10) | ~m1_subset_1(sK10,u1_struct_0(sK9))),
% 0.20/0.52    inference(resolution,[],[f102,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    r3_lattice3(sK9,sK10,sK11)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f102,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r3_lattice3(X1,X3,X0) | sP7(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.20/0.52    inference(equality_resolution,[],[f99])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (sP7(X0,X1,X2) | ~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f60])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r3_lattice3(X1,sK15(X0,X1,X2),X0) & sK15(X0,X1,X2) = X2 & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f58,f59])).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r3_lattice3(X1,sK15(X0,X1,X2),X0) & sK15(X0,X1,X2) = X2 & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f58,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ! [X3] : (~r3_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r3_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 0.20/0.52    inference(rectify,[],[f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    ! [X2,X1,X0] : ((sP7(X2,X1,X0) | ! [X3] : (~r3_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP7(X2,X1,X0)))),
% 0.20/0.52    inference(nnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    ! [X2,X1,X0] : (sP7(X2,X1,X0) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 0.20/0.52  fof(f347,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~sP7(X1,X0,sK10) | v2_struct_0(X0) | sK13(sK10,sK9,a_2_1_lattice3(X0,X1)) = sK15(X1,X0,sK13(sK10,sK9,a_2_1_lattice3(X0,X1))) | sK10 = k15_lattice3(sK9,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f346,f100])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (sP8(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (sP8(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 0.20/0.52    inference(definition_folding,[],[f19,f31,f30])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> sP7(X2,X1,X0)) | ~sP8(X0,X1,X2))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | v2_struct_0(X1))),
% 0.20/0.52    inference(flattening,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | v2_struct_0(X1)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((l3_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_lattice3(X1,X2)) <=> ? [X3] : (r3_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_lattice3)).
% 0.20/0.52  fof(f346,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~l3_lattices(X0) | v2_struct_0(X0) | sK13(sK10,sK9,a_2_1_lattice3(X0,X1)) = sK15(X1,X0,sK13(sK10,sK9,a_2_1_lattice3(X0,X1))) | sK10 = k15_lattice3(sK9,a_2_1_lattice3(X0,X1)) | ~sP7(X1,X0,sK10) | ~sP8(sK10,X0,X1)) )),
% 0.20/0.52    inference(resolution,[],[f281,f95])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP7(X2,X1,X0) | ~sP8(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f56,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_lattice3(X1,X2)) | ~sP7(X2,X1,X0)) & (sP7(X2,X1,X0) | ~r2_hidden(X0,a_2_1_lattice3(X1,X2)))) | ~sP8(X0,X1,X2))),
% 0.20/0.52    inference(nnf_transformation,[],[f31])).
% 0.20/0.52  fof(f281,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~r2_hidden(sK10,a_2_1_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0) | sK13(sK10,sK9,a_2_1_lattice3(X0,X1)) = sK15(X1,X0,sK13(sK10,sK9,a_2_1_lattice3(X0,X1))) | sK10 = k15_lattice3(sK9,a_2_1_lattice3(X0,X1))) )),
% 0.20/0.52    inference(resolution,[],[f280,f176])).
% 0.20/0.52  fof(f176,plain,(
% 0.20/0.52    ( ! [X0] : (~sP1(X0,sK9,sK10) | sK10 = k15_lattice3(sK9,X0)) )),
% 0.20/0.52    inference(resolution,[],[f175,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~sP2(X0,X1,X2) | ~sP1(X2,X1,X0) | k15_lattice3(X1,X2) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((k15_lattice3(X1,X2) = X0 | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | k15_lattice3(X1,X2) != X0)) | ~sP2(X0,X1,X2))),
% 0.20/0.52    inference(rectify,[],[f37])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ! [X2,X0,X1] : (((k15_lattice3(X0,X1) = X2 | ~sP1(X1,X0,X2)) & (sP1(X1,X0,X2) | k15_lattice3(X0,X1) != X2)) | ~sP2(X2,X0,X1))),
% 0.20/0.52    inference(nnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X2,X0,X1] : ((k15_lattice3(X0,X1) = X2 <=> sP1(X1,X0,X2)) | ~sP2(X2,X0,X1))),
% 0.20/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.52  fof(f175,plain,(
% 0.20/0.52    ( ! [X0] : (sP2(sK10,sK9,X0)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f174,f61])).
% 0.20/0.52  fof(f174,plain,(
% 0.20/0.52    ( ! [X0] : (sP2(sK10,sK9,X0) | v2_struct_0(sK9)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f173,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    v10_lattices(sK9)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f173,plain,(
% 0.20/0.52    ( ! [X0] : (sP2(sK10,sK9,X0) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f172,f63])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    v4_lattice3(sK9)),
% 0.20/0.52    inference(cnf_transformation,[],[f36])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    ( ! [X0] : (sP2(sK10,sK9,X0) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f167,f64])).
% 0.20/0.52  fof(f167,plain,(
% 0.20/0.52    ( ! [X0] : (sP2(sK10,sK9,X0) | ~l3_lattices(sK9) | ~v4_lattice3(sK9) | ~v10_lattices(sK9) | v2_struct_0(sK9)) )),
% 0.20/0.52    inference(resolution,[],[f103,f65])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | sP2(X2,X0,X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f78])).
% 0.20/0.52  fof(f78,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (sP2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : (sP2(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(definition_folding,[],[f11,f22,f21,f20])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 0.20/0.52  fof(f280,plain,(
% 0.20/0.52    ( ! [X24,X25] : (sP1(a_2_1_lattice3(X24,X25),sK9,sK10) | sK13(sK10,sK9,a_2_1_lattice3(X24,X25)) = sK15(X25,X24,sK13(sK10,sK9,a_2_1_lattice3(X24,X25))) | ~l3_lattices(X24) | v2_struct_0(X24) | ~r2_hidden(sK10,a_2_1_lattice3(X24,X25))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f273,f109])).
% 0.20/0.52  fof(f273,plain,(
% 0.20/0.52    ( ! [X24,X25] : (v2_struct_0(X24) | sK13(sK10,sK9,a_2_1_lattice3(X24,X25)) = sK15(X25,X24,sK13(sK10,sK9,a_2_1_lattice3(X24,X25))) | ~l3_lattices(X24) | ~sP4(sK9,sK10) | sP1(a_2_1_lattice3(X24,X25),sK9,sK10) | ~r2_hidden(sK10,a_2_1_lattice3(X24,X25))) )),
% 0.20/0.52    inference(resolution,[],[f238,f218])).
% 0.20/0.52  fof(f238,plain,(
% 0.20/0.52    ( ! [X6,X8,X7,X5] : (r4_lattice3(X7,X6,a_2_1_lattice3(X5,X8)) | v2_struct_0(X5) | sK13(X6,X7,a_2_1_lattice3(X5,X8)) = sK15(X8,X5,sK13(X6,X7,a_2_1_lattice3(X5,X8))) | ~l3_lattices(X5) | ~sP4(X7,X6)) )),
% 0.20/0.52    inference(resolution,[],[f199,f81])).
% 0.20/0.52  fof(f199,plain,(
% 0.20/0.52    ( ! [X10,X8,X11,X9] : (sP3(X8,X9,a_2_1_lattice3(X10,X11)) | ~l3_lattices(X10) | v2_struct_0(X10) | sK13(X8,X9,a_2_1_lattice3(X10,X11)) = sK15(X11,X10,sK13(X8,X9,a_2_1_lattice3(X10,X11)))) )),
% 0.20/0.52    inference(resolution,[],[f196,f97])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~sP7(X0,X1,X2) | sK15(X0,X1,X2) = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f60])).
% 0.20/0.52  fof(f196,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (sP7(X0,X1,sK13(X2,X3,a_2_1_lattice3(X1,X0))) | sP3(X2,X3,a_2_1_lattice3(X1,X0)) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 0.20/0.52    inference(resolution,[],[f147,f100])).
% 0.20/0.52  fof(f147,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (~sP8(sK13(X2,X3,a_2_1_lattice3(X1,X0)),X1,X0) | sP7(X0,X1,sK13(X2,X3,a_2_1_lattice3(X1,X0))) | sP3(X2,X3,a_2_1_lattice3(X1,X0))) )),
% 0.20/0.52    inference(resolution,[],[f94,f84])).
% 0.20/0.52  fof(f84,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK13(X0,X1,X2),X2) | sP3(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f50])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_lattice3(X1,X2)) | sP7(X2,X1,X0) | ~sP8(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f56])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK15(X0,X1,X2),X0) | ~sP7(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f60])).
% 0.20/0.52  fof(f437,plain,(
% 0.20/0.52    ~spl16_6),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f436])).
% 0.20/0.52  fof(f436,plain,(
% 0.20/0.52    $false | ~spl16_6),
% 0.20/0.52    inference(subsumption_resolution,[],[f432,f68])).
% 0.20/0.52  fof(f432,plain,(
% 0.20/0.52    sK10 = k16_lattice3(sK9,sK11) | ~spl16_6),
% 0.20/0.52    inference(superposition,[],[f145,f426])).
% 0.20/0.52  fof(f426,plain,(
% 0.20/0.52    sK10 = k15_lattice3(sK9,a_2_1_lattice3(sK9,sK11)) | ~spl16_6),
% 0.20/0.52    inference(resolution,[],[f416,f176])).
% 0.20/0.52  fof(f416,plain,(
% 0.20/0.52    sP1(a_2_1_lattice3(sK9,sK11),sK9,sK10) | ~spl16_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f414])).
% 0.20/0.52  fof(f423,plain,(
% 0.20/0.52    spl16_5),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f422])).
% 0.20/0.52  fof(f422,plain,(
% 0.20/0.52    $false | spl16_5),
% 0.20/0.52    inference(subsumption_resolution,[],[f421,f61])).
% 0.20/0.52  fof(f421,plain,(
% 0.20/0.52    v2_struct_0(sK9) | spl16_5),
% 0.20/0.52    inference(subsumption_resolution,[],[f420,f64])).
% 0.20/0.52  fof(f420,plain,(
% 0.20/0.52    ~l3_lattices(sK9) | v2_struct_0(sK9) | spl16_5),
% 0.20/0.52    inference(resolution,[],[f419,f100])).
% 0.20/0.52  fof(f419,plain,(
% 0.20/0.52    ~sP8(sK10,sK9,sK11) | spl16_5),
% 0.20/0.52    inference(subsumption_resolution,[],[f418,f137])).
% 0.20/0.52  fof(f418,plain,(
% 0.20/0.52    ~sP7(sK11,sK9,sK10) | ~sP8(sK10,sK9,sK11) | spl16_5),
% 0.20/0.52    inference(resolution,[],[f412,f95])).
% 0.20/0.52  fof(f412,plain,(
% 0.20/0.52    ~r2_hidden(sK10,a_2_1_lattice3(sK9,sK11)) | spl16_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f410])).
% 0.20/0.52  fof(f417,plain,(
% 0.20/0.52    ~spl16_5 | spl16_6 | spl16_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f405,f391,f414,f410])).
% 0.20/0.52  fof(f405,plain,(
% 0.20/0.52    sP1(a_2_1_lattice3(sK9,sK11),sK9,sK10) | ~r2_hidden(sK10,a_2_1_lattice3(sK9,sK11)) | spl16_3),
% 0.20/0.52    inference(resolution,[],[f404,f218])).
% 0.20/0.52  fof(f404,plain,(
% 0.20/0.52    r4_lattice3(sK9,sK10,a_2_1_lattice3(sK9,sK11)) | spl16_3),
% 0.20/0.52    inference(subsumption_resolution,[],[f403,f109])).
% 0.20/0.52  fof(f403,plain,(
% 0.20/0.52    r4_lattice3(sK9,sK10,a_2_1_lattice3(sK9,sK11)) | ~sP4(sK9,sK10) | spl16_3),
% 0.20/0.52    inference(resolution,[],[f401,f81])).
% 0.20/0.52  fof(f401,plain,(
% 0.20/0.52    sP3(sK10,sK9,a_2_1_lattice3(sK9,sK11)) | spl16_3),
% 0.20/0.52    inference(subsumption_resolution,[],[f400,f61])).
% 0.20/0.52  fof(f400,plain,(
% 0.20/0.52    sP3(sK10,sK9,a_2_1_lattice3(sK9,sK11)) | v2_struct_0(sK9) | spl16_3),
% 0.20/0.52    inference(subsumption_resolution,[],[f399,f64])).
% 0.20/0.52  fof(f399,plain,(
% 0.20/0.52    sP3(sK10,sK9,a_2_1_lattice3(sK9,sK11)) | ~l3_lattices(sK9) | v2_struct_0(sK9) | spl16_3),
% 0.20/0.52    inference(resolution,[],[f393,f196])).
% 0.20/0.52  fof(f393,plain,(
% 0.20/0.52    ~sP7(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) | spl16_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f391])).
% 0.20/0.52  fof(f398,plain,(
% 0.20/0.52    ~spl16_3 | spl16_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f369,f395,f391])).
% 0.20/0.52  fof(f369,plain,(
% 0.20/0.52    sP6(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) | ~sP7(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11)))),
% 0.20/0.52    inference(subsumption_resolution,[],[f368,f61])).
% 0.20/0.52  fof(f368,plain,(
% 0.20/0.52    sP6(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) | ~sP7(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) | v2_struct_0(sK9)),
% 0.20/0.52    inference(subsumption_resolution,[],[f356,f64])).
% 0.20/0.52  fof(f356,plain,(
% 0.20/0.52    sP6(sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) | ~sP7(sK11,sK9,sK13(sK10,sK9,a_2_1_lattice3(sK9,sK11))) | ~l3_lattices(sK9) | v2_struct_0(sK9)),
% 0.20/0.52    inference(superposition,[],[f132,f352])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (sP6(X1,sK15(X0,X1,X2)) | ~sP7(X0,X1,X2) | ~l3_lattices(X1) | v2_struct_0(X1)) )),
% 0.20/0.52    inference(resolution,[],[f96,f93])).
% 0.20/0.52  fof(f93,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP6(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (sP6(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(definition_folding,[],[f17,f28,f27])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 0.20/0.52  fof(f96,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) | ~sP7(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f60])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (25838)------------------------------
% 0.20/0.52  % (25838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (25838)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (25838)Memory used [KB]: 11129
% 0.20/0.52  % (25838)Time elapsed: 0.120 s
% 0.20/0.52  % (25838)------------------------------
% 0.20/0.52  % (25838)------------------------------
% 0.20/0.52  % (25812)Success in time 0.165 s
%------------------------------------------------------------------------------
