%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1509+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:59 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 586 expanded)
%              Number of leaves         :   32 ( 185 expanded)
%              Depth                    :   23
%              Number of atoms          :  914 (3424 expanded)
%              Number of equality atoms :   82 ( 815 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f497,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f165,f404,f417,f422,f427,f451,f490,f496])).

fof(f496,plain,(
    ~ spl11_3 ),
    inference(avatar_contradiction_clause,[],[f495])).

fof(f495,plain,
    ( $false
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f494,f70])).

fof(f70,plain,(
    l3_lattices(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
    ( ( sK7 != k16_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK7))
      | sK7 != k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK7)) )
    & m1_subset_1(sK7,u1_struct_0(sK6))
    & l3_lattices(sK6)
    & v4_lattice3(sK6)
    & v10_lattices(sK6)
    & ~ v2_struct_0(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f16,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
              | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( k16_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),X1)) != X1
            | k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(sK6)) )
      & l3_lattices(sK6)
      & v4_lattice3(sK6)
      & v10_lattices(sK6)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ( k16_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),X1)) != X1
          | k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),X1)) != X1 )
        & m1_subset_1(X1,u1_struct_0(sK6)) )
   => ( ( sK7 != k16_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK7))
        | sK7 != k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK7)) )
      & m1_subset_1(sK7,u1_struct_0(sK6)) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
            | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
            | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
              & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).

fof(f494,plain,
    ( ~ l3_lattices(sK6)
    | ~ spl11_3 ),
    inference(resolution,[],[f493,f75])).

fof(f75,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f493,plain,
    ( ~ l2_lattices(sK6)
    | ~ spl11_3 ),
    inference(resolution,[],[f492,f73])).

fof(f73,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l2_lattices)).

fof(f492,plain,
    ( ~ l1_struct_0(sK6)
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f491,f67])).

fof(f67,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f491,plain,
    ( ~ l1_struct_0(sK6)
    | v2_struct_0(sK6)
    | ~ spl11_3 ),
    inference(resolution,[],[f160,f84])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f160,plain,
    ( v1_xboole_0(u1_struct_0(sK6))
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl11_3
  <=> v1_xboole_0(u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f490,plain,
    ( ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_9 ),
    inference(avatar_contradiction_clause,[],[f489])).

fof(f489,plain,
    ( $false
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_9 ),
    inference(subsumption_resolution,[],[f488,f67])).

fof(f488,plain,
    ( v2_struct_0(sK6)
    | ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_9 ),
    inference(subsumption_resolution,[],[f487,f388])).

fof(f388,plain,
    ( v6_lattices(sK6)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f387])).

fof(f387,plain,
    ( spl11_5
  <=> v6_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f487,plain,
    ( ~ v6_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ spl11_6
    | ~ spl11_7
    | spl11_9 ),
    inference(subsumption_resolution,[],[f486,f392])).

fof(f392,plain,
    ( v8_lattices(sK6)
    | ~ spl11_6 ),
    inference(avatar_component_clause,[],[f391])).

fof(f391,plain,
    ( spl11_6
  <=> v8_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_6])])).

fof(f486,plain,
    ( ~ v8_lattices(sK6)
    | ~ v6_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ spl11_7
    | spl11_9 ),
    inference(subsumption_resolution,[],[f485,f396])).

fof(f396,plain,
    ( v9_lattices(sK6)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f395])).

fof(f395,plain,
    ( spl11_7
  <=> v9_lattices(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f485,plain,
    ( ~ v9_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ v6_lattices(sK6)
    | v2_struct_0(sK6)
    | spl11_9 ),
    inference(subsumption_resolution,[],[f484,f70])).

fof(f484,plain,
    ( ~ l3_lattices(sK6)
    | ~ v9_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ v6_lattices(sK6)
    | v2_struct_0(sK6)
    | spl11_9 ),
    inference(subsumption_resolution,[],[f483,f146])).

fof(f146,plain,(
    sP2(sK6,sK7) ),
    inference(subsumption_resolution,[],[f145,f67])).

fof(f145,plain,
    ( sP2(sK6,sK7)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f143,f70])).

fof(f143,plain,
    ( sP2(sK6,sK7)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f93,f71])).

fof(f71,plain,(
    m1_subset_1(sK7,u1_struct_0(sK6)) ),
    inference(cnf_transformation,[],[f49])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP2(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP2(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f28,f40,f39])).

fof(f39,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP1(X1,X0,X2) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f483,plain,
    ( ~ sP2(sK6,sK7)
    | ~ l3_lattices(sK6)
    | ~ v9_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ v6_lattices(sK6)
    | v2_struct_0(sK6)
    | spl11_9 ),
    inference(subsumption_resolution,[],[f482,f124])).

fof(f124,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f111,f112])).

fof(f112,plain,(
    ! [X0] : sP5(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( sP5(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP5(X0,X1) )
      & ( sP5(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP5(X0,X1) ) ),
    inference(definition_folding,[],[f4,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( sP5(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f111,plain,(
    ! [X3,X1] :
      ( ~ sP5(X3,X1)
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | ~ sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ( ( sK10(X0,X1) != X0
            | ~ r2_hidden(sK10(X0,X1),X1) )
          & ( sK10(X0,X1) = X0
            | r2_hidden(sK10(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP5(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f62,f63])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK10(X0,X1) != X0
          | ~ r2_hidden(sK10(X0,X1),X1) )
        & ( sK10(X0,X1) = X0
          | r2_hidden(sK10(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP5(X0,X1) ) ) ),
    inference(rectify,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( sP5(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP5(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f482,plain,
    ( ~ r2_hidden(sK7,k1_tarski(sK7))
    | ~ sP2(sK6,sK7)
    | ~ l3_lattices(sK6)
    | ~ v9_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ v6_lattices(sK6)
    | v2_struct_0(sK6)
    | spl11_9 ),
    inference(subsumption_resolution,[],[f479,f71])).

fof(f479,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(sK7,k1_tarski(sK7))
    | ~ sP2(sK6,sK7)
    | ~ l3_lattices(sK6)
    | ~ v9_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ v6_lattices(sK6)
    | v2_struct_0(sK6)
    | spl11_9 ),
    inference(duplicate_literal_removal,[],[f478])).

fof(f478,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(sK7,k1_tarski(sK7))
    | ~ sP2(sK6,sK7)
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | ~ v9_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ v6_lattices(sK6)
    | v2_struct_0(sK6)
    | spl11_9 ),
    inference(resolution,[],[f471,f298])).

fof(f298,plain,(
    ! [X0,X1] :
      ( r1_lattices(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f297])).

fof(f297,plain,(
    ! [X0,X1] :
      ( r1_lattices(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f109,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( r3_lattices(X1,X0,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(condensation,[],[f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( r3_lattices(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f109,plain,(
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
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f471,plain,
    ( ! [X0] :
        ( ~ r1_lattices(sK6,X0,sK7)
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ r2_hidden(X0,k1_tarski(sK7))
        | ~ sP2(sK6,X0) )
    | spl11_9 ),
    inference(resolution,[],[f462,f177])).

fof(f177,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X0,X1,k1_tarski(X2))
      | ~ r1_lattices(X0,X1,X2)
      | ~ sP2(X0,X1) ) ),
    inference(resolution,[],[f173,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X1,X0,X2)
      | r3_lattice3(X0,X1,X2)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP1(X1,X0,X2) )
          & ( sP1(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,k1_tarski(X2))
      | ~ r1_lattices(X1,X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f168])).

fof(f168,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,X2)
      | sP1(X0,X1,k1_tarski(X2))
      | sP1(X0,X1,k1_tarski(X2)) ) ),
    inference(superposition,[],[f92,f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( sK8(X0,X1,k1_tarski(X2)) = X2
      | sP1(X0,X1,k1_tarski(X2)) ) ),
    inference(resolution,[],[f91,f135])).

fof(f135,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f102,f112])).

fof(f102,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f64])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X2)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK8(X0,X1,X2))
          & r2_hidden(sK8(X0,X1,X2),X2)
          & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f53,f54])).

fof(f54,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK8(X0,X1,X2))
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f462,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK6,X0,k1_tarski(sK7))
        | ~ r2_hidden(X0,k1_tarski(sK7))
        | ~ m1_subset_1(X0,u1_struct_0(sK6)) )
    | spl11_9 ),
    inference(subsumption_resolution,[],[f461,f135])).

fof(f461,plain,
    ( ! [X0] :
        ( sK7 != X0
        | ~ r3_lattice3(sK6,X0,k1_tarski(sK7))
        | ~ r2_hidden(X0,k1_tarski(sK7))
        | ~ m1_subset_1(X0,u1_struct_0(sK6)) )
    | spl11_9 ),
    inference(subsumption_resolution,[],[f460,f67])).

fof(f460,plain,
    ( ! [X0] :
        ( sK7 != X0
        | ~ r3_lattice3(sK6,X0,k1_tarski(sK7))
        | ~ r2_hidden(X0,k1_tarski(sK7))
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | v2_struct_0(sK6) )
    | spl11_9 ),
    inference(subsumption_resolution,[],[f459,f68])).

fof(f68,plain,(
    v10_lattices(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f459,plain,
    ( ! [X0] :
        ( sK7 != X0
        | ~ r3_lattice3(sK6,X0,k1_tarski(sK7))
        | ~ r2_hidden(X0,k1_tarski(sK7))
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ v10_lattices(sK6)
        | v2_struct_0(sK6) )
    | spl11_9 ),
    inference(subsumption_resolution,[],[f458,f69])).

fof(f69,plain,(
    v4_lattice3(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f458,plain,
    ( ! [X0] :
        ( sK7 != X0
        | ~ r3_lattice3(sK6,X0,k1_tarski(sK7))
        | ~ r2_hidden(X0,k1_tarski(sK7))
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ v4_lattice3(sK6)
        | ~ v10_lattices(sK6)
        | v2_struct_0(sK6) )
    | spl11_9 ),
    inference(subsumption_resolution,[],[f457,f70])).

fof(f457,plain,
    ( ! [X0] :
        ( sK7 != X0
        | ~ r3_lattice3(sK6,X0,k1_tarski(sK7))
        | ~ r2_hidden(X0,k1_tarski(sK7))
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ l3_lattices(sK6)
        | ~ v4_lattice3(sK6)
        | ~ v10_lattices(sK6)
        | v2_struct_0(sK6) )
    | spl11_9 ),
    inference(superposition,[],[f450,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X0,X2) = X1
      | ~ r3_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f450,plain,
    ( sK7 != k16_lattice3(sK6,k1_tarski(sK7))
    | spl11_9 ),
    inference(avatar_component_clause,[],[f448])).

fof(f448,plain,
    ( spl11_9
  <=> sK7 = k16_lattice3(sK6,k1_tarski(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f451,plain,
    ( spl11_3
    | ~ spl11_9
    | spl11_2 ),
    inference(avatar_split_clause,[],[f446,f119,f448,f158])).

fof(f119,plain,
    ( spl11_2
  <=> sK7 = k16_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f446,plain,
    ( sK7 != k16_lattice3(sK6,k1_tarski(sK7))
    | v1_xboole_0(u1_struct_0(sK6))
    | spl11_2 ),
    inference(subsumption_resolution,[],[f444,f71])).

fof(f444,plain,
    ( sK7 != k16_lattice3(sK6,k1_tarski(sK7))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6))
    | spl11_2 ),
    inference(superposition,[],[f121,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f121,plain,
    ( sK7 != k16_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK7))
    | spl11_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f427,plain,(
    spl11_7 ),
    inference(avatar_contradiction_clause,[],[f426])).

fof(f426,plain,
    ( $false
    | spl11_7 ),
    inference(subsumption_resolution,[],[f425,f68])).

fof(f425,plain,
    ( ~ v10_lattices(sK6)
    | spl11_7 ),
    inference(subsumption_resolution,[],[f424,f70])).

fof(f424,plain,
    ( ~ l3_lattices(sK6)
    | ~ v10_lattices(sK6)
    | spl11_7 ),
    inference(subsumption_resolution,[],[f423,f67])).

fof(f423,plain,
    ( v2_struct_0(sK6)
    | ~ l3_lattices(sK6)
    | ~ v10_lattices(sK6)
    | spl11_7 ),
    inference(resolution,[],[f397,f134])).

fof(f134,plain,(
    ! [X6] :
      ( v9_lattices(X6)
      | v2_struct_0(X6)
      | ~ l3_lattices(X6)
      | ~ v10_lattices(X6) ) ),
    inference(resolution,[],[f83,f82])).

fof(f82,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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

fof(f83,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f20,f37])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f397,plain,
    ( ~ v9_lattices(sK6)
    | spl11_7 ),
    inference(avatar_component_clause,[],[f395])).

fof(f422,plain,(
    spl11_6 ),
    inference(avatar_contradiction_clause,[],[f421])).

fof(f421,plain,
    ( $false
    | spl11_6 ),
    inference(subsumption_resolution,[],[f420,f68])).

fof(f420,plain,
    ( ~ v10_lattices(sK6)
    | spl11_6 ),
    inference(subsumption_resolution,[],[f419,f70])).

fof(f419,plain,
    ( ~ l3_lattices(sK6)
    | ~ v10_lattices(sK6)
    | spl11_6 ),
    inference(subsumption_resolution,[],[f418,f67])).

fof(f418,plain,
    ( v2_struct_0(sK6)
    | ~ l3_lattices(sK6)
    | ~ v10_lattices(sK6)
    | spl11_6 ),
    inference(resolution,[],[f393,f133])).

fof(f133,plain,(
    ! [X5] :
      ( v8_lattices(X5)
      | v2_struct_0(X5)
      | ~ l3_lattices(X5)
      | ~ v10_lattices(X5) ) ),
    inference(resolution,[],[f83,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f393,plain,
    ( ~ v8_lattices(sK6)
    | spl11_6 ),
    inference(avatar_component_clause,[],[f391])).

fof(f417,plain,(
    spl11_5 ),
    inference(avatar_contradiction_clause,[],[f416])).

fof(f416,plain,
    ( $false
    | spl11_5 ),
    inference(subsumption_resolution,[],[f415,f68])).

fof(f415,plain,
    ( ~ v10_lattices(sK6)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f414,f70])).

fof(f414,plain,
    ( ~ l3_lattices(sK6)
    | ~ v10_lattices(sK6)
    | spl11_5 ),
    inference(subsumption_resolution,[],[f413,f67])).

fof(f413,plain,
    ( v2_struct_0(sK6)
    | ~ l3_lattices(sK6)
    | ~ v10_lattices(sK6)
    | spl11_5 ),
    inference(resolution,[],[f389,f131])).

fof(f131,plain,(
    ! [X3] :
      ( v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3) ) ),
    inference(resolution,[],[f83,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f389,plain,
    ( ~ v6_lattices(sK6)
    | spl11_5 ),
    inference(avatar_component_clause,[],[f387])).

fof(f404,plain,
    ( ~ spl11_5
    | ~ spl11_6
    | ~ spl11_7
    | spl11_4 ),
    inference(avatar_split_clause,[],[f403,f162,f395,f391,f387])).

fof(f162,plain,
    ( spl11_4
  <=> sK7 = k15_lattice3(sK6,k1_tarski(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f403,plain,
    ( ~ v9_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ v6_lattices(sK6)
    | spl11_4 ),
    inference(subsumption_resolution,[],[f402,f154])).

fof(f154,plain,(
    sP4(sK6,sK7) ),
    inference(subsumption_resolution,[],[f153,f67])).

fof(f153,plain,
    ( sP4(sK6,sK7)
    | v2_struct_0(sK6) ),
    inference(subsumption_resolution,[],[f150,f70])).

fof(f150,plain,
    ( sP4(sK6,sK7)
    | ~ l3_lattices(sK6)
    | v2_struct_0(sK6) ),
    inference(resolution,[],[f100,f71])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP4(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP4(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f30,f43,f42])).

fof(f42,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP3(X1,X0,X2) )
      | ~ sP4(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

% (2152)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (2163)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (2143)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% (2149)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% (2140)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
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

fof(f402,plain,
    ( ~ v9_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ v6_lattices(sK6)
    | ~ sP4(sK6,sK7)
    | spl11_4 ),
    inference(subsumption_resolution,[],[f401,f124])).

fof(f401,plain,
    ( ~ v9_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ v6_lattices(sK6)
    | ~ r2_hidden(sK7,k1_tarski(sK7))
    | ~ sP4(sK6,sK7)
    | spl11_4 ),
    inference(subsumption_resolution,[],[f400,f67])).

fof(f400,plain,
    ( ~ v9_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ v6_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ r2_hidden(sK7,k1_tarski(sK7))
    | ~ sP4(sK6,sK7)
    | spl11_4 ),
    inference(subsumption_resolution,[],[f399,f70])).

fof(f399,plain,
    ( ~ l3_lattices(sK6)
    | ~ v9_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ v6_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ r2_hidden(sK7,k1_tarski(sK7))
    | ~ sP4(sK6,sK7)
    | spl11_4 ),
    inference(subsumption_resolution,[],[f381,f71])).

fof(f381,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | ~ v9_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ v6_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ r2_hidden(sK7,k1_tarski(sK7))
    | ~ sP4(sK6,sK7)
    | spl11_4 ),
    inference(duplicate_literal_removal,[],[f378])).

fof(f378,plain,
    ( ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ l3_lattices(sK6)
    | ~ v9_lattices(sK6)
    | ~ v8_lattices(sK6)
    | ~ v6_lattices(sK6)
    | v2_struct_0(sK6)
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | ~ r2_hidden(sK7,k1_tarski(sK7))
    | ~ sP4(sK6,sK7)
    | spl11_4 ),
    inference(resolution,[],[f298,f288])).

fof(f288,plain,
    ( ! [X0] :
        ( ~ r1_lattices(sK6,sK7,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK6))
        | ~ r2_hidden(X0,k1_tarski(sK7))
        | ~ sP4(sK6,X0) )
    | spl11_4 ),
    inference(resolution,[],[f282,f195])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X2,k1_tarski(X1))
      | ~ r1_lattices(X0,X1,X2)
      | ~ sP4(X0,X2) ) ),
    inference(resolution,[],[f187,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ sP3(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP3(X1,X0,X2) )
          & ( sP3(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP4(X0,X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X1,k1_tarski(X2))
      | ~ r1_lattices(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f182])).

fof(f182,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X2,X0)
      | sP3(X0,X1,k1_tarski(X2))
      | sP3(X0,X1,k1_tarski(X2)) ) ),
    inference(superposition,[],[f99,f140])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( sK9(X0,X1,k1_tarski(X2)) = X2
      | sP3(X0,X1,k1_tarski(X2)) ) ),
    inference(resolution,[],[f98,f135])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X2)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK9(X0,X1,X2),X0)
          & r2_hidden(sK9(X0,X1,X2),X2)
          & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f58,f59])).

fof(f59,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK9(X0,X1,X2),X0)
        & r2_hidden(sK9(X0,X1,X2),X2)
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f57,plain,(
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
    inference(nnf_transformation,[],[f42])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK9(X0,X1,X2),X0)
      | sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f282,plain,
    ( ! [X1] :
        ( ~ r4_lattice3(sK6,X1,k1_tarski(sK7))
        | ~ r2_hidden(X1,k1_tarski(sK7))
        | ~ m1_subset_1(X1,u1_struct_0(sK6)) )
    | spl11_4 ),
    inference(subsumption_resolution,[],[f281,f135])).

fof(f281,plain,
    ( ! [X1] :
        ( sK7 != X1
        | ~ r4_lattice3(sK6,X1,k1_tarski(sK7))
        | ~ r2_hidden(X1,k1_tarski(sK7))
        | ~ m1_subset_1(X1,u1_struct_0(sK6)) )
    | spl11_4 ),
    inference(subsumption_resolution,[],[f280,f67])).

fof(f280,plain,
    ( ! [X1] :
        ( sK7 != X1
        | ~ r4_lattice3(sK6,X1,k1_tarski(sK7))
        | ~ r2_hidden(X1,k1_tarski(sK7))
        | ~ m1_subset_1(X1,u1_struct_0(sK6))
        | v2_struct_0(sK6) )
    | spl11_4 ),
    inference(subsumption_resolution,[],[f279,f68])).

fof(f279,plain,
    ( ! [X1] :
        ( sK7 != X1
        | ~ r4_lattice3(sK6,X1,k1_tarski(sK7))
        | ~ r2_hidden(X1,k1_tarski(sK7))
        | ~ m1_subset_1(X1,u1_struct_0(sK6))
        | ~ v10_lattices(sK6)
        | v2_struct_0(sK6) )
    | spl11_4 ),
    inference(subsumption_resolution,[],[f278,f69])).

fof(f278,plain,
    ( ! [X1] :
        ( sK7 != X1
        | ~ r4_lattice3(sK6,X1,k1_tarski(sK7))
        | ~ r2_hidden(X1,k1_tarski(sK7))
        | ~ m1_subset_1(X1,u1_struct_0(sK6))
        | ~ v4_lattice3(sK6)
        | ~ v10_lattices(sK6)
        | v2_struct_0(sK6) )
    | spl11_4 ),
    inference(subsumption_resolution,[],[f271,f70])).

fof(f271,plain,
    ( ! [X1] :
        ( sK7 != X1
        | ~ r4_lattice3(sK6,X1,k1_tarski(sK7))
        | ~ r2_hidden(X1,k1_tarski(sK7))
        | ~ m1_subset_1(X1,u1_struct_0(sK6))
        | ~ l3_lattices(sK6)
        | ~ v4_lattice3(sK6)
        | ~ v10_lattices(sK6)
        | v2_struct_0(sK6) )
    | spl11_4 ),
    inference(superposition,[],[f164,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k15_lattice3(X0,X2) = X1
      | ~ r4_lattice3(X0,X1,X2)
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f164,plain,
    ( sK7 != k15_lattice3(sK6,k1_tarski(sK7))
    | spl11_4 ),
    inference(avatar_component_clause,[],[f162])).

fof(f165,plain,
    ( spl11_3
    | ~ spl11_4
    | spl11_1 ),
    inference(avatar_split_clause,[],[f156,f115,f162,f158])).

fof(f115,plain,
    ( spl11_1
  <=> sK7 = k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f156,plain,
    ( sK7 != k15_lattice3(sK6,k1_tarski(sK7))
    | v1_xboole_0(u1_struct_0(sK6))
    | spl11_1 ),
    inference(subsumption_resolution,[],[f155,f71])).

fof(f155,plain,
    ( sK7 != k15_lattice3(sK6,k1_tarski(sK7))
    | ~ m1_subset_1(sK7,u1_struct_0(sK6))
    | v1_xboole_0(u1_struct_0(sK6))
    | spl11_1 ),
    inference(superposition,[],[f117,f101])).

fof(f117,plain,
    ( sK7 != k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK7))
    | spl11_1 ),
    inference(avatar_component_clause,[],[f115])).

fof(f122,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f72,f119,f115])).

fof(f72,plain,
    ( sK7 != k16_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK7))
    | sK7 != k15_lattice3(sK6,k6_domain_1(u1_struct_0(sK6),sK7)) ),
    inference(cnf_transformation,[],[f49])).

%------------------------------------------------------------------------------
