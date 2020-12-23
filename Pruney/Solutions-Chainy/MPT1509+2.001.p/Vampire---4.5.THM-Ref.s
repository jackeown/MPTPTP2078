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
% DateTime   : Thu Dec  3 13:15:45 EST 2020

% Result     : Theorem 1.98s
% Output     : Refutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :  231 (1622 expanded)
%              Number of leaves         :   28 ( 495 expanded)
%              Depth                    :   42
%              Number of atoms          : 1173 (10662 expanded)
%              Number of equality atoms :  153 (2816 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1492,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f155,f191,f239,f1298,f1491])).

fof(f1491,plain,
    ( spl10_2
    | ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f1490])).

fof(f1490,plain,
    ( $false
    | spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1489,f87])).

fof(f87,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( sK1 != k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
      | sK1 != k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f57,f56])).

fof(f56,plain,
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
          ( ( k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X1)) != X1
            | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X1] :
        ( ( k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X1)) != X1
          | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X1)) != X1 )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ( sK1 != k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        | sK1 != k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
            | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1
            | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
              & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f1489,plain,
    ( v2_struct_0(sK0)
    | spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1488,f88])).

fof(f88,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f1488,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1487,f89])).

fof(f89,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f1487,plain,
    ( ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1486,f90])).

fof(f90,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f1486,plain,
    ( ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1485,f91])).

fof(f91,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f58])).

fof(f1485,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1484,f140])).

fof(f140,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f139])).

fof(f139,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f133])).

fof(f133,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK9(X0,X1) != X0
            | ~ r2_hidden(sK9(X0,X1),X1) )
          & ( sK9(X0,X1) = X0
            | r2_hidden(sK9(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f84,f85])).

fof(f85,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK9(X0,X1) != X0
          | ~ r2_hidden(sK9(X0,X1),X1) )
        & ( sK9(X0,X1) = X0
          | r2_hidden(sK9(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f1484,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1482,f282])).

fof(f282,plain,
    ( sK1 != k16_lattice3(sK0,k1_tarski(sK1))
    | spl10_2
    | ~ spl10_4 ),
    inference(superposition,[],[f154,f190])).

fof(f190,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl10_4
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f154,plain,
    ( sK1 != k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl10_2
  <=> sK1 = k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f1482,plain,
    ( sK1 = k16_lattice3(sK0,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_2
    | ~ spl10_4 ),
    inference(resolution,[],[f1404,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattice3(X0,X1,X2)
      | k16_lattice3(X0,X2) = X1
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f1404,plain,
    ( r3_lattice3(sK0,sK1,k1_tarski(sK1))
    | spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1403,f87])).

fof(f1403,plain,
    ( r3_lattice3(sK0,sK1,k1_tarski(sK1))
    | v2_struct_0(sK0)
    | spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1402,f90])).

fof(f1402,plain,
    ( r3_lattice3(sK0,sK1,k1_tarski(sK1))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1401,f91])).

fof(f1401,plain,
    ( r3_lattice3(sK0,sK1,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1400,f395])).

fof(f395,plain,(
    r1_lattices(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f391,f383])).

fof(f383,plain,(
    sK1 = k2_lattices(sK0,sK1,sK1) ),
    inference(forward_demodulation,[],[f380,f214])).

fof(f214,plain,(
    sK1 = k1_lattices(sK0,sK1,sK1) ),
    inference(subsumption_resolution,[],[f213,f87])).

fof(f213,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f212,f165])).

fof(f165,plain,(
    v6_lattices(sK0) ),
    inference(subsumption_resolution,[],[f164,f90])).

fof(f164,plain,
    ( v6_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f163,f87])).

fof(f163,plain,
    ( v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f98,f88])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v7_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f4,axiom,(
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

fof(f212,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f211,f171])).

fof(f171,plain,(
    v8_lattices(sK0) ),
    inference(subsumption_resolution,[],[f170,f90])).

fof(f170,plain,
    ( v8_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f169,f87])).

fof(f169,plain,
    ( v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f100,f88])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f211,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f210,f174])).

fof(f174,plain,(
    v9_lattices(sK0) ),
    inference(subsumption_resolution,[],[f173,f90])).

fof(f173,plain,
    ( v9_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f172,f87])).

fof(f172,plain,
    ( v9_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f101,f88])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f210,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f209,f90])).

fof(f209,plain,
    ( sK1 = k1_lattices(sK0,sK1,sK1)
    | ~ l3_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f109,f91])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_lattices(X0,X1,X1) = X1
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).

fof(f380,plain,(
    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1)) ),
    inference(resolution,[],[f222,f91])).

fof(f222,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | k2_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) = X0 ) ),
    inference(subsumption_resolution,[],[f221,f87])).

fof(f221,plain,(
    ! [X0] :
      ( k2_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f220,f90])).

fof(f220,plain,(
    ! [X0] :
      ( k2_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f219,f174])).

fof(f219,plain,(
    ! [X0] :
      ( k2_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) = X0
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f118,f91])).

fof(f118,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0)))
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f71,f73,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f73,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0)))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f71,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(f391,plain,
    ( r1_lattices(sK0,sK1,sK1)
    | sK1 != k2_lattices(sK0,sK1,sK1) ),
    inference(resolution,[],[f235,f91])).

fof(f235,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,sK1)
      | k2_lattices(sK0,X0,sK1) != X0 ) ),
    inference(subsumption_resolution,[],[f234,f87])).

fof(f234,plain,(
    ! [X0] :
      ( k2_lattices(sK0,X0,sK1) != X0
      | r1_lattices(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f233,f171])).

fof(f233,plain,(
    ! [X0] :
      ( k2_lattices(sK0,X0,sK1) != X0
      | r1_lattices(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f232,f174])).

fof(f232,plain,(
    ! [X0] :
      ( k2_lattices(sK0,X0,sK1) != X0
      | r1_lattices(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f231,f90])).

fof(f231,plain,(
    ! [X0] :
      ( k2_lattices(sK0,X0,sK1) != X0
      | r1_lattices(sK0,X0,sK1)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v9_lattices(sK0)
      | ~ v8_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f112,f91])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k2_lattices(X0,X1,X2) != X1
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(f1400,plain,
    ( ~ r1_lattices(sK0,sK1,sK1)
    | r3_lattice3(sK0,sK1,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_2
    | ~ spl10_4 ),
    inference(superposition,[],[f129,f1272])).

fof(f1272,plain,
    ( sK1 = sK8(sK0,sK1,k1_tarski(sK1))
    | spl10_2
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1271,f282])).

fof(f1271,plain,
    ( sK1 = k16_lattice3(sK0,k1_tarski(sK1))
    | sK1 = sK8(sK0,sK1,k1_tarski(sK1)) ),
    inference(resolution,[],[f481,f140])).

fof(f481,plain,(
    ! [X1] :
      ( ~ r2_hidden(sK1,k1_tarski(X1))
      | sK1 = k16_lattice3(sK0,k1_tarski(X1))
      | sK8(sK0,sK1,k1_tarski(X1)) = X1 ) ),
    inference(subsumption_resolution,[],[f480,f87])).

fof(f480,plain,(
    ! [X1] :
      ( sK8(sK0,sK1,k1_tarski(X1)) = X1
      | sK1 = k16_lattice3(sK0,k1_tarski(X1))
      | ~ r2_hidden(sK1,k1_tarski(X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f479,f88])).

fof(f479,plain,(
    ! [X1] :
      ( sK8(sK0,sK1,k1_tarski(X1)) = X1
      | sK1 = k16_lattice3(sK0,k1_tarski(X1))
      | ~ r2_hidden(sK1,k1_tarski(X1))
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f478,f89])).

fof(f478,plain,(
    ! [X1] :
      ( sK8(sK0,sK1,k1_tarski(X1)) = X1
      | sK1 = k16_lattice3(sK0,k1_tarski(X1))
      | ~ r2_hidden(sK1,k1_tarski(X1))
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f477,f90])).

fof(f477,plain,(
    ! [X1] :
      ( sK8(sK0,sK1,k1_tarski(X1)) = X1
      | sK1 = k16_lattice3(sK0,k1_tarski(X1))
      | ~ r2_hidden(sK1,k1_tarski(X1))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f473,f91])).

fof(f473,plain,(
    ! [X1] :
      ( sK8(sK0,sK1,k1_tarski(X1)) = X1
      | sK1 = k16_lattice3(sK0,k1_tarski(X1))
      | ~ r2_hidden(sK1,k1_tarski(X1))
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f288,f110])).

fof(f288,plain,(
    ! [X0] :
      ( r3_lattice3(sK0,sK1,k1_tarski(X0))
      | sK8(sK0,sK1,k1_tarski(X0)) = X0 ) ),
    inference(resolution,[],[f200,f141])).

fof(f141,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f132])).

fof(f132,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f86])).

fof(f200,plain,(
    ! [X0] :
      ( r2_hidden(sK8(sK0,sK1,X0),X0)
      | r3_lattice3(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f199,f87])).

fof(f199,plain,(
    ! [X0] :
      ( r2_hidden(sK8(sK0,sK1,X0),X0)
      | r3_lattice3(sK0,sK1,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f198,f90])).

fof(f198,plain,(
    ! [X0] :
      ( r2_hidden(sK8(sK0,sK1,X0),X0)
      | r3_lattice3(sK0,sK1,X0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f128,f91])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK8(X0,X1,X2),X2)
      | r3_lattice3(X0,X1,X2)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f82,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK8(X0,X1,X2))
                  & r2_hidden(sK8(X0,X1,X2),X2)
                  & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f80,f81])).

fof(f81,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK8(X0,X1,X2))
        & r2_hidden(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X1,X3)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X1,X3)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,sK8(X0,X1,X2))
      | r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f1298,plain,
    ( spl10_1
    | ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f1297])).

fof(f1297,plain,
    ( $false
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1296,f87])).

fof(f1296,plain,
    ( v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1295,f88])).

fof(f1295,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1294,f89])).

fof(f1294,plain,
    ( ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1293,f90])).

fof(f1293,plain,
    ( ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1292,f177])).

fof(f177,plain,(
    ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f176,f87])).

fof(f176,plain,(
    ! [X0] :
      ( m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f131,f90])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f1292,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1291,f91])).

fof(f1291,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1277,f605])).

fof(f605,plain,
    ( ~ r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f604,f87])).

fof(f604,plain,
    ( ~ r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f603,f162])).

fof(f162,plain,(
    v4_lattices(sK0) ),
    inference(subsumption_resolution,[],[f161,f90])).

fof(f161,plain,
    ( v4_lattices(sK0)
    | ~ l3_lattices(sK0) ),
    inference(subsumption_resolution,[],[f160,f87])).

fof(f160,plain,
    ( v4_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0) ),
    inference(resolution,[],[f97,f88])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f603,plain,
    ( ~ r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f602,f158])).

fof(f158,plain,(
    l2_lattices(sK0) ),
    inference(resolution,[],[f95,f90])).

fof(f95,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f602,plain,
    ( ~ r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1)
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f601,f177])).

fof(f601,plain,
    ( ~ r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f600,f91])).

fof(f600,plain,
    ( ~ r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f586,f283])).

fof(f283,plain,
    ( sK1 != k15_lattice3(sK0,k1_tarski(sK1))
    | spl10_1
    | ~ spl10_4 ),
    inference(superposition,[],[f150,f190])).

fof(f150,plain,
    ( sK1 != k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f148])).

fof(f148,plain,
    ( spl10_1
  <=> sK1 = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f586,plain,
    ( sK1 = k15_lattice3(sK0,k1_tarski(sK1))
    | ~ r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f487,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( X1 = X2
              | ~ r1_lattices(X0,X2,X1)
              | ~ r1_lattices(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r1_lattices(X0,X2,X1)
                  & r1_lattices(X0,X1,X2) )
               => X1 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).

fof(f487,plain,(
    r1_lattices(sK0,sK1,k15_lattice3(sK0,k1_tarski(sK1))) ),
    inference(resolution,[],[f418,f91])).

fof(f418,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,k1_tarski(X0))) ) ),
    inference(subsumption_resolution,[],[f417,f87])).

fof(f417,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,k1_tarski(X0)))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f416,f90])).

fof(f416,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,k1_tarski(X0)))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f415,f177])).

fof(f415,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k15_lattice3(sK0,k1_tarski(X0)))
      | ~ m1_subset_1(k15_lattice3(sK0,k1_tarski(X0)),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f223,f254])).

fof(f254,plain,(
    ! [X0] : r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) ),
    inference(subsumption_resolution,[],[f253,f87])).

fof(f253,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f252,f88])).

fof(f252,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f251,f89])).

fof(f251,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f240,f90])).

fof(f240,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f177,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r4_lattice3(X0,k15_lattice3(X0,X1),X1)
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X0,X2,X1)
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
                & r4_lattice3(X0,sK4(X0,X1,X2),X1)
                & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f67,f68])).

fof(f68,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK4(X0,X1,X2))
        & r4_lattice3(X0,sK4(X0,X1,X2),X1)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X4] :
                    ( r1_lattices(X0,X2,X4)
                    | ~ r4_lattice3(X0,X4,X1)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ? [X3] :
                  ( ~ r1_lattices(X0,X2,X3)
                  & r4_lattice3(X0,X3,X1)
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ r4_lattice3(X0,X2,X1) )
            & ( ( ! [X3] :
                    ( r1_lattices(X0,X2,X3)
                    | ~ r4_lattice3(X0,X3,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                & r4_lattice3(X0,X2,X1) )
              | k15_lattice3(X0,X1) != X2 ) )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f223,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_lattice3(X0,X2,k1_tarski(X1))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f122,f140])).

fof(f122,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X2)
      | r1_lattices(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK7(X0,X1,X2),X1)
                  & r2_hidden(sK7(X0,X1,X2),X2)
                  & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f76,f77])).

fof(f77,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK7(X0,X1,X2),X1)
        & r2_hidden(sK7(X0,X1,X2),X2)
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ? [X3] :
                    ( ~ r1_lattices(X0,X3,X1)
                    & r2_hidden(X3,X2)
                    & m1_subset_1(X3,u1_struct_0(X0)) ) )
              & ( ! [X3] :
                    ( r1_lattices(X0,X3,X1)
                    | ~ r2_hidden(X3,X2)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f1277,plain,
    ( r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_tarski(sK1)),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(resolution,[],[f1227,f143])).

fof(f143,plain,(
    ! [X4,X0,X1] :
      ( ~ r4_lattice3(X0,X4,X1)
      | r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,(
    ! [X4,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f114])).

fof(f114,plain,(
    ! [X4,X2,X0,X1] :
      ( r1_lattices(X0,X2,X4)
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | k15_lattice3(X0,X1) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f1227,plain,
    ( r4_lattice3(sK0,sK1,k1_tarski(sK1))
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1226,f87])).

fof(f1226,plain,
    ( r4_lattice3(sK0,sK1,k1_tarski(sK1))
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1225,f90])).

fof(f1225,plain,
    ( r4_lattice3(sK0,sK1,k1_tarski(sK1))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1224,f91])).

fof(f1224,plain,
    ( r4_lattice3(sK0,sK1,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f1223,f395])).

fof(f1223,plain,
    ( ~ r1_lattices(sK0,sK1,sK1)
    | r4_lattice3(sK0,sK1,k1_tarski(sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_1
    | ~ spl10_4 ),
    inference(superposition,[],[f125,f1130])).

fof(f1130,plain,
    ( sK1 = sK7(sK0,sK1,k1_tarski(sK1))
    | spl10_1
    | ~ spl10_4 ),
    inference(resolution,[],[f471,f605])).

fof(f471,plain,(
    ! [X3] :
      ( r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(X3)),sK1)
      | sK7(sK0,sK1,k1_tarski(X3)) = X3 ) ),
    inference(subsumption_resolution,[],[f470,f87])).

fof(f470,plain,(
    ! [X3] :
      ( sK7(sK0,sK1,k1_tarski(X3)) = X3
      | r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(X3)),sK1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f469,f88])).

fof(f469,plain,(
    ! [X3] :
      ( sK7(sK0,sK1,k1_tarski(X3)) = X3
      | r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(X3)),sK1)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f468,f89])).

fof(f468,plain,(
    ! [X3] :
      ( sK7(sK0,sK1,k1_tarski(X3)) = X3
      | r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(X3)),sK1)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f467,f90])).

fof(f467,plain,(
    ! [X3] :
      ( sK7(sK0,sK1,k1_tarski(X3)) = X3
      | r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(X3)),sK1)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f466,f177])).

fof(f466,plain,(
    ! [X3] :
      ( sK7(sK0,sK1,k1_tarski(X3)) = X3
      | r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(X3)),sK1)
      | ~ m1_subset_1(k15_lattice3(sK0,k1_tarski(X3)),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f452,f91])).

fof(f452,plain,(
    ! [X3] :
      ( sK7(sK0,sK1,k1_tarski(X3)) = X3
      | r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(X3)),sK1)
      | ~ m1_subset_1(sK1,u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,k1_tarski(X3)),u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f284,f143])).

fof(f284,plain,(
    ! [X0] :
      ( r4_lattice3(sK0,sK1,k1_tarski(X0))
      | sK7(sK0,sK1,k1_tarski(X0)) = X0 ) ),
    inference(resolution,[],[f197,f141])).

fof(f197,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK0,sK1,X0),X0)
      | r4_lattice3(sK0,sK1,X0) ) ),
    inference(subsumption_resolution,[],[f196,f87])).

fof(f196,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK0,sK1,X0),X0)
      | r4_lattice3(sK0,sK1,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f195,f90])).

fof(f195,plain,(
    ! [X0] :
      ( r2_hidden(sK7(sK0,sK1,X0),X0)
      | r4_lattice3(sK0,sK1,X0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f124,f91])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK7(X0,X1,X2),X2)
      | r4_lattice3(X0,X1,X2)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,sK7(X0,X1,X2),X1)
      | r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f239,plain,(
    ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f237,f87])).

fof(f237,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f236,f175])).

fof(f175,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f158,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ l2_lattices(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l2_lattices)).

fof(f236,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_3 ),
    inference(resolution,[],[f186,f104])).

fof(f104,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f186,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl10_3
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f191,plain,
    ( spl10_3
    | spl10_4 ),
    inference(avatar_split_clause,[],[f182,f188,f184])).

fof(f182,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | v1_xboole_0(u1_struct_0(sK0)) ),
    inference(resolution,[],[f130,f91])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f155,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f92,f152,f148])).

fof(f92,plain,
    ( sK1 != k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
    | sK1 != k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.09  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.11  % Command    : run_vampire %s %d
% 0.11/0.30  % Computer   : n006.cluster.edu
% 0.11/0.30  % Model      : x86_64 x86_64
% 0.11/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.30  % Memory     : 8042.1875MB
% 0.11/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.30  % CPULimit   : 60
% 0.11/0.30  % WCLimit    : 600
% 0.11/0.30  % DateTime   : Tue Dec  1 12:15:22 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.17/0.44  % (813)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.17/0.45  % (814)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.17/0.45  % (805)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.17/0.45  % (815)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.17/0.46  % (806)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.17/0.46  % (810)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.17/0.46  % (808)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.17/0.46  % (812)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.17/0.47  % (807)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.17/0.47  % (828)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.17/0.47  % (827)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.17/0.47  % (809)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.17/0.48  % (825)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.17/0.48  % (819)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.17/0.49  % (822)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.17/0.49  % (829)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.17/0.49  % (804)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.17/0.49  % (823)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.17/0.49  % (804)Refutation not found, incomplete strategy% (804)------------------------------
% 0.17/0.49  % (804)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.49  % (804)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.49  
% 0.17/0.49  % (804)Memory used [KB]: 10618
% 0.17/0.49  % (804)Time elapsed: 0.121 s
% 0.17/0.49  % (804)------------------------------
% 0.17/0.49  % (804)------------------------------
% 0.17/0.50  % (818)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.17/0.50  % (817)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.17/0.50  % (821)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.17/0.51  % (811)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.17/0.51  % (824)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.17/0.52  % (816)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.17/0.53  % (832)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.17/0.54  % (811)Refutation not found, incomplete strategy% (811)------------------------------
% 0.17/0.54  % (811)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.54  % (811)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.54  
% 0.17/0.54  % (811)Memory used [KB]: 1791
% 0.17/0.54  % (811)Time elapsed: 0.137 s
% 0.17/0.54  % (811)------------------------------
% 0.17/0.54  % (811)------------------------------
% 0.17/0.54  % (820)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.98/0.57  % (814)Refutation found. Thanks to Tanya!
% 1.98/0.57  % SZS status Theorem for theBenchmark
% 1.98/0.57  % SZS output start Proof for theBenchmark
% 1.98/0.57  fof(f1492,plain,(
% 1.98/0.57    $false),
% 1.98/0.57    inference(avatar_sat_refutation,[],[f155,f191,f239,f1298,f1491])).
% 1.98/0.57  fof(f1491,plain,(
% 1.98/0.57    spl10_2 | ~spl10_4),
% 1.98/0.57    inference(avatar_contradiction_clause,[],[f1490])).
% 1.98/0.57  fof(f1490,plain,(
% 1.98/0.57    $false | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1489,f87])).
% 1.98/0.57  fof(f87,plain,(
% 1.98/0.57    ~v2_struct_0(sK0)),
% 1.98/0.57    inference(cnf_transformation,[],[f58])).
% 1.98/0.57  fof(f58,plain,(
% 1.98/0.57    ((sK1 != k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | sK1 != k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 1.98/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f57,f56])).
% 1.98/0.57  fof(f56,plain,(
% 1.98/0.57    ? [X0] : (? [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : ((k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X1)) != X1 | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X1)) != X1) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 1.98/0.57    introduced(choice_axiom,[])).
% 1.98/0.57  fof(f57,plain,(
% 1.98/0.57    ? [X1] : ((k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X1)) != X1 | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X1)) != X1) & m1_subset_1(X1,u1_struct_0(sK0))) => ((sK1 != k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | sK1 != k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 1.98/0.57    introduced(choice_axiom,[])).
% 1.98/0.57  fof(f23,plain,(
% 1.98/0.57    ? [X0] : (? [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.98/0.57    inference(flattening,[],[f22])).
% 1.98/0.57  fof(f22,plain,(
% 1.98/0.57    ? [X0] : (? [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1 | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) != X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.98/0.57    inference(ennf_transformation,[],[f20])).
% 1.98/0.57  fof(f20,negated_conjecture,(
% 1.98/0.57    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 1.98/0.57    inference(negated_conjecture,[],[f19])).
% 1.98/0.57  fof(f19,conjecture,(
% 1.98/0.57    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).
% 1.98/0.57  fof(f1489,plain,(
% 1.98/0.57    v2_struct_0(sK0) | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1488,f88])).
% 1.98/0.57  fof(f88,plain,(
% 1.98/0.57    v10_lattices(sK0)),
% 1.98/0.57    inference(cnf_transformation,[],[f58])).
% 1.98/0.57  fof(f1488,plain,(
% 1.98/0.57    ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1487,f89])).
% 1.98/0.57  fof(f89,plain,(
% 1.98/0.57    v4_lattice3(sK0)),
% 1.98/0.57    inference(cnf_transformation,[],[f58])).
% 1.98/0.57  fof(f1487,plain,(
% 1.98/0.57    ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1486,f90])).
% 1.98/0.57  fof(f90,plain,(
% 1.98/0.57    l3_lattices(sK0)),
% 1.98/0.57    inference(cnf_transformation,[],[f58])).
% 1.98/0.57  fof(f1486,plain,(
% 1.98/0.57    ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1485,f91])).
% 1.98/0.57  fof(f91,plain,(
% 1.98/0.57    m1_subset_1(sK1,u1_struct_0(sK0))),
% 1.98/0.57    inference(cnf_transformation,[],[f58])).
% 1.98/0.57  fof(f1485,plain,(
% 1.98/0.57    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1484,f140])).
% 1.98/0.57  fof(f140,plain,(
% 1.98/0.57    ( ! [X3] : (r2_hidden(X3,k1_tarski(X3))) )),
% 1.98/0.57    inference(equality_resolution,[],[f139])).
% 1.98/0.57  fof(f139,plain,(
% 1.98/0.57    ( ! [X3,X1] : (r2_hidden(X3,X1) | k1_tarski(X3) != X1) )),
% 1.98/0.57    inference(equality_resolution,[],[f133])).
% 1.98/0.57  fof(f133,plain,(
% 1.98/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.98/0.57    inference(cnf_transformation,[],[f86])).
% 1.98/0.57  fof(f86,plain,(
% 1.98/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.98/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f84,f85])).
% 1.98/0.57  fof(f85,plain,(
% 1.98/0.57    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK9(X0,X1) != X0 | ~r2_hidden(sK9(X0,X1),X1)) & (sK9(X0,X1) = X0 | r2_hidden(sK9(X0,X1),X1))))),
% 1.98/0.57    introduced(choice_axiom,[])).
% 1.98/0.57  fof(f84,plain,(
% 1.98/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.98/0.57    inference(rectify,[],[f83])).
% 1.98/0.57  fof(f83,plain,(
% 1.98/0.57    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.98/0.57    inference(nnf_transformation,[],[f1])).
% 1.98/0.57  fof(f1,axiom,(
% 1.98/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.98/0.57  fof(f1484,plain,(
% 1.98/0.57    ~r2_hidden(sK1,k1_tarski(sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1482,f282])).
% 1.98/0.57  fof(f282,plain,(
% 1.98/0.57    sK1 != k16_lattice3(sK0,k1_tarski(sK1)) | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(superposition,[],[f154,f190])).
% 1.98/0.57  fof(f190,plain,(
% 1.98/0.57    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | ~spl10_4),
% 1.98/0.57    inference(avatar_component_clause,[],[f188])).
% 1.98/0.57  fof(f188,plain,(
% 1.98/0.57    spl10_4 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 1.98/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 1.98/0.57  fof(f154,plain,(
% 1.98/0.57    sK1 != k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | spl10_2),
% 1.98/0.57    inference(avatar_component_clause,[],[f152])).
% 1.98/0.57  fof(f152,plain,(
% 1.98/0.57    spl10_2 <=> sK1 = k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.98/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.98/0.57  fof(f1482,plain,(
% 1.98/0.57    sK1 = k16_lattice3(sK0,k1_tarski(sK1)) | ~r2_hidden(sK1,k1_tarski(sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(resolution,[],[f1404,f110])).
% 1.98/0.57  fof(f110,plain,(
% 1.98/0.57    ( ! [X2,X0,X1] : (~r3_lattice3(X0,X1,X2) | k16_lattice3(X0,X2) = X1 | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f39])).
% 1.98/0.57  fof(f39,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 | ~r3_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(flattening,[],[f38])).
% 1.98/0.57  fof(f38,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 | (~r3_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.98/0.57    inference(ennf_transformation,[],[f18])).
% 1.98/0.57  fof(f18,axiom,(
% 1.98/0.57    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r3_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k16_lattice3(X0,X2) = X1)))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_lattice3)).
% 1.98/0.57  fof(f1404,plain,(
% 1.98/0.57    r3_lattice3(sK0,sK1,k1_tarski(sK1)) | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1403,f87])).
% 1.98/0.57  fof(f1403,plain,(
% 1.98/0.57    r3_lattice3(sK0,sK1,k1_tarski(sK1)) | v2_struct_0(sK0) | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1402,f90])).
% 1.98/0.57  fof(f1402,plain,(
% 1.98/0.57    r3_lattice3(sK0,sK1,k1_tarski(sK1)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1401,f91])).
% 1.98/0.57  fof(f1401,plain,(
% 1.98/0.57    r3_lattice3(sK0,sK1,k1_tarski(sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1400,f395])).
% 1.98/0.57  fof(f395,plain,(
% 1.98/0.57    r1_lattices(sK0,sK1,sK1)),
% 1.98/0.57    inference(subsumption_resolution,[],[f391,f383])).
% 1.98/0.57  fof(f383,plain,(
% 1.98/0.57    sK1 = k2_lattices(sK0,sK1,sK1)),
% 1.98/0.57    inference(forward_demodulation,[],[f380,f214])).
% 1.98/0.57  fof(f214,plain,(
% 1.98/0.57    sK1 = k1_lattices(sK0,sK1,sK1)),
% 1.98/0.57    inference(subsumption_resolution,[],[f213,f87])).
% 1.98/0.57  fof(f213,plain,(
% 1.98/0.57    sK1 = k1_lattices(sK0,sK1,sK1) | v2_struct_0(sK0)),
% 1.98/0.57    inference(subsumption_resolution,[],[f212,f165])).
% 1.98/0.57  fof(f165,plain,(
% 1.98/0.57    v6_lattices(sK0)),
% 1.98/0.57    inference(subsumption_resolution,[],[f164,f90])).
% 1.98/0.57  fof(f164,plain,(
% 1.98/0.57    v6_lattices(sK0) | ~l3_lattices(sK0)),
% 1.98/0.57    inference(subsumption_resolution,[],[f163,f87])).
% 1.98/0.57  fof(f163,plain,(
% 1.98/0.57    v6_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.98/0.57    inference(resolution,[],[f98,f88])).
% 1.98/0.57  fof(f98,plain,(
% 1.98/0.57    ( ! [X0] : (~v10_lattices(X0) | v6_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f27])).
% 1.98/0.57  fof(f27,plain,(
% 1.98/0.57    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.98/0.57    inference(flattening,[],[f26])).
% 1.98/0.57  fof(f26,plain,(
% 1.98/0.57    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.98/0.57    inference(ennf_transformation,[],[f21])).
% 1.98/0.57  fof(f21,plain,(
% 1.98/0.57    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.98/0.57    inference(pure_predicate_removal,[],[f4])).
% 1.98/0.57  fof(f4,axiom,(
% 1.98/0.57    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 1.98/0.57  fof(f212,plain,(
% 1.98/0.57    sK1 = k1_lattices(sK0,sK1,sK1) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.98/0.57    inference(subsumption_resolution,[],[f211,f171])).
% 1.98/0.57  fof(f171,plain,(
% 1.98/0.57    v8_lattices(sK0)),
% 1.98/0.57    inference(subsumption_resolution,[],[f170,f90])).
% 1.98/0.57  fof(f170,plain,(
% 1.98/0.57    v8_lattices(sK0) | ~l3_lattices(sK0)),
% 1.98/0.57    inference(subsumption_resolution,[],[f169,f87])).
% 1.98/0.57  fof(f169,plain,(
% 1.98/0.57    v8_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.98/0.57    inference(resolution,[],[f100,f88])).
% 1.98/0.57  fof(f100,plain,(
% 1.98/0.57    ( ! [X0] : (~v10_lattices(X0) | v8_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f27])).
% 1.98/0.57  fof(f211,plain,(
% 1.98/0.57    sK1 = k1_lattices(sK0,sK1,sK1) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.98/0.57    inference(subsumption_resolution,[],[f210,f174])).
% 1.98/0.57  fof(f174,plain,(
% 1.98/0.57    v9_lattices(sK0)),
% 1.98/0.57    inference(subsumption_resolution,[],[f173,f90])).
% 1.98/0.57  fof(f173,plain,(
% 1.98/0.57    v9_lattices(sK0) | ~l3_lattices(sK0)),
% 1.98/0.57    inference(subsumption_resolution,[],[f172,f87])).
% 1.98/0.57  fof(f172,plain,(
% 1.98/0.57    v9_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.98/0.57    inference(resolution,[],[f101,f88])).
% 1.98/0.57  fof(f101,plain,(
% 1.98/0.57    ( ! [X0] : (~v10_lattices(X0) | v9_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f27])).
% 1.98/0.57  fof(f210,plain,(
% 1.98/0.57    sK1 = k1_lattices(sK0,sK1,sK1) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.98/0.57    inference(subsumption_resolution,[],[f209,f90])).
% 1.98/0.57  fof(f209,plain,(
% 1.98/0.57    sK1 = k1_lattices(sK0,sK1,sK1) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0)),
% 1.98/0.57    inference(resolution,[],[f109,f91])).
% 1.98/0.57  fof(f109,plain,(
% 1.98/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | k1_lattices(X0,X1,X1) = X1 | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f37])).
% 1.98/0.57  fof(f37,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(flattening,[],[f36])).
% 1.98/0.57  fof(f36,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (k1_lattices(X0,X1,X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.98/0.57    inference(ennf_transformation,[],[f9])).
% 1.98/0.57  fof(f9,axiom,(
% 1.98/0.57    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k1_lattices(X0,X1,X1) = X1))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_lattices)).
% 1.98/0.57  fof(f380,plain,(
% 1.98/0.57    sK1 = k2_lattices(sK0,sK1,k1_lattices(sK0,sK1,sK1))),
% 1.98/0.57    inference(resolution,[],[f222,f91])).
% 1.98/0.57  fof(f222,plain,(
% 1.98/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) = X0) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f221,f87])).
% 1.98/0.57  fof(f221,plain,(
% 1.98/0.57    ( ! [X0] : (k2_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f220,f90])).
% 1.98/0.57  fof(f220,plain,(
% 1.98/0.57    ( ! [X0] : (k2_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f219,f174])).
% 1.98/0.57  fof(f219,plain,(
% 1.98/0.57    ( ! [X0] : (k2_lattices(sK0,X0,k1_lattices(sK0,X0,sK1)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(resolution,[],[f118,f91])).
% 1.98/0.57  fof(f118,plain,(
% 1.98/0.57    ( ! [X4,X0,X3] : (~m1_subset_1(X4,u1_struct_0(X0)) | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f74])).
% 1.98/0.57  fof(f74,plain,(
% 1.98/0.57    ! [X0] : (((v9_lattices(X0) | ((sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f71,f73,f72])).
% 1.98/0.57  fof(f72,plain,(
% 1.98/0.57    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 1.98/0.57    introduced(choice_axiom,[])).
% 1.98/0.57  fof(f73,plain,(
% 1.98/0.57    ! [X0] : (? [X2] : (sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK5(X0) != k2_lattices(X0,sK5(X0),k1_lattices(X0,sK5(X0),sK6(X0))) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 1.98/0.57    introduced(choice_axiom,[])).
% 1.98/0.57  fof(f71,plain,(
% 1.98/0.57    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(rectify,[],[f70])).
% 1.98/0.57  fof(f70,plain,(
% 1.98/0.57    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(nnf_transformation,[],[f45])).
% 1.98/0.57  fof(f45,plain,(
% 1.98/0.57    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(flattening,[],[f44])).
% 1.98/0.57  fof(f44,plain,(
% 1.98/0.57    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.98/0.57    inference(ennf_transformation,[],[f5])).
% 1.98/0.57  fof(f5,axiom,(
% 1.98/0.57    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).
% 1.98/0.57  fof(f391,plain,(
% 1.98/0.57    r1_lattices(sK0,sK1,sK1) | sK1 != k2_lattices(sK0,sK1,sK1)),
% 1.98/0.57    inference(resolution,[],[f235,f91])).
% 1.98/0.57  fof(f235,plain,(
% 1.98/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,sK1) | k2_lattices(sK0,X0,sK1) != X0) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f234,f87])).
% 1.98/0.57  fof(f234,plain,(
% 1.98/0.57    ( ! [X0] : (k2_lattices(sK0,X0,sK1) != X0 | r1_lattices(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f233,f171])).
% 1.98/0.57  fof(f233,plain,(
% 1.98/0.57    ( ! [X0] : (k2_lattices(sK0,X0,sK1) != X0 | r1_lattices(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f232,f174])).
% 1.98/0.57  fof(f232,plain,(
% 1.98/0.57    ( ! [X0] : (k2_lattices(sK0,X0,sK1) != X0 | r1_lattices(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f231,f90])).
% 1.98/0.57  fof(f231,plain,(
% 1.98/0.57    ( ! [X0] : (k2_lattices(sK0,X0,sK1) != X0 | r1_lattices(sK0,X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(resolution,[],[f112,f91])).
% 1.98/0.57  fof(f112,plain,(
% 1.98/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k2_lattices(X0,X1,X2) != X1 | r1_lattices(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f64])).
% 1.98/0.57  fof(f64,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(nnf_transformation,[],[f41])).
% 1.98/0.57  fof(f41,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(flattening,[],[f40])).
% 1.98/0.57  fof(f40,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 1.98/0.57    inference(ennf_transformation,[],[f10])).
% 1.98/0.57  fof(f10,axiom,(
% 1.98/0.57    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 1.98/0.57  fof(f1400,plain,(
% 1.98/0.57    ~r1_lattices(sK0,sK1,sK1) | r3_lattice3(sK0,sK1,k1_tarski(sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(superposition,[],[f129,f1272])).
% 1.98/0.57  fof(f1272,plain,(
% 1.98/0.57    sK1 = sK8(sK0,sK1,k1_tarski(sK1)) | (spl10_2 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1271,f282])).
% 1.98/0.57  fof(f1271,plain,(
% 1.98/0.57    sK1 = k16_lattice3(sK0,k1_tarski(sK1)) | sK1 = sK8(sK0,sK1,k1_tarski(sK1))),
% 1.98/0.57    inference(resolution,[],[f481,f140])).
% 1.98/0.57  fof(f481,plain,(
% 1.98/0.57    ( ! [X1] : (~r2_hidden(sK1,k1_tarski(X1)) | sK1 = k16_lattice3(sK0,k1_tarski(X1)) | sK8(sK0,sK1,k1_tarski(X1)) = X1) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f480,f87])).
% 1.98/0.57  fof(f480,plain,(
% 1.98/0.57    ( ! [X1] : (sK8(sK0,sK1,k1_tarski(X1)) = X1 | sK1 = k16_lattice3(sK0,k1_tarski(X1)) | ~r2_hidden(sK1,k1_tarski(X1)) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f479,f88])).
% 1.98/0.57  fof(f479,plain,(
% 1.98/0.57    ( ! [X1] : (sK8(sK0,sK1,k1_tarski(X1)) = X1 | sK1 = k16_lattice3(sK0,k1_tarski(X1)) | ~r2_hidden(sK1,k1_tarski(X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f478,f89])).
% 1.98/0.57  fof(f478,plain,(
% 1.98/0.57    ( ! [X1] : (sK8(sK0,sK1,k1_tarski(X1)) = X1 | sK1 = k16_lattice3(sK0,k1_tarski(X1)) | ~r2_hidden(sK1,k1_tarski(X1)) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f477,f90])).
% 1.98/0.57  fof(f477,plain,(
% 1.98/0.57    ( ! [X1] : (sK8(sK0,sK1,k1_tarski(X1)) = X1 | sK1 = k16_lattice3(sK0,k1_tarski(X1)) | ~r2_hidden(sK1,k1_tarski(X1)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f473,f91])).
% 1.98/0.57  fof(f473,plain,(
% 1.98/0.57    ( ! [X1] : (sK8(sK0,sK1,k1_tarski(X1)) = X1 | sK1 = k16_lattice3(sK0,k1_tarski(X1)) | ~r2_hidden(sK1,k1_tarski(X1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(resolution,[],[f288,f110])).
% 1.98/0.57  fof(f288,plain,(
% 1.98/0.57    ( ! [X0] : (r3_lattice3(sK0,sK1,k1_tarski(X0)) | sK8(sK0,sK1,k1_tarski(X0)) = X0) )),
% 1.98/0.57    inference(resolution,[],[f200,f141])).
% 1.98/0.57  fof(f141,plain,(
% 1.98/0.57    ( ! [X0,X3] : (~r2_hidden(X3,k1_tarski(X0)) | X0 = X3) )),
% 1.98/0.57    inference(equality_resolution,[],[f132])).
% 1.98/0.57  fof(f132,plain,(
% 1.98/0.57    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.98/0.57    inference(cnf_transformation,[],[f86])).
% 1.98/0.57  fof(f200,plain,(
% 1.98/0.57    ( ! [X0] : (r2_hidden(sK8(sK0,sK1,X0),X0) | r3_lattice3(sK0,sK1,X0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f199,f87])).
% 1.98/0.57  fof(f199,plain,(
% 1.98/0.57    ( ! [X0] : (r2_hidden(sK8(sK0,sK1,X0),X0) | r3_lattice3(sK0,sK1,X0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f198,f90])).
% 1.98/0.57  fof(f198,plain,(
% 1.98/0.57    ( ! [X0] : (r2_hidden(sK8(sK0,sK1,X0),X0) | r3_lattice3(sK0,sK1,X0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(resolution,[],[f128,f91])).
% 1.98/0.57  fof(f128,plain,(
% 1.98/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(sK8(X0,X1,X2),X2) | r3_lattice3(X0,X1,X2) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f82])).
% 1.98/0.57  fof(f82,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | (~r1_lattices(X0,X1,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f80,f81])).
% 1.98/0.57  fof(f81,plain,(
% 1.98/0.57    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X1,sK8(X0,X1,X2)) & r2_hidden(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X0))))),
% 1.98/0.57    introduced(choice_axiom,[])).
% 1.98/0.57  fof(f80,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X1,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(rectify,[],[f79])).
% 1.98/0.57  fof(f79,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(nnf_transformation,[],[f49])).
% 1.98/0.57  fof(f49,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(flattening,[],[f48])).
% 1.98/0.57  fof(f48,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.98/0.57    inference(ennf_transformation,[],[f13])).
% 1.98/0.57  fof(f13,axiom,(
% 1.98/0.57    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattice3)).
% 1.98/0.57  fof(f129,plain,(
% 1.98/0.57    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,sK8(X0,X1,X2)) | r3_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f82])).
% 1.98/0.57  fof(f1298,plain,(
% 1.98/0.57    spl10_1 | ~spl10_4),
% 1.98/0.57    inference(avatar_contradiction_clause,[],[f1297])).
% 1.98/0.57  fof(f1297,plain,(
% 1.98/0.57    $false | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1296,f87])).
% 1.98/0.57  fof(f1296,plain,(
% 1.98/0.57    v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1295,f88])).
% 1.98/0.57  fof(f1295,plain,(
% 1.98/0.57    ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1294,f89])).
% 1.98/0.57  fof(f1294,plain,(
% 1.98/0.57    ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1293,f90])).
% 1.98/0.57  fof(f1293,plain,(
% 1.98/0.57    ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1292,f177])).
% 1.98/0.57  fof(f177,plain,(
% 1.98/0.57    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f176,f87])).
% 1.98/0.57  fof(f176,plain,(
% 1.98/0.57    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(resolution,[],[f131,f90])).
% 1.98/0.57  fof(f131,plain,(
% 1.98/0.57    ( ! [X0,X1] : (~l3_lattices(X0) | m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f53])).
% 1.98/0.57  fof(f53,plain,(
% 1.98/0.57    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(flattening,[],[f52])).
% 1.98/0.57  fof(f52,plain,(
% 1.98/0.57    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.98/0.57    inference(ennf_transformation,[],[f17])).
% 1.98/0.57  fof(f17,axiom,(
% 1.98/0.57    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 1.98/0.57  fof(f1292,plain,(
% 1.98/0.57    ~m1_subset_1(k15_lattice3(sK0,k1_tarski(sK1)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1291,f91])).
% 1.98/0.57  fof(f1291,plain,(
% 1.98/0.57    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_tarski(sK1)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1277,f605])).
% 1.98/0.57  fof(f605,plain,(
% 1.98/0.57    ~r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f604,f87])).
% 1.98/0.57  fof(f604,plain,(
% 1.98/0.57    ~r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f603,f162])).
% 1.98/0.57  fof(f162,plain,(
% 1.98/0.57    v4_lattices(sK0)),
% 1.98/0.57    inference(subsumption_resolution,[],[f161,f90])).
% 1.98/0.57  fof(f161,plain,(
% 1.98/0.57    v4_lattices(sK0) | ~l3_lattices(sK0)),
% 1.98/0.57    inference(subsumption_resolution,[],[f160,f87])).
% 1.98/0.57  fof(f160,plain,(
% 1.98/0.57    v4_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0)),
% 1.98/0.57    inference(resolution,[],[f97,f88])).
% 1.98/0.57  fof(f97,plain,(
% 1.98/0.57    ( ! [X0] : (~v10_lattices(X0) | v4_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f27])).
% 1.98/0.57  fof(f603,plain,(
% 1.98/0.57    ~r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1) | ~v4_lattices(sK0) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f602,f158])).
% 1.98/0.57  fof(f158,plain,(
% 1.98/0.57    l2_lattices(sK0)),
% 1.98/0.57    inference(resolution,[],[f95,f90])).
% 1.98/0.57  fof(f95,plain,(
% 1.98/0.57    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f25])).
% 1.98/0.57  fof(f25,plain,(
% 1.98/0.57    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 1.98/0.57    inference(ennf_transformation,[],[f7])).
% 1.98/0.57  fof(f7,axiom,(
% 1.98/0.57    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 1.98/0.57  fof(f602,plain,(
% 1.98/0.57    ~r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f601,f177])).
% 1.98/0.57  fof(f601,plain,(
% 1.98/0.57    ~r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1) | ~m1_subset_1(k15_lattice3(sK0,k1_tarski(sK1)),u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f600,f91])).
% 1.98/0.57  fof(f600,plain,(
% 1.98/0.57    ~r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_tarski(sK1)),u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f586,f283])).
% 1.98/0.57  fof(f283,plain,(
% 1.98/0.57    sK1 != k15_lattice3(sK0,k1_tarski(sK1)) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(superposition,[],[f150,f190])).
% 1.98/0.57  fof(f150,plain,(
% 1.98/0.57    sK1 != k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | spl10_1),
% 1.98/0.57    inference(avatar_component_clause,[],[f148])).
% 1.98/0.57  fof(f148,plain,(
% 1.98/0.57    spl10_1 <=> sK1 = k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.98/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.98/0.57  fof(f586,plain,(
% 1.98/0.57    sK1 = k15_lattice3(sK0,k1_tarski(sK1)) | ~r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_tarski(sK1)),u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | v2_struct_0(sK0)),
% 1.98/0.57    inference(resolution,[],[f487,f102])).
% 1.98/0.57  fof(f102,plain,(
% 1.98/0.57    ( ! [X2,X0,X1] : (~r1_lattices(X0,X2,X1) | X1 = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f29])).
% 1.98/0.57  fof(f29,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(flattening,[],[f28])).
% 1.98/0.57  fof(f28,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 1.98/0.57    inference(ennf_transformation,[],[f11])).
% 1.98/0.57  fof(f11,axiom,(
% 1.98/0.57    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_lattices)).
% 1.98/0.57  fof(f487,plain,(
% 1.98/0.57    r1_lattices(sK0,sK1,k15_lattice3(sK0,k1_tarski(sK1)))),
% 1.98/0.57    inference(resolution,[],[f418,f91])).
% 1.98/0.57  fof(f418,plain,(
% 1.98/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k15_lattice3(sK0,k1_tarski(X0)))) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f417,f87])).
% 1.98/0.57  fof(f417,plain,(
% 1.98/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k15_lattice3(sK0,k1_tarski(X0))) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f416,f90])).
% 1.98/0.57  fof(f416,plain,(
% 1.98/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k15_lattice3(sK0,k1_tarski(X0))) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f415,f177])).
% 1.98/0.57  fof(f415,plain,(
% 1.98/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r1_lattices(sK0,X0,k15_lattice3(sK0,k1_tarski(X0))) | ~m1_subset_1(k15_lattice3(sK0,k1_tarski(X0)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(resolution,[],[f223,f254])).
% 1.98/0.57  fof(f254,plain,(
% 1.98/0.57    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f253,f87])).
% 1.98/0.57  fof(f253,plain,(
% 1.98/0.57    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f252,f88])).
% 1.98/0.57  fof(f252,plain,(
% 1.98/0.57    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f251,f89])).
% 1.98/0.57  fof(f251,plain,(
% 1.98/0.57    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f240,f90])).
% 1.98/0.57  fof(f240,plain,(
% 1.98/0.57    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),X0) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(resolution,[],[f177,f142])).
% 1.98/0.57  fof(f142,plain,(
% 1.98/0.57    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(duplicate_literal_removal,[],[f138])).
% 1.98/0.57  fof(f138,plain,(
% 1.98/0.57    ( ! [X0,X1] : (r4_lattice3(X0,k15_lattice3(X0,X1),X1) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(equality_resolution,[],[f113])).
% 1.98/0.57  fof(f113,plain,(
% 1.98/0.57    ( ! [X2,X0,X1] : (r4_lattice3(X0,X2,X1) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f69])).
% 1.98/0.57  fof(f69,plain,(
% 1.98/0.57    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK4(X0,X1,X2)) & r4_lattice3(X0,sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f67,f68])).
% 1.98/0.57  fof(f68,plain,(
% 1.98/0.57    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK4(X0,X1,X2)) & r4_lattice3(X0,sK4(X0,X1,X2),X1) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 1.98/0.57    introduced(choice_axiom,[])).
% 1.98/0.57  fof(f67,plain,(
% 1.98/0.57    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(rectify,[],[f66])).
% 1.98/0.57  fof(f66,plain,(
% 1.98/0.57    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(flattening,[],[f65])).
% 1.98/0.57  fof(f65,plain,(
% 1.98/0.57    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(nnf_transformation,[],[f43])).
% 1.98/0.57  fof(f43,plain,(
% 1.98/0.57    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(flattening,[],[f42])).
% 1.98/0.57  fof(f42,plain,(
% 1.98/0.57    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.98/0.57    inference(ennf_transformation,[],[f15])).
% 1.98/0.57  fof(f15,axiom,(
% 1.98/0.57    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 1.98/0.57  fof(f223,plain,(
% 1.98/0.57    ( ! [X2,X0,X1] : (~r4_lattice3(X0,X2,k1_tarski(X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(resolution,[],[f122,f140])).
% 1.98/0.57  fof(f122,plain,(
% 1.98/0.57    ( ! [X4,X2,X0,X1] : (~r2_hidden(X4,X2) | r1_lattices(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f78])).
% 1.98/0.57  fof(f78,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X2) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f76,f77])).
% 1.98/0.57  fof(f77,plain,(
% 1.98/0.57    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK7(X0,X1,X2),X1) & r2_hidden(sK7(X0,X1,X2),X2) & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 1.98/0.57    introduced(choice_axiom,[])).
% 1.98/0.57  fof(f76,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(rectify,[],[f75])).
% 1.98/0.57  fof(f75,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(nnf_transformation,[],[f47])).
% 1.98/0.57  fof(f47,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(flattening,[],[f46])).
% 1.98/0.57  fof(f46,plain,(
% 1.98/0.57    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.98/0.57    inference(ennf_transformation,[],[f14])).
% 1.98/0.57  fof(f14,axiom,(
% 1.98/0.57    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 1.98/0.57  fof(f1277,plain,(
% 1.98/0.57    r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(sK1)),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_tarski(sK1)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(resolution,[],[f1227,f143])).
% 1.98/0.57  fof(f143,plain,(
% 1.98/0.57    ( ! [X4,X0,X1] : (~r4_lattice3(X0,X4,X1) | r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(duplicate_literal_removal,[],[f137])).
% 1.98/0.57  fof(f137,plain,(
% 1.98/0.57    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(equality_resolution,[],[f114])).
% 1.98/0.57  fof(f114,plain,(
% 1.98/0.57    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f69])).
% 1.98/0.57  fof(f1227,plain,(
% 1.98/0.57    r4_lattice3(sK0,sK1,k1_tarski(sK1)) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1226,f87])).
% 1.98/0.57  fof(f1226,plain,(
% 1.98/0.57    r4_lattice3(sK0,sK1,k1_tarski(sK1)) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1225,f90])).
% 1.98/0.57  fof(f1225,plain,(
% 1.98/0.57    r4_lattice3(sK0,sK1,k1_tarski(sK1)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1224,f91])).
% 1.98/0.57  fof(f1224,plain,(
% 1.98/0.57    r4_lattice3(sK0,sK1,k1_tarski(sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(subsumption_resolution,[],[f1223,f395])).
% 1.98/0.57  fof(f1223,plain,(
% 1.98/0.57    ~r1_lattices(sK0,sK1,sK1) | r4_lattice3(sK0,sK1,k1_tarski(sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(superposition,[],[f125,f1130])).
% 1.98/0.57  fof(f1130,plain,(
% 1.98/0.57    sK1 = sK7(sK0,sK1,k1_tarski(sK1)) | (spl10_1 | ~spl10_4)),
% 1.98/0.57    inference(resolution,[],[f471,f605])).
% 1.98/0.57  fof(f471,plain,(
% 1.98/0.57    ( ! [X3] : (r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(X3)),sK1) | sK7(sK0,sK1,k1_tarski(X3)) = X3) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f470,f87])).
% 1.98/0.57  fof(f470,plain,(
% 1.98/0.57    ( ! [X3] : (sK7(sK0,sK1,k1_tarski(X3)) = X3 | r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(X3)),sK1) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f469,f88])).
% 1.98/0.57  fof(f469,plain,(
% 1.98/0.57    ( ! [X3] : (sK7(sK0,sK1,k1_tarski(X3)) = X3 | r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(X3)),sK1) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f468,f89])).
% 1.98/0.57  fof(f468,plain,(
% 1.98/0.57    ( ! [X3] : (sK7(sK0,sK1,k1_tarski(X3)) = X3 | r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(X3)),sK1) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f467,f90])).
% 1.98/0.57  fof(f467,plain,(
% 1.98/0.57    ( ! [X3] : (sK7(sK0,sK1,k1_tarski(X3)) = X3 | r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(X3)),sK1) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f466,f177])).
% 1.98/0.57  fof(f466,plain,(
% 1.98/0.57    ( ! [X3] : (sK7(sK0,sK1,k1_tarski(X3)) = X3 | r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(X3)),sK1) | ~m1_subset_1(k15_lattice3(sK0,k1_tarski(X3)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f452,f91])).
% 1.98/0.57  fof(f452,plain,(
% 1.98/0.57    ( ! [X3] : (sK7(sK0,sK1,k1_tarski(X3)) = X3 | r1_lattices(sK0,k15_lattice3(sK0,k1_tarski(X3)),sK1) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_tarski(X3)),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(resolution,[],[f284,f143])).
% 1.98/0.57  fof(f284,plain,(
% 1.98/0.57    ( ! [X0] : (r4_lattice3(sK0,sK1,k1_tarski(X0)) | sK7(sK0,sK1,k1_tarski(X0)) = X0) )),
% 1.98/0.57    inference(resolution,[],[f197,f141])).
% 1.98/0.57  fof(f197,plain,(
% 1.98/0.57    ( ! [X0] : (r2_hidden(sK7(sK0,sK1,X0),X0) | r4_lattice3(sK0,sK1,X0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f196,f87])).
% 1.98/0.57  fof(f196,plain,(
% 1.98/0.57    ( ! [X0] : (r2_hidden(sK7(sK0,sK1,X0),X0) | r4_lattice3(sK0,sK1,X0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(subsumption_resolution,[],[f195,f90])).
% 1.98/0.57  fof(f195,plain,(
% 1.98/0.57    ( ! [X0] : (r2_hidden(sK7(sK0,sK1,X0),X0) | r4_lattice3(sK0,sK1,X0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 1.98/0.57    inference(resolution,[],[f124,f91])).
% 1.98/0.57  fof(f124,plain,(
% 1.98/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(sK7(X0,X1,X2),X2) | r4_lattice3(X0,X1,X2) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f78])).
% 1.98/0.57  fof(f125,plain,(
% 1.98/0.57    ( ! [X2,X0,X1] : (~r1_lattices(X0,sK7(X0,X1,X2),X1) | r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f78])).
% 1.98/0.57  fof(f239,plain,(
% 1.98/0.57    ~spl10_3),
% 1.98/0.57    inference(avatar_contradiction_clause,[],[f238])).
% 1.98/0.57  fof(f238,plain,(
% 1.98/0.57    $false | ~spl10_3),
% 1.98/0.57    inference(subsumption_resolution,[],[f237,f87])).
% 1.98/0.57  fof(f237,plain,(
% 1.98/0.57    v2_struct_0(sK0) | ~spl10_3),
% 1.98/0.57    inference(subsumption_resolution,[],[f236,f175])).
% 1.98/0.57  fof(f175,plain,(
% 1.98/0.57    l1_struct_0(sK0)),
% 1.98/0.57    inference(resolution,[],[f158,f93])).
% 1.98/0.57  fof(f93,plain,(
% 1.98/0.57    ( ! [X0] : (~l2_lattices(X0) | l1_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f24])).
% 1.98/0.57  fof(f24,plain,(
% 1.98/0.57    ! [X0] : (l1_struct_0(X0) | ~l2_lattices(X0))),
% 1.98/0.57    inference(ennf_transformation,[],[f6])).
% 1.98/0.57  fof(f6,axiom,(
% 1.98/0.57    ! [X0] : (l2_lattices(X0) => l1_struct_0(X0))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l2_lattices)).
% 1.98/0.57  fof(f236,plain,(
% 1.98/0.57    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl10_3),
% 1.98/0.57    inference(resolution,[],[f186,f104])).
% 1.98/0.57  fof(f104,plain,(
% 1.98/0.57    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f33])).
% 1.98/0.57  fof(f33,plain,(
% 1.98/0.57    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.98/0.57    inference(flattening,[],[f32])).
% 1.98/0.57  fof(f32,plain,(
% 1.98/0.57    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.98/0.57    inference(ennf_transformation,[],[f2])).
% 1.98/0.57  fof(f2,axiom,(
% 1.98/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.98/0.57  fof(f186,plain,(
% 1.98/0.57    v1_xboole_0(u1_struct_0(sK0)) | ~spl10_3),
% 1.98/0.57    inference(avatar_component_clause,[],[f184])).
% 1.98/0.57  fof(f184,plain,(
% 1.98/0.57    spl10_3 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.98/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.98/0.57  fof(f191,plain,(
% 1.98/0.57    spl10_3 | spl10_4),
% 1.98/0.57    inference(avatar_split_clause,[],[f182,f188,f184])).
% 1.98/0.57  fof(f182,plain,(
% 1.98/0.57    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | v1_xboole_0(u1_struct_0(sK0))),
% 1.98/0.57    inference(resolution,[],[f130,f91])).
% 1.98/0.57  fof(f130,plain,(
% 1.98/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1) | v1_xboole_0(X0)) )),
% 1.98/0.57    inference(cnf_transformation,[],[f51])).
% 1.98/0.57  fof(f51,plain,(
% 1.98/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.98/0.57    inference(flattening,[],[f50])).
% 1.98/0.57  fof(f50,plain,(
% 1.98/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.98/0.57    inference(ennf_transformation,[],[f3])).
% 1.98/0.57  fof(f3,axiom,(
% 1.98/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.98/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.98/0.57  fof(f155,plain,(
% 1.98/0.57    ~spl10_1 | ~spl10_2),
% 1.98/0.57    inference(avatar_split_clause,[],[f92,f152,f148])).
% 1.98/0.57  fof(f92,plain,(
% 1.98/0.57    sK1 != k16_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) | sK1 != k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),sK1))),
% 1.98/0.57    inference(cnf_transformation,[],[f58])).
% 1.98/0.57  % SZS output end Proof for theBenchmark
% 1.98/0.57  % (814)------------------------------
% 1.98/0.57  % (814)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.98/0.57  % (814)Termination reason: Refutation
% 1.98/0.57  
% 1.98/0.57  % (814)Memory used [KB]: 11641
% 1.98/0.57  % (814)Time elapsed: 0.209 s
% 1.98/0.57  % (814)------------------------------
% 1.98/0.57  % (814)------------------------------
% 1.98/0.58  % (803)Success in time 0.26 s
%------------------------------------------------------------------------------
