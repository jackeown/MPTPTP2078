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
% DateTime   : Thu Dec  3 13:15:47 EST 2020

% Result     : Theorem 9.20s
% Output     : Refutation 9.32s
% Verified   : 
% Statistics : Number of formulae       :  383 (4515 expanded)
%              Number of leaves         :   35 (1120 expanded)
%              Depth                    :   51
%              Number of atoms          : 1779 (31450 expanded)
%              Number of equality atoms :  255 (3353 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21469,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1871,f1875,f2879,f4331,f14493,f18487,f21468])).

fof(f21468,plain,
    ( ~ spl12_3
    | spl12_9
    | ~ spl12_18
    | ~ spl12_33 ),
    inference(avatar_contradiction_clause,[],[f21467])).

fof(f21467,plain,
    ( $false
    | ~ spl12_3
    | spl12_9
    | ~ spl12_18
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f21458,f21357])).

fof(f21357,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | ~ spl12_3
    | ~ spl12_18
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f21356,f160])).

fof(f160,plain,(
    v6_lattices(sK7) ),
    inference(resolution,[],[f157,f94])).

fof(f94,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f157,plain,(
    sP0(sK7) ),
    inference(subsumption_resolution,[],[f156,f88])).

fof(f88,plain,(
    l3_lattices(sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,
    ( ( k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0)
      | ~ l3_lattices(sK7)
      | ~ v13_lattices(sK7)
      | ~ v10_lattices(sK7)
      | v2_struct_0(sK7) )
    & l3_lattices(sK7)
    & v4_lattice3(sK7)
    & v10_lattices(sK7)
    & ~ v2_struct_0(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f61])).

fof(f61,plain,
    ( ? [X0] :
        ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
          | ~ l3_lattices(X0)
          | ~ v13_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0)
        | ~ l3_lattices(sK7)
        | ~ v13_lattices(sK7)
        | ~ v10_lattices(sK7)
        | v2_struct_0(sK7) )
      & l3_lattices(sK7)
      & v4_lattice3(sK7)
      & v10_lattices(sK7)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ( k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0)
        | ~ l3_lattices(X0)
        | ~ v13_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
          & l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0)
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).

fof(f156,plain,
    ( sP0(sK7)
    | ~ l3_lattices(sK7) ),
    inference(subsumption_resolution,[],[f155,f85])).

fof(f85,plain,(
    ~ v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f155,plain,
    ( sP0(sK7)
    | v2_struct_0(sK7)
    | ~ l3_lattices(sK7) ),
    inference(resolution,[],[f97,f86])).

fof(f86,plain,(
    v10_lattices(sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | sP0(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(definition_folding,[],[f25,f50])).

fof(f25,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
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

fof(f21356,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | ~ v6_lattices(sK7)
    | ~ spl12_3
    | ~ spl12_18
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f21355,f159])).

fof(f159,plain,(
    v8_lattices(sK7) ),
    inference(resolution,[],[f157,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f21355,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | ~ v8_lattices(sK7)
    | ~ v6_lattices(sK7)
    | ~ spl12_3
    | ~ spl12_18
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f21354,f88])).

fof(f21354,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | ~ l3_lattices(sK7)
    | ~ v8_lattices(sK7)
    | ~ v6_lattices(sK7)
    | ~ spl12_3
    | ~ spl12_18
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f21353,f4323])).

fof(f4323,plain,
    ( m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7))
    | ~ spl12_18 ),
    inference(avatar_component_clause,[],[f4322])).

fof(f4322,plain,
    ( spl12_18
  <=> m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).

fof(f21353,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | ~ m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | ~ v8_lattices(sK7)
    | ~ v6_lattices(sK7)
    | ~ spl12_3
    | ~ spl12_18
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f21352,f85])).

fof(f21352,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | v2_struct_0(sK7)
    | ~ m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | ~ v8_lattices(sK7)
    | ~ v6_lattices(sK7)
    | ~ spl12_3
    | ~ spl12_18
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f21351,f161])).

fof(f161,plain,(
    v4_lattices(sK7) ),
    inference(resolution,[],[f157,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v4_lattices(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f21351,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | ~ v4_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | ~ v8_lattices(sK7)
    | ~ v6_lattices(sK7)
    | ~ spl12_3
    | ~ spl12_18
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f21348,f1865])).

fof(f1865,plain,
    ( m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | ~ spl12_3 ),
    inference(avatar_component_clause,[],[f1864])).

fof(f1864,plain,
    ( spl12_3
  <=> m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).

fof(f21348,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | ~ v4_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | ~ v8_lattices(sK7)
    | ~ v6_lattices(sK7)
    | ~ spl12_3
    | ~ spl12_18
    | ~ spl12_33 ),
    inference(resolution,[],[f20460,f1520])).

fof(f1520,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,k4_lattices(X1,X0,X2))
      | k4_lattices(X1,X0,X2) = X0
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v4_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1) ) ),
    inference(global_subsumption,[],[f90,f131,f1519])).

fof(f1519,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X1,X0,X2) = X0
      | ~ r1_lattices(X1,X0,k4_lattices(X1,X0,X2))
      | ~ m1_subset_1(k4_lattices(X1,X0,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v4_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f1518,f91])).

fof(f91,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f1518,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X1,X0,X2) = X0
      | ~ r1_lattices(X1,X0,k4_lattices(X1,X0,X2))
      | ~ m1_subset_1(k4_lattices(X1,X0,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l2_lattices(X1)
      | ~ v4_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f1497])).

fof(f1497,plain,(
    ! [X2,X0,X1] :
      ( k4_lattices(X1,X0,X2) = X0
      | ~ r1_lattices(X1,X0,k4_lattices(X1,X0,X2))
      | ~ m1_subset_1(k4_lattices(X1,X0,X2),u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l2_lattices(X1)
      | ~ v4_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f98,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f90,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f20460,plain,
    ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | ~ spl12_3
    | ~ spl12_18
    | ~ spl12_33 ),
    inference(superposition,[],[f20010,f14195])).

fof(f14195,plain,
    ( sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | ~ spl12_18 ),
    inference(subsumption_resolution,[],[f14194,f85])).

fof(f14194,plain,
    ( sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | v2_struct_0(sK7)
    | ~ spl12_18 ),
    inference(subsumption_resolution,[],[f14193,f86])).

fof(f14193,plain,
    ( sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_18 ),
    inference(subsumption_resolution,[],[f14192,f87])).

fof(f87,plain,(
    v4_lattice3(sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f14192,plain,
    ( sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | ~ v4_lattice3(sK7)
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_18 ),
    inference(subsumption_resolution,[],[f14165,f88])).

fof(f14165,plain,
    ( sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | ~ l3_lattices(sK7)
    | ~ v4_lattice3(sK7)
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_18 ),
    inference(resolution,[],[f4323,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f20010,plain,
    ( ! [X24] : r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X24)))
    | ~ spl12_3
    | ~ spl12_33 ),
    inference(superposition,[],[f10517,f19784])).

fof(f19784,plain,
    ( ! [X7] : k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X7)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X7))))
    | ~ spl12_3
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f19783,f85])).

fof(f19783,plain,
    ( ! [X7] :
        ( k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X7)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X7))))
        | v2_struct_0(sK7) )
    | ~ spl12_3
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f19769,f88])).

fof(f19769,plain,
    ( ! [X7] :
        ( k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X7)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X7))))
        | ~ l3_lattices(sK7)
        | v2_struct_0(sK7) )
    | ~ spl12_3
    | ~ spl12_33 ),
    inference(resolution,[],[f18719,f125])).

fof(f125,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f18719,plain,
    ( ! [X30] :
        ( ~ m1_subset_1(X30,u1_struct_0(sK7))
        | k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),X30) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),X30))) )
    | ~ spl12_3
    | ~ spl12_33 ),
    inference(backward_demodulation,[],[f18569,f18659])).

fof(f18659,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ spl12_3
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f18658,f18474])).

fof(f18474,plain,
    ( m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7))
    | ~ spl12_33 ),
    inference(avatar_component_clause,[],[f18473])).

fof(f18473,plain,
    ( spl12_33
  <=> m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_33])])).

fof(f18658,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7))
    | ~ spl12_3
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f18629,f2683])).

fof(f2683,plain,
    ( r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0))
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2682,f85])).

fof(f2682,plain,
    ( r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0))
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2681,f160])).

fof(f2681,plain,
    ( r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0))
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2680,f159])).

fof(f2680,plain,
    ( r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0))
    | ~ v8_lattices(sK7)
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2679,f88])).

fof(f2679,plain,
    ( r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0))
    | ~ l3_lattices(sK7)
    | ~ v8_lattices(sK7)
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2678,f1865])).

fof(f2678,plain,
    ( r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0))
    | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | ~ v8_lattices(sK7)
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2676,f326])).

fof(f326,plain,(
    m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) ),
    inference(subsumption_resolution,[],[f325,f85])).

fof(f325,plain,
    ( m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | v2_struct_0(sK7) ),
    inference(subsumption_resolution,[],[f321,f88])).

fof(f321,plain,
    ( m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(superposition,[],[f125,f317])).

fof(f317,plain,(
    k5_lattices(sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k5_lattices(sK7))) ),
    inference(subsumption_resolution,[],[f316,f85])).

fof(f316,plain,
    ( k5_lattices(sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k5_lattices(sK7)))
    | v2_struct_0(sK7) ),
    inference(subsumption_resolution,[],[f315,f86])).

fof(f315,plain,
    ( k5_lattices(sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k5_lattices(sK7)))
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(subsumption_resolution,[],[f314,f88])).

fof(f314,plain,
    ( ~ l3_lattices(sK7)
    | k5_lattices(sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k5_lattices(sK7)))
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(resolution,[],[f313,f87])).

fof(f313,plain,(
    ! [X1] :
      ( ~ v4_lattice3(X1)
      | ~ l3_lattices(X1)
      | k5_lattices(X1) = k15_lattice3(X1,a_2_3_lattice3(X1,k5_lattices(X1)))
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f312,f90])).

fof(f312,plain,(
    ! [X1] :
      ( k5_lattices(X1) = k15_lattice3(X1,a_2_3_lattice3(X1,k5_lattices(X1)))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l1_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f306])).

fof(f306,plain,(
    ! [X1] :
      ( k5_lattices(X1) = k15_lattice3(X1,a_2_3_lattice3(X1,k5_lattices(X1)))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l1_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f99,f106])).

fof(f106,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f2676,plain,
    ( r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0))
    | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | ~ v8_lattices(sK7)
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(superposition,[],[f105,f2529])).

fof(f2529,plain,
    ( k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2528,f85])).

fof(f2528,plain,
    ( k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2527,f160])).

fof(f2527,plain,
    ( k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2516,f137])).

fof(f137,plain,(
    l1_lattices(sK7) ),
    inference(resolution,[],[f90,f88])).

fof(f2516,plain,
    ( k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ l1_lattices(sK7)
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(resolution,[],[f1078,f1865])).

fof(f1078,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(X4))
      | k4_lattices(X4,X5,k5_lattices(X4)) = k4_lattices(X4,k5_lattices(X4),X5)
      | ~ l1_lattices(X4)
      | ~ v6_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f1066])).

fof(f1066,plain,(
    ! [X4,X5] :
      ( k4_lattices(X4,X5,k5_lattices(X4)) = k4_lattices(X4,k5_lattices(X4),X5)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_lattices(X4)
      | ~ v6_lattices(X4)
      | v2_struct_0(X4)
      | ~ l1_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f132,f106])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).

fof(f18629,plain,
    ( ~ r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0))
    | k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7))
    | ~ spl12_3
    | ~ spl12_33 ),
    inference(superposition,[],[f3608,f18542])).

fof(f18542,plain,
    ( k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))))
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f18541,f85])).

fof(f18541,plain,
    ( k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))))
    | v2_struct_0(sK7)
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f18540,f86])).

fof(f18540,plain,
    ( k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))))
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f18539,f87])).

fof(f18539,plain,
    ( k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))))
    | ~ v4_lattice3(sK7)
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f18509,f88])).

fof(f18509,plain,
    ( k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))))
    | ~ l3_lattices(sK7)
    | ~ v4_lattice3(sK7)
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_33 ),
    inference(resolution,[],[f18474,f99])).

fof(f3608,plain,
    ( ! [X1] :
        ( ~ r1_lattices(sK7,k15_lattice3(sK7,X1),k15_lattice3(sK7,k1_xboole_0))
        | k15_lattice3(sK7,k1_xboole_0) = k15_lattice3(sK7,X1)
        | ~ m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7)) )
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f3607,f85])).

fof(f3607,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7))
        | k15_lattice3(sK7,k1_xboole_0) = k15_lattice3(sK7,X1)
        | ~ r1_lattices(sK7,k15_lattice3(sK7,X1),k15_lattice3(sK7,k1_xboole_0))
        | v2_struct_0(sK7) )
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f3606,f161])).

fof(f3606,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7))
        | k15_lattice3(sK7,k1_xboole_0) = k15_lattice3(sK7,X1)
        | ~ r1_lattices(sK7,k15_lattice3(sK7,X1),k15_lattice3(sK7,k1_xboole_0))
        | ~ v4_lattices(sK7)
        | v2_struct_0(sK7) )
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f3605,f138])).

fof(f138,plain,(
    l2_lattices(sK7) ),
    inference(resolution,[],[f91,f88])).

fof(f3605,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7))
        | k15_lattice3(sK7,k1_xboole_0) = k15_lattice3(sK7,X1)
        | ~ r1_lattices(sK7,k15_lattice3(sK7,X1),k15_lattice3(sK7,k1_xboole_0))
        | ~ l2_lattices(sK7)
        | ~ v4_lattices(sK7)
        | v2_struct_0(sK7) )
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f3603,f1865])).

fof(f3603,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7))
        | k15_lattice3(sK7,k1_xboole_0) = k15_lattice3(sK7,X1)
        | ~ r1_lattices(sK7,k15_lattice3(sK7,X1),k15_lattice3(sK7,k1_xboole_0))
        | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
        | ~ l2_lattices(sK7)
        | ~ v4_lattices(sK7)
        | v2_struct_0(sK7) )
    | ~ spl12_3 ),
    inference(duplicate_literal_removal,[],[f3598])).

fof(f3598,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7))
        | k15_lattice3(sK7,k1_xboole_0) = k15_lattice3(sK7,X1)
        | ~ r1_lattices(sK7,k15_lattice3(sK7,X1),k15_lattice3(sK7,k1_xboole_0))
        | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
        | ~ m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7))
        | ~ l2_lattices(sK7)
        | ~ v4_lattices(sK7)
        | v2_struct_0(sK7) )
    | ~ spl12_3 ),
    inference(resolution,[],[f3309,f98])).

fof(f3309,plain,
    ( ! [X3] :
        ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X3))
        | ~ m1_subset_1(k15_lattice3(sK7,X3),u1_struct_0(sK7)) )
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f1826,f1865])).

fof(f1826,plain,(
    ! [X3] :
      ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X3))
      | ~ m1_subset_1(k15_lattice3(sK7,X3),u1_struct_0(sK7))
      | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) ) ),
    inference(subsumption_resolution,[],[f1825,f85])).

fof(f1825,plain,(
    ! [X3] :
      ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X3))
      | ~ m1_subset_1(k15_lattice3(sK7,X3),u1_struct_0(sK7))
      | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f1824,f160])).

fof(f1824,plain,(
    ! [X3] :
      ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X3))
      | ~ m1_subset_1(k15_lattice3(sK7,X3),u1_struct_0(sK7))
      | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
      | ~ v6_lattices(sK7)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f1823,f159])).

fof(f1823,plain,(
    ! [X3] :
      ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X3))
      | ~ m1_subset_1(k15_lattice3(sK7,X3),u1_struct_0(sK7))
      | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
      | ~ v8_lattices(sK7)
      | ~ v6_lattices(sK7)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f1822,f158])).

fof(f158,plain,(
    v9_lattices(sK7) ),
    inference(resolution,[],[f157,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1822,plain,(
    ! [X3] :
      ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X3))
      | ~ m1_subset_1(k15_lattice3(sK7,X3),u1_struct_0(sK7))
      | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
      | ~ v9_lattices(sK7)
      | ~ v8_lattices(sK7)
      | ~ v6_lattices(sK7)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f1806,f88])).

fof(f1806,plain,(
    ! [X3] :
      ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X3))
      | ~ m1_subset_1(k15_lattice3(sK7,X3),u1_struct_0(sK7))
      | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
      | ~ l3_lattices(sK7)
      | ~ v9_lattices(sK7)
      | ~ v8_lattices(sK7)
      | ~ v6_lattices(sK7)
      | v2_struct_0(sK7) ) ),
    inference(resolution,[],[f129,f489])).

fof(f489,plain,(
    ! [X0] : r3_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X0)) ),
    inference(resolution,[],[f473,f167])).

fof(f167,plain,(
    ! [X0,X1] : ~ sP1(X0,X1,k1_xboole_0) ),
    inference(resolution,[],[f102,f139])).

fof(f139,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f124,f135])).

fof(f135,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f128])).

fof(f128,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f124,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK8(X0,X1,X2),X2)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X4] :
            ( ~ r2_hidden(X4,X0)
            | ~ r3_lattices(X1,sK8(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & r2_hidden(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f65,f66])).

fof(f66,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X4,X0)
              | ~ r3_lattices(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ! [X4] :
            ( ~ r2_hidden(X4,X0)
            | ~ r3_lattices(X1,sK8(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        & r2_hidden(sK8(X0,X1,X2),X2)
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X4,X0)
              | ~ r3_lattices(X1,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X4,X2)
              | ~ r3_lattices(X0,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP1(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X4,X2)
              | ~ r3_lattices(X0,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
      | ~ sP1(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f473,plain,(
    ! [X2,X1] :
      ( sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2)
      | r3_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1)) ) ),
    inference(subsumption_resolution,[],[f472,f85])).

fof(f472,plain,(
    ! [X2,X1] :
      ( r3_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1))
      | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f471,f86])).

fof(f471,plain,(
    ! [X2,X1] :
      ( r3_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1))
      | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2)
      | ~ v10_lattices(sK7)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f470,f87])).

fof(f470,plain,(
    ! [X2,X1] :
      ( r3_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1))
      | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2)
      | ~ v4_lattice3(sK7)
      | ~ v10_lattices(sK7)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f457,f88])).

fof(f457,plain,(
    ! [X2,X1] :
      ( r3_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1))
      | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2)
      | ~ l3_lattices(sK7)
      | ~ v4_lattice3(sK7)
      | ~ v10_lattices(sK7)
      | v2_struct_0(sK7) ) ),
    inference(superposition,[],[f104,f365])).

fof(f365,plain,(
    ! [X0] : k15_lattice3(sK7,X0) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k15_lattice3(sK7,X0))) ),
    inference(subsumption_resolution,[],[f364,f85])).

fof(f364,plain,(
    ! [X0] :
      ( k15_lattice3(sK7,X0) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k15_lattice3(sK7,X0)))
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f363,f86])).

fof(f363,plain,(
    ! [X0] :
      ( k15_lattice3(sK7,X0) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k15_lattice3(sK7,X0)))
      | ~ v10_lattices(sK7)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f362,f88])).

fof(f362,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK7)
      | k15_lattice3(sK7,X0) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k15_lattice3(sK7,X0)))
      | ~ v10_lattices(sK7)
      | v2_struct_0(sK7) ) ),
    inference(resolution,[],[f311,f87])).

fof(f311,plain,(
    ! [X2,X3] :
      ( ~ v4_lattice3(X2)
      | ~ l3_lattices(X2)
      | k15_lattice3(X2,X3) = k15_lattice3(X2,a_2_3_lattice3(X2,k15_lattice3(X2,X3)))
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f307])).

fof(f307,plain,(
    ! [X2,X3] :
      ( k15_lattice3(X2,X3) = k15_lattice3(X2,a_2_3_lattice3(X2,k15_lattice3(X2,X3)))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ l3_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f99,f125])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | sP1(X2,X0,X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | sP1(X2,X0,X1) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f31,f52])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

% (10426)Time limit reached!
% (10426)------------------------------
% (10426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10426)Termination reason: Time limit

% (10426)Memory used [KB]: 11641
% (10426)Time elapsed: 1.117 s
% (10426)------------------------------
% (10426)------------------------------
fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ? [X3] :
              ( ! [X4] :
                  ( ~ r2_hidden(X4,X2)
                  | ~ r3_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f129,plain,(
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
    inference(cnf_transformation,[],[f84])).

fof(f84,plain,(
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
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f18569,plain,
    ( ! [X30] :
        ( ~ m1_subset_1(X30,u1_struct_0(sK7))
        | k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30))) )
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f18568,f86])).

fof(f18568,plain,
    ( ! [X30] :
        ( ~ m1_subset_1(X30,u1_struct_0(sK7))
        | k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30)))
        | ~ v10_lattices(sK7) )
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f18567,f87])).

fof(f18567,plain,
    ( ! [X30] :
        ( ~ m1_subset_1(X30,u1_struct_0(sK7))
        | k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30)))
        | ~ v4_lattice3(sK7)
        | ~ v10_lattices(sK7) )
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f18566,f88])).

fof(f18566,plain,
    ( ! [X30] :
        ( ~ m1_subset_1(X30,u1_struct_0(sK7))
        | k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30)))
        | ~ l3_lattices(sK7)
        | ~ v4_lattice3(sK7)
        | ~ v10_lattices(sK7) )
    | ~ spl12_33 ),
    inference(subsumption_resolution,[],[f18523,f85])).

fof(f18523,plain,
    ( ! [X30] :
        ( ~ m1_subset_1(X30,u1_struct_0(sK7))
        | v2_struct_0(sK7)
        | k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30)))
        | ~ l3_lattices(sK7)
        | ~ v4_lattice3(sK7)
        | ~ v10_lattices(sK7) )
    | ~ spl12_33 ),
    inference(resolution,[],[f18474,f589])).

fof(f589,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | k4_lattices(X1,X2,X0) = k15_lattice3(X1,a_2_3_lattice3(X1,k4_lattices(X1,X2,X0)))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1) ) ),
    inference(global_subsumption,[],[f94,f97,f588])).

fof(f588,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | k4_lattices(X1,X2,X0) = k15_lattice3(X1,a_2_3_lattice3(X1,k4_lattices(X1,X2,X0)))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f587,f90])).

fof(f587,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | k4_lattices(X1,X2,X0) = k15_lattice3(X1,a_2_3_lattice3(X1,k4_lattices(X1,X2,X0)))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f577])).

fof(f577,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | k4_lattices(X1,X2,X0) = k15_lattice3(X1,a_2_3_lattice3(X1,k4_lattices(X1,X2,X0)))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f131,f99])).

fof(f10517,plain,(
    ! [X0] : r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X0)) ),
    inference(resolution,[],[f10399,f167])).

fof(f10399,plain,(
    ! [X2,X1] :
      ( sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2)
      | r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1)) ) ),
    inference(subsumption_resolution,[],[f10398,f86])).

fof(f10398,plain,(
    ! [X2,X1] :
      ( r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1))
      | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2)
      | ~ v10_lattices(sK7) ) ),
    inference(subsumption_resolution,[],[f10397,f87])).

fof(f10397,plain,(
    ! [X2,X1] :
      ( r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1))
      | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2)
      | ~ v4_lattice3(sK7)
      | ~ v10_lattices(sK7) ) ),
    inference(subsumption_resolution,[],[f10396,f85])).

fof(f10396,plain,(
    ! [X2,X1] :
      ( r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1))
      | v2_struct_0(sK7)
      | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2)
      | ~ v4_lattice3(sK7)
      | ~ v10_lattices(sK7) ) ),
    inference(subsumption_resolution,[],[f10395,f160])).

fof(f10395,plain,(
    ! [X2,X1] :
      ( r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1))
      | ~ v6_lattices(sK7)
      | v2_struct_0(sK7)
      | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2)
      | ~ v4_lattice3(sK7)
      | ~ v10_lattices(sK7) ) ),
    inference(subsumption_resolution,[],[f10394,f159])).

fof(f10394,plain,(
    ! [X2,X1] :
      ( r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1))
      | ~ v8_lattices(sK7)
      | ~ v6_lattices(sK7)
      | v2_struct_0(sK7)
      | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2)
      | ~ v4_lattice3(sK7)
      | ~ v10_lattices(sK7) ) ),
    inference(subsumption_resolution,[],[f10393,f158])).

fof(f10393,plain,(
    ! [X2,X1] :
      ( r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1))
      | ~ v9_lattices(sK7)
      | ~ v8_lattices(sK7)
      | ~ v6_lattices(sK7)
      | v2_struct_0(sK7)
      | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2)
      | ~ v4_lattice3(sK7)
      | ~ v10_lattices(sK7) ) ),
    inference(subsumption_resolution,[],[f10287,f88])).

fof(f10287,plain,(
    ! [X2,X1] :
      ( r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1))
      | ~ l3_lattices(sK7)
      | ~ v9_lattices(sK7)
      | ~ v8_lattices(sK7)
      | ~ v6_lattices(sK7)
      | v2_struct_0(sK7)
      | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2)
      | ~ v4_lattice3(sK7)
      | ~ v10_lattices(sK7) ) ),
    inference(superposition,[],[f1815,f365])).

fof(f1815,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP1(X2,X0,X1)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f1814,f125])).

fof(f1814,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP1(X2,X0,X1)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f1813,f125])).

fof(f1813,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP1(X2,X0,X1)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f1804])).

fof(f1804,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0))
      | ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP1(X2,X0,X1)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f129,f104])).

fof(f21458,plain,
    ( k15_lattice3(sK7,k1_xboole_0) != k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | ~ spl12_3
    | spl12_9
    | ~ spl12_18
    | ~ spl12_33 ),
    inference(superposition,[],[f21442,f19044])).

fof(f19044,plain,
    ( ! [X7] : k4_lattices(sK7,k15_lattice3(sK7,X7),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,k15_lattice3(sK7,X7),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | ~ spl12_18 ),
    inference(subsumption_resolution,[],[f19043,f85])).

fof(f19043,plain,
    ( ! [X7] :
        ( k4_lattices(sK7,k15_lattice3(sK7,X7),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,k15_lattice3(sK7,X7),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
        | v2_struct_0(sK7) )
    | ~ spl12_18 ),
    inference(subsumption_resolution,[],[f19029,f88])).

fof(f19029,plain,
    ( ! [X7] :
        ( k4_lattices(sK7,k15_lattice3(sK7,X7),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,k15_lattice3(sK7,X7),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
        | ~ l3_lattices(sK7)
        | v2_struct_0(sK7) )
    | ~ spl12_18 ),
    inference(resolution,[],[f14206,f125])).

fof(f14206,plain,
    ( ! [X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK7))
        | k4_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) )
    | ~ spl12_18 ),
    inference(subsumption_resolution,[],[f14205,f85])).

fof(f14205,plain,
    ( ! [X9] :
        ( k4_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
        | ~ m1_subset_1(X9,u1_struct_0(sK7))
        | v2_struct_0(sK7) )
    | ~ spl12_18 ),
    inference(subsumption_resolution,[],[f14204,f160])).

fof(f14204,plain,
    ( ! [X9] :
        ( k4_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
        | ~ m1_subset_1(X9,u1_struct_0(sK7))
        | ~ v6_lattices(sK7)
        | v2_struct_0(sK7) )
    | ~ spl12_18 ),
    inference(subsumption_resolution,[],[f14174,f137])).

fof(f14174,plain,
    ( ! [X9] :
        ( k4_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
        | ~ m1_subset_1(X9,u1_struct_0(sK7))
        | ~ l1_lattices(sK7)
        | ~ v6_lattices(sK7)
        | v2_struct_0(sK7) )
    | ~ spl12_18 ),
    inference(resolution,[],[f4323,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f21442,plain,
    ( k15_lattice3(sK7,k1_xboole_0) != k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | ~ spl12_3
    | spl12_9
    | ~ spl12_18
    | ~ spl12_33 ),
    inference(trivial_inequality_removal,[],[f21388])).

fof(f21388,plain,
    ( k15_lattice3(sK7,k1_xboole_0) != k15_lattice3(sK7,k1_xboole_0)
    | k15_lattice3(sK7,k1_xboole_0) != k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | ~ spl12_3
    | spl12_9
    | ~ spl12_18
    | ~ spl12_33 ),
    inference(backward_demodulation,[],[f18984,f21357])).

fof(f18984,plain,
    ( k15_lattice3(sK7,k1_xboole_0) != k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | k15_lattice3(sK7,k1_xboole_0) != k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | ~ spl12_3
    | spl12_9
    | ~ spl12_18 ),
    inference(subsumption_resolution,[],[f18983,f3048])).

fof(f3048,plain,
    ( ~ sP2(k15_lattice3(sK7,k1_xboole_0),sK7)
    | spl12_9 ),
    inference(avatar_component_clause,[],[f3046])).

fof(f3046,plain,
    ( spl12_9
  <=> sP2(k15_lattice3(sK7,k1_xboole_0),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).

fof(f18983,plain,
    ( k15_lattice3(sK7,k1_xboole_0) != k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | sP2(k15_lattice3(sK7,k1_xboole_0),sK7)
    | k15_lattice3(sK7,k1_xboole_0) != k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | ~ spl12_3
    | ~ spl12_18 ),
    inference(superposition,[],[f112,f14191])).

fof(f14191,plain,
    ( k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ spl12_3
    | ~ spl12_18 ),
    inference(forward_demodulation,[],[f14160,f14159])).

fof(f14159,plain,
    ( k4_lattices(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7),k15_lattice3(sK7,k1_xboole_0)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))
    | ~ spl12_3
    | ~ spl12_18 ),
    inference(resolution,[],[f4323,f1893])).

fof(f1893,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK7))
        | k4_lattices(sK7,X4,k15_lattice3(sK7,k1_xboole_0)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),X4) )
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f1892,f85])).

fof(f1892,plain,
    ( ! [X4] :
        ( k4_lattices(sK7,X4,k15_lattice3(sK7,k1_xboole_0)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK7))
        | v2_struct_0(sK7) )
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f1891,f160])).

fof(f1891,plain,
    ( ! [X4] :
        ( k4_lattices(sK7,X4,k15_lattice3(sK7,k1_xboole_0)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK7))
        | ~ v6_lattices(sK7)
        | v2_struct_0(sK7) )
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f1888,f137])).

fof(f1888,plain,
    ( ! [X4] :
        ( k4_lattices(sK7,X4,k15_lattice3(sK7,k1_xboole_0)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK7))
        | ~ l1_lattices(sK7)
        | ~ v6_lattices(sK7)
        | v2_struct_0(sK7) )
    | ~ spl12_3 ),
    inference(resolution,[],[f1865,f132])).

fof(f14160,plain,
    ( k4_lattices(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7),k15_lattice3(sK7,k1_xboole_0)) = k2_lattices(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ spl12_3
    | ~ spl12_18 ),
    inference(resolution,[],[f4323,f1896])).

fof(f1896,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK7))
        | k4_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0)) = k2_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0)) )
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f1895,f85])).

fof(f1895,plain,
    ( ! [X5] :
        ( k4_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0)) = k2_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0))
        | ~ m1_subset_1(X5,u1_struct_0(sK7))
        | v2_struct_0(sK7) )
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f1894,f160])).

fof(f1894,plain,
    ( ! [X5] :
        ( k4_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0)) = k2_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0))
        | ~ m1_subset_1(X5,u1_struct_0(sK7))
        | ~ v6_lattices(sK7)
        | v2_struct_0(sK7) )
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f1889,f137])).

fof(f1889,plain,
    ( ! [X5] :
        ( k4_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0)) = k2_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0))
        | ~ m1_subset_1(X5,u1_struct_0(sK7))
        | ~ l1_lattices(sK7)
        | ~ v6_lattices(sK7)
        | v2_struct_0(sK7) )
    | ~ spl12_3 ),
    inference(resolution,[],[f1865,f133])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k2_lattices(X1,sK9(X0,X1),X0) != X0
      | sP2(X0,X1)
      | k2_lattices(X1,X0,sK9(X0,X1)) != X0 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ( ( k2_lattices(X1,sK9(X0,X1),X0) != X0
            | k2_lattices(X1,X0,sK9(X0,X1)) != X0 )
          & m1_subset_1(sK9(X0,X1),u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( ( k2_lattices(X1,X3,X0) = X0
              & k2_lattices(X1,X0,X3) = X0 )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f70,f71])).

fof(f71,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X1,X2,X0) != X0
            | k2_lattices(X1,X0,X2) != X0 )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ( k2_lattices(X1,sK9(X0,X1),X0) != X0
          | k2_lattices(X1,X0,sK9(X0,X1)) != X0 )
        & m1_subset_1(sK9(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( sP2(X0,X1)
        | ? [X2] :
            ( ( k2_lattices(X1,X2,X0) != X0
              | k2_lattices(X1,X0,X2) != X0 )
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( ( k2_lattices(X1,X3,X0) = X0
              & k2_lattices(X1,X0,X3) = X0 )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP2(X0,X1) ) ) ),
    inference(rectify,[],[f69])).

fof(f69,plain,(
    ! [X1,X0] :
      ( ( sP2(X1,X0)
        | ? [X2] :
            ( ( k2_lattices(X0,X2,X1) != X1
              | k2_lattices(X0,X1,X2) != X1 )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ( k2_lattices(X0,X2,X1) = X1
              & k2_lattices(X0,X1,X2) = X1 )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP2(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( sP2(X1,X0)
    <=> ! [X2] :
          ( ( k2_lattices(X0,X2,X1) = X1
            & k2_lattices(X0,X1,X2) = X1 )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f18487,plain,
    ( ~ spl12_3
    | spl12_33 ),
    inference(avatar_contradiction_clause,[],[f18486])).

fof(f18486,plain,
    ( $false
    | ~ spl12_3
    | spl12_33 ),
    inference(subsumption_resolution,[],[f18485,f85])).

fof(f18485,plain,
    ( v2_struct_0(sK7)
    | ~ spl12_3
    | spl12_33 ),
    inference(subsumption_resolution,[],[f18484,f160])).

fof(f18484,plain,
    ( ~ v6_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3
    | spl12_33 ),
    inference(subsumption_resolution,[],[f18483,f137])).

fof(f18483,plain,
    ( ~ l1_lattices(sK7)
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3
    | spl12_33 ),
    inference(subsumption_resolution,[],[f18482,f326])).

fof(f18482,plain,
    ( ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | ~ l1_lattices(sK7)
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3
    | spl12_33 ),
    inference(subsumption_resolution,[],[f18481,f1865])).

fof(f18481,plain,
    ( ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | ~ l1_lattices(sK7)
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7)
    | spl12_33 ),
    inference(resolution,[],[f18475,f131])).

fof(f18475,plain,
    ( ~ m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7))
    | spl12_33 ),
    inference(avatar_component_clause,[],[f18473])).

fof(f14493,plain,
    ( spl12_2
    | ~ spl12_3
    | ~ spl12_9 ),
    inference(avatar_contradiction_clause,[],[f14492])).

fof(f14492,plain,
    ( $false
    | spl12_2
    | ~ spl12_3
    | ~ spl12_9 ),
    inference(subsumption_resolution,[],[f14491,f13994])).

fof(f13994,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK11(k15_lattice3(sK7,k1_xboole_0),sK7))
    | spl12_2
    | ~ spl12_3
    | ~ spl12_9 ),
    inference(resolution,[],[f3047,f3739])).

fof(f3739,plain,
    ( ! [X0] :
        ( ~ sP2(X0,sK7)
        | k2_lattices(sK7,X0,sK11(k15_lattice3(sK7,k1_xboole_0),sK7)) = X0 )
    | spl12_2
    | ~ spl12_3 ),
    inference(resolution,[],[f3722,f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X1))
      | k2_lattices(X1,X0,X3) = X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f3722,plain,
    ( m1_subset_1(sK11(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7))
    | spl12_2
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f3721,f85])).

fof(f3721,plain,
    ( m1_subset_1(sK11(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7))
    | v2_struct_0(sK7)
    | spl12_2
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f3717,f88])).

fof(f3717,plain,
    ( m1_subset_1(sK11(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | spl12_2
    | ~ spl12_3 ),
    inference(superposition,[],[f125,f1905])).

fof(f1905,plain,
    ( sK11(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK11(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | spl12_2
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f1904,f85])).

fof(f1904,plain,
    ( v2_struct_0(sK7)
    | sK11(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK11(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | spl12_2
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f1903,f86])).

fof(f1903,plain,
    ( ~ v10_lattices(sK7)
    | v2_struct_0(sK7)
    | sK11(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK11(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | spl12_2
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f1902,f87])).

fof(f1902,plain,
    ( ~ v4_lattice3(sK7)
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7)
    | sK11(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK11(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | spl12_2
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f1897,f88])).

fof(f1897,plain,
    ( ~ l3_lattices(sK7)
    | ~ v4_lattice3(sK7)
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7)
    | sK11(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK11(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | spl12_2
    | ~ spl12_3 ),
    inference(resolution,[],[f1890,f309])).

fof(f309,plain,(
    ! [X6,X7] :
      ( sP4(X7,X6)
      | ~ l3_lattices(X6)
      | ~ v4_lattice3(X6)
      | ~ v10_lattices(X6)
      | v2_struct_0(X6)
      | sK11(X7,X6) = k15_lattice3(X6,a_2_3_lattice3(X6,sK11(X7,X6))) ) ),
    inference(resolution,[],[f99,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK11(X0,X1),u1_struct_0(X1))
      | sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ( ( k2_lattices(X1,sK11(X0,X1),X0) != X0
            | k2_lattices(X1,X0,sK11(X0,X1)) != X0 )
          & m1_subset_1(sK11(X0,X1),u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( ( k2_lattices(X1,X3,X0) = X0
              & k2_lattices(X1,X0,X3) = X0 )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP4(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f79,f80])).

fof(f80,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X1,X2,X0) != X0
            | k2_lattices(X1,X0,X2) != X0 )
          & m1_subset_1(X2,u1_struct_0(X1)) )
     => ( ( k2_lattices(X1,sK11(X0,X1),X0) != X0
          | k2_lattices(X1,X0,sK11(X0,X1)) != X0 )
        & m1_subset_1(sK11(X0,X1),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( sP4(X0,X1)
        | ? [X2] :
            ( ( k2_lattices(X1,X2,X0) != X0
              | k2_lattices(X1,X0,X2) != X0 )
            & m1_subset_1(X2,u1_struct_0(X1)) ) )
      & ( ! [X3] :
            ( ( k2_lattices(X1,X3,X0) = X0
              & k2_lattices(X1,X0,X3) = X0 )
            | ~ m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP4(X0,X1) ) ) ),
    inference(rectify,[],[f78])).

fof(f78,plain,(
    ! [X1,X0] :
      ( ( sP4(X1,X0)
        | ? [X2] :
            ( ( k2_lattices(X0,X2,X1) != X1
              | k2_lattices(X0,X1,X2) != X1 )
            & m1_subset_1(X2,u1_struct_0(X0)) ) )
      & ( ! [X2] :
            ( ( k2_lattices(X0,X2,X1) = X1
              & k2_lattices(X0,X1,X2) = X1 )
            | ~ m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP4(X1,X0) ) ) ),
    inference(nnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( sP4(X1,X0)
    <=> ! [X2] :
          ( ( k2_lattices(X0,X2,X1) = X1
            & k2_lattices(X0,X1,X2) = X1 )
          | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f1890,plain,
    ( ~ sP4(k15_lattice3(sK7,k1_xboole_0),sK7)
    | spl12_2
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f1885,f152])).

fof(f152,plain,
    ( ~ sP5(sK7)
    | spl12_2 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl12_2
  <=> sP5(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).

fof(f1885,plain,
    ( ~ sP4(k15_lattice3(sK7,k1_xboole_0),sK7)
    | sP5(sK7)
    | ~ spl12_3 ),
    inference(resolution,[],[f1865,f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ sP4(X1,X0)
      | sP5(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0] :
      ( ( sP5(X0)
        | ! [X1] :
            ( ~ sP4(X1,X0)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ( sP4(sK10(X0),X0)
          & m1_subset_1(sK10(X0),u1_struct_0(X0)) )
        | ~ sP5(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f75,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sP4(X2,X0)
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sP4(sK10(X0),X0)
        & m1_subset_1(sK10(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f75,plain,(
    ! [X0] :
      ( ( sP5(X0)
        | ! [X1] :
            ( ~ sP4(X1,X0)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ? [X2] :
            ( sP4(X2,X0)
            & m1_subset_1(X2,u1_struct_0(X0)) )
        | ~ sP5(X0) ) ) ),
    inference(rectify,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ( sP5(X0)
        | ! [X1] :
            ( ~ sP4(X1,X0)
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      & ( ? [X1] :
            ( sP4(X1,X0)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        | ~ sP5(X0) ) ) ),
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( sP5(X0)
    <=> ? [X1] :
          ( sP4(X1,X0)
          & m1_subset_1(X1,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f3047,plain,
    ( sP2(k15_lattice3(sK7,k1_xboole_0),sK7)
    | ~ spl12_9 ),
    inference(avatar_component_clause,[],[f3046])).

fof(f14491,plain,
    ( k15_lattice3(sK7,k1_xboole_0) != k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK11(k15_lattice3(sK7,k1_xboole_0),sK7))
    | spl12_2
    | ~ spl12_3
    | ~ spl12_9 ),
    inference(subsumption_resolution,[],[f14490,f1890])).

fof(f14490,plain,
    ( sP4(k15_lattice3(sK7,k1_xboole_0),sK7)
    | k15_lattice3(sK7,k1_xboole_0) != k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK11(k15_lattice3(sK7,k1_xboole_0),sK7))
    | spl12_2
    | ~ spl12_3
    | ~ spl12_9 ),
    inference(trivial_inequality_removal,[],[f14489])).

fof(f14489,plain,
    ( k15_lattice3(sK7,k1_xboole_0) != k15_lattice3(sK7,k1_xboole_0)
    | sP4(k15_lattice3(sK7,k1_xboole_0),sK7)
    | k15_lattice3(sK7,k1_xboole_0) != k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK11(k15_lattice3(sK7,k1_xboole_0),sK7))
    | spl12_2
    | ~ spl12_3
    | ~ spl12_9 ),
    inference(superposition,[],[f122,f13995])).

fof(f13995,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k2_lattices(sK7,sK11(k15_lattice3(sK7,k1_xboole_0),sK7),k15_lattice3(sK7,k1_xboole_0))
    | spl12_2
    | ~ spl12_3
    | ~ spl12_9 ),
    inference(resolution,[],[f3047,f3740])).

fof(f3740,plain,
    ( ! [X1] :
        ( ~ sP2(X1,sK7)
        | k2_lattices(sK7,sK11(k15_lattice3(sK7,k1_xboole_0),sK7),X1) = X1 )
    | spl12_2
    | ~ spl12_3 ),
    inference(resolution,[],[f3722,f110])).

fof(f110,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X1))
      | k2_lattices(X1,X3,X0) = X0
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f122,plain,(
    ! [X0,X1] :
      ( k2_lattices(X1,sK11(X0,X1),X0) != X0
      | sP4(X0,X1)
      | k2_lattices(X1,X0,sK11(X0,X1)) != X0 ) ),
    inference(cnf_transformation,[],[f81])).

fof(f4331,plain,
    ( spl12_9
    | spl12_18 ),
    inference(avatar_contradiction_clause,[],[f4330])).

fof(f4330,plain,
    ( $false
    | spl12_9
    | spl12_18 ),
    inference(subsumption_resolution,[],[f4324,f3839])).

fof(f3839,plain,
    ( m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7))
    | spl12_9 ),
    inference(subsumption_resolution,[],[f3838,f85])).

fof(f3838,plain,
    ( m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7))
    | v2_struct_0(sK7)
    | spl12_9 ),
    inference(subsumption_resolution,[],[f3834,f88])).

fof(f3834,plain,
    ( m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | spl12_9 ),
    inference(superposition,[],[f125,f3329])).

fof(f3329,plain,
    ( sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | spl12_9 ),
    inference(subsumption_resolution,[],[f3328,f85])).

fof(f3328,plain,
    ( v2_struct_0(sK7)
    | sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | spl12_9 ),
    inference(subsumption_resolution,[],[f3327,f86])).

fof(f3327,plain,
    ( ~ v10_lattices(sK7)
    | v2_struct_0(sK7)
    | sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | spl12_9 ),
    inference(subsumption_resolution,[],[f3326,f87])).

fof(f3326,plain,
    ( ~ v4_lattice3(sK7)
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7)
    | sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | spl12_9 ),
    inference(subsumption_resolution,[],[f3317,f88])).

fof(f3317,plain,
    ( ~ l3_lattices(sK7)
    | ~ v4_lattice3(sK7)
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7)
    | sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)))
    | spl12_9 ),
    inference(resolution,[],[f3048,f308])).

fof(f308,plain,(
    ! [X4,X5] :
      ( sP2(X5,X4)
      | ~ l3_lattices(X4)
      | ~ v4_lattice3(X4)
      | ~ v10_lattices(X4)
      | v2_struct_0(X4)
      | sK9(X5,X4) = k15_lattice3(X4,a_2_3_lattice3(X4,sK9(X5,X4))) ) ),
    inference(resolution,[],[f99,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK9(X0,X1),u1_struct_0(X1))
      | sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f4324,plain,
    ( ~ m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7))
    | spl12_18 ),
    inference(avatar_component_clause,[],[f4322])).

fof(f2879,plain,
    ( ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(avatar_contradiction_clause,[],[f2878])).

fof(f2878,plain,
    ( $false
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(global_subsumption,[],[f143,f151,f2056,f2877])).

fof(f2877,plain,
    ( k5_lattices(sK7) = k15_lattice3(sK7,k1_xboole_0)
    | ~ spl12_2
    | ~ spl12_3
    | ~ spl12_4 ),
    inference(subsumption_resolution,[],[f2876,f1870])).

fof(f1870,plain,
    ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))
    | ~ spl12_4 ),
    inference(avatar_component_clause,[],[f1868])).

fof(f1868,plain,
    ( spl12_4
  <=> r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).

fof(f2876,plain,
    ( ~ r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))
    | k5_lattices(sK7) = k15_lattice3(sK7,k1_xboole_0)
    | ~ spl12_2
    | ~ spl12_3 ),
    inference(forward_demodulation,[],[f2875,f2865])).

fof(f2865,plain,
    ( k5_lattices(sK7) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ spl12_2
    | ~ spl12_3 ),
    inference(backward_demodulation,[],[f2706,f2806])).

fof(f2806,plain,
    ( ! [X1] : k5_lattices(sK7) = k2_lattices(sK7,k15_lattice3(sK7,X1),k5_lattices(sK7))
    | ~ spl12_2 ),
    inference(backward_demodulation,[],[f2220,f2746])).

fof(f2746,plain,
    ( k5_lattices(sK7) = sK10(sK7)
    | ~ spl12_2 ),
    inference(global_subsumption,[],[f143,f151,f2745])).

fof(f2745,plain,
    ( k5_lattices(sK7) = sK10(sK7)
    | ~ v13_lattices(sK7)
    | ~ spl12_2 ),
    inference(forward_demodulation,[],[f2744,f2214])).

fof(f2214,plain,
    ( sK10(sK7) = k2_lattices(sK7,k5_lattices(sK7),sK10(sK7))
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f2213,f85])).

fof(f2213,plain,
    ( v2_struct_0(sK7)
    | sK10(sK7) = k2_lattices(sK7,k5_lattices(sK7),sK10(sK7))
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f2071,f137])).

fof(f2071,plain,
    ( ~ l1_lattices(sK7)
    | v2_struct_0(sK7)
    | sK10(sK7) = k2_lattices(sK7,k5_lattices(sK7),sK10(sK7))
    | ~ spl12_2 ),
    inference(resolution,[],[f151,f229])).

fof(f229,plain,(
    ! [X0] :
      ( ~ sP5(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | sK10(X0) = k2_lattices(X0,k5_lattices(X0),sK10(X0)) ) ),
    inference(resolution,[],[f209,f117])).

fof(f117,plain,(
    ! [X0] :
      ( sP4(sK10(X0),X0)
      | ~ sP5(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f209,plain,(
    ! [X2,X3] :
      ( ~ sP4(X3,X2)
      | k2_lattices(X2,k5_lattices(X2),X3) = X3
      | ~ l1_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f120,f106])).

fof(f120,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X1))
      | k2_lattices(X1,X3,X0) = X0
      | ~ sP4(X0,X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f2744,plain,
    ( ~ v13_lattices(sK7)
    | k5_lattices(sK7) = k2_lattices(sK7,k5_lattices(sK7),sK10(sK7))
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f2205,f137])).

fof(f2205,plain,
    ( ~ v13_lattices(sK7)
    | k5_lattices(sK7) = k2_lattices(sK7,k5_lattices(sK7),sK10(sK7))
    | ~ l1_lattices(sK7)
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f2068,f85])).

fof(f2068,plain,
    ( v2_struct_0(sK7)
    | ~ v13_lattices(sK7)
    | k5_lattices(sK7) = k2_lattices(sK7,k5_lattices(sK7),sK10(sK7))
    | ~ l1_lattices(sK7)
    | ~ spl12_2 ),
    inference(resolution,[],[f151,f198])).

fof(f198,plain,(
    ! [X1] :
      ( ~ sP5(X1)
      | v2_struct_0(X1)
      | ~ v13_lattices(X1)
      | k5_lattices(X1) = k2_lattices(X1,k5_lattices(X1),sK10(X1))
      | ~ l1_lattices(X1) ) ),
    inference(resolution,[],[f194,f172])).

fof(f172,plain,(
    ! [X0,X1] :
      ( ~ sP2(X1,X0)
      | k2_lattices(X0,X1,sK10(X0)) = X1
      | ~ sP5(X0) ) ),
    inference(resolution,[],[f109,f116])).

fof(f116,plain,(
    ! [X0] :
      ( m1_subset_1(sK10(X0),u1_struct_0(X0))
      | ~ sP5(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f194,plain,(
    ! [X0] :
      ( sP2(k5_lattices(X0),X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0)
      | ~ v13_lattices(X0) ) ),
    inference(resolution,[],[f191,f134])).

fof(f134,plain,(
    ! [X0] :
      ( ~ sP3(X0,k5_lattices(X0))
      | sP2(k5_lattices(X0),X0) ) ),
    inference(equality_resolution,[],[f107])).

fof(f107,plain,(
    ! [X0,X1] :
      ( sP2(X1,X0)
      | k5_lattices(X0) != X1
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( ( k5_lattices(X0) = X1
          | ~ sP2(X1,X0) )
        & ( sP2(X1,X0)
          | k5_lattices(X0) != X1 ) )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( k5_lattices(X0) = X1
      <=> sP2(X1,X0) )
      | ~ sP3(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f191,plain,(
    ! [X1] :
      ( sP3(X1,k5_lattices(X1))
      | ~ v13_lattices(X1)
      | ~ l1_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(duplicate_literal_removal,[],[f185])).

fof(f185,plain,(
    ! [X1] :
      ( sP3(X1,k5_lattices(X1))
      | ~ v13_lattices(X1)
      | ~ l1_lattices(X1)
      | v2_struct_0(X1)
      | ~ l1_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f113,f106])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP3(X0,X1)
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f37,f55,f54])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f2220,plain,
    ( ! [X1] : sK10(sK7) = k2_lattices(sK7,k15_lattice3(sK7,X1),sK10(sK7))
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f2219,f85])).

fof(f2219,plain,
    ( ! [X1] :
        ( v2_struct_0(sK7)
        | sK10(sK7) = k2_lattices(sK7,k15_lattice3(sK7,X1),sK10(sK7)) )
    | ~ spl12_2 ),
    inference(subsumption_resolution,[],[f2073,f88])).

fof(f2073,plain,
    ( ! [X1] :
        ( ~ l3_lattices(sK7)
        | v2_struct_0(sK7)
        | sK10(sK7) = k2_lattices(sK7,k15_lattice3(sK7,X1),sK10(sK7)) )
    | ~ spl12_2 ),
    inference(resolution,[],[f151,f239])).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ sP5(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | sK10(X0) = k2_lattices(X0,k15_lattice3(X0,X1),sK10(X0)) ) ),
    inference(resolution,[],[f210,f117])).

fof(f210,plain,(
    ! [X6,X4,X5] :
      ( ~ sP4(X6,X4)
      | k2_lattices(X4,k15_lattice3(X4,X5),X6) = X6
      | ~ l3_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f120,f125])).

fof(f2706,plain,
    ( k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ spl12_3 ),
    inference(forward_demodulation,[],[f2705,f2529])).

fof(f2705,plain,
    ( k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2704,f85])).

fof(f2704,plain,
    ( k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2703,f160])).

fof(f2703,plain,
    ( k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2692,f137])).

fof(f2692,plain,
    ( k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))
    | ~ l1_lattices(sK7)
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(resolution,[],[f1271,f1865])).

fof(f1271,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(X4))
      | k4_lattices(X4,X5,k5_lattices(X4)) = k2_lattices(X4,X5,k5_lattices(X4))
      | ~ l1_lattices(X4)
      | ~ v6_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(duplicate_literal_removal,[],[f1259])).

fof(f1259,plain,(
    ! [X4,X5] :
      ( k4_lattices(X4,X5,k5_lattices(X4)) = k2_lattices(X4,X5,k5_lattices(X4))
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ l1_lattices(X4)
      | ~ v6_lattices(X4)
      | v2_struct_0(X4)
      | ~ l1_lattices(X4)
      | v2_struct_0(X4) ) ),
    inference(resolution,[],[f133,f106])).

fof(f2875,plain,
    ( k5_lattices(sK7) = k15_lattice3(sK7,k1_xboole_0)
    | ~ r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)))
    | ~ spl12_2
    | ~ spl12_3 ),
    inference(forward_demodulation,[],[f2874,f2865])).

fof(f2874,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)))
    | ~ spl12_2
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2869,f326])).

fof(f2869,plain,
    ( ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)))
    | ~ spl12_2
    | ~ spl12_3 ),
    inference(backward_demodulation,[],[f2742,f2865])).

fof(f2742,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)))
    | ~ m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7))
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2741,f85])).

fof(f2741,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)))
    | ~ m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7))
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2740,f161])).

fof(f2740,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)))
    | ~ m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7))
    | ~ v4_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2739,f138])).

fof(f2739,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)))
    | ~ m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7))
    | ~ l2_lattices(sK7)
    | ~ v4_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(subsumption_resolution,[],[f2732,f1865])).

fof(f2732,plain,
    ( k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))
    | ~ r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)))
    | ~ m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | ~ l2_lattices(sK7)
    | ~ v4_lattices(sK7)
    | v2_struct_0(sK7)
    | ~ spl12_3 ),
    inference(resolution,[],[f2683,f98])).

fof(f2056,plain,
    ( k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0)
    | ~ v13_lattices(sK7) ),
    inference(subsumption_resolution,[],[f2055,f85])).

fof(f2055,plain,
    ( k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0)
    | ~ v13_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(subsumption_resolution,[],[f2054,f86])).

fof(f2054,plain,
    ( k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0)
    | ~ v13_lattices(sK7)
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(subsumption_resolution,[],[f89,f88])).

fof(f89,plain,
    ( k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0)
    | ~ l3_lattices(sK7)
    | ~ v13_lattices(sK7)
    | ~ v10_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f151,plain,
    ( sP5(sK7)
    | ~ spl12_2 ),
    inference(avatar_component_clause,[],[f150])).

fof(f143,plain,
    ( ~ sP5(sK7)
    | v13_lattices(sK7) ),
    inference(resolution,[],[f142,f115])).

fof(f115,plain,(
    ! [X0] :
      ( ~ sP6(X0)
      | ~ sP5(X0)
      | v13_lattices(X0) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ~ sP5(X0) )
        & ( sP5(X0)
          | ~ v13_lattices(X0) ) )
      | ~ sP6(X0) ) ),
    inference(nnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> sP5(X0) )
      | ~ sP6(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f142,plain,(
    sP6(sK7) ),
    inference(subsumption_resolution,[],[f141,f85])).

fof(f141,plain,
    ( sP6(sK7)
    | v2_struct_0(sK7) ),
    inference(resolution,[],[f123,f137])).

fof(f123,plain,(
    ! [X0] :
      ( ~ l1_lattices(X0)
      | sP6(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( sP6(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f39,f59,f58,f57])).

fof(f39,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).

fof(f1875,plain,(
    spl12_3 ),
    inference(avatar_contradiction_clause,[],[f1874])).

fof(f1874,plain,
    ( $false
    | spl12_3 ),
    inference(subsumption_resolution,[],[f1873,f85])).

fof(f1873,plain,
    ( v2_struct_0(sK7)
    | spl12_3 ),
    inference(subsumption_resolution,[],[f1872,f88])).

fof(f1872,plain,
    ( ~ l3_lattices(sK7)
    | v2_struct_0(sK7)
    | spl12_3 ),
    inference(resolution,[],[f1866,f125])).

fof(f1866,plain,
    ( ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | spl12_3 ),
    inference(avatar_component_clause,[],[f1864])).

fof(f1871,plain,
    ( ~ spl12_3
    | spl12_4 ),
    inference(avatar_split_clause,[],[f1821,f1868,f1864])).

fof(f1821,plain,
    ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) ),
    inference(subsumption_resolution,[],[f1820,f85])).

fof(f1820,plain,
    ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | v2_struct_0(sK7) ),
    inference(subsumption_resolution,[],[f1819,f160])).

fof(f1819,plain,
    ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(subsumption_resolution,[],[f1818,f159])).

fof(f1818,plain,
    ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | ~ v8_lattices(sK7)
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(subsumption_resolution,[],[f1817,f158])).

fof(f1817,plain,
    ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | ~ v9_lattices(sK7)
    | ~ v8_lattices(sK7)
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(subsumption_resolution,[],[f1816,f88])).

fof(f1816,plain,
    ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | ~ v9_lattices(sK7)
    | ~ v8_lattices(sK7)
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(subsumption_resolution,[],[f1805,f326])).

fof(f1805,plain,
    ( r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))
    | ~ m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))
    | ~ m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))
    | ~ l3_lattices(sK7)
    | ~ v9_lattices(sK7)
    | ~ v8_lattices(sK7)
    | ~ v6_lattices(sK7)
    | v2_struct_0(sK7) ),
    inference(resolution,[],[f129,f478])).

fof(f478,plain,(
    r3_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) ),
    inference(resolution,[],[f469,f167])).

fof(f469,plain,(
    ! [X0] :
      ( sP1(a_2_3_lattice3(sK7,k5_lattices(sK7)),sK7,X0)
      | r3_lattices(sK7,k15_lattice3(sK7,X0),k5_lattices(sK7)) ) ),
    inference(subsumption_resolution,[],[f468,f85])).

fof(f468,plain,(
    ! [X0] :
      ( r3_lattices(sK7,k15_lattice3(sK7,X0),k5_lattices(sK7))
      | sP1(a_2_3_lattice3(sK7,k5_lattices(sK7)),sK7,X0)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f467,f86])).

fof(f467,plain,(
    ! [X0] :
      ( r3_lattices(sK7,k15_lattice3(sK7,X0),k5_lattices(sK7))
      | sP1(a_2_3_lattice3(sK7,k5_lattices(sK7)),sK7,X0)
      | ~ v10_lattices(sK7)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f466,f87])).

fof(f466,plain,(
    ! [X0] :
      ( r3_lattices(sK7,k15_lattice3(sK7,X0),k5_lattices(sK7))
      | sP1(a_2_3_lattice3(sK7,k5_lattices(sK7)),sK7,X0)
      | ~ v4_lattice3(sK7)
      | ~ v10_lattices(sK7)
      | v2_struct_0(sK7) ) ),
    inference(subsumption_resolution,[],[f456,f88])).

fof(f456,plain,(
    ! [X0] :
      ( r3_lattices(sK7,k15_lattice3(sK7,X0),k5_lattices(sK7))
      | sP1(a_2_3_lattice3(sK7,k5_lattices(sK7)),sK7,X0)
      | ~ l3_lattices(sK7)
      | ~ v4_lattice3(sK7)
      | ~ v10_lattices(sK7)
      | v2_struct_0(sK7) ) ),
    inference(superposition,[],[f104,f317])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:14:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (10426)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (10423)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (10445)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (10422)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.50  % (10437)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (10424)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.50  % (10430)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.50  % (10429)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.50  % (10443)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.50  % (10434)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (10427)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (10433)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (10447)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (10425)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (10431)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (10428)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (10433)Refutation not found, incomplete strategy% (10433)------------------------------
% 0.21/0.51  % (10433)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10427)Refutation not found, incomplete strategy% (10427)------------------------------
% 0.21/0.51  % (10427)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10435)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (10442)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (10438)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.51  % (10439)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (10435)Refutation not found, incomplete strategy% (10435)------------------------------
% 0.21/0.51  % (10435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (10433)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10433)Memory used [KB]: 10618
% 0.21/0.51  % (10433)Time elapsed: 0.096 s
% 0.21/0.51  % (10433)------------------------------
% 0.21/0.51  % (10433)------------------------------
% 0.21/0.51  % (10427)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (10427)Memory used [KB]: 6140
% 0.21/0.51  % (10427)Time elapsed: 0.098 s
% 0.21/0.51  % (10427)------------------------------
% 0.21/0.51  % (10427)------------------------------
% 0.21/0.52  % (10435)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10435)Memory used [KB]: 6140
% 0.21/0.52  % (10435)Time elapsed: 0.111 s
% 0.21/0.52  % (10435)------------------------------
% 0.21/0.52  % (10435)------------------------------
% 0.21/0.52  % (10428)Refutation not found, incomplete strategy% (10428)------------------------------
% 0.21/0.52  % (10428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10428)Memory used [KB]: 10618
% 0.21/0.52  % (10428)Time elapsed: 0.106 s
% 0.21/0.52  % (10428)------------------------------
% 0.21/0.52  % (10428)------------------------------
% 0.21/0.52  % (10423)Refutation not found, incomplete strategy% (10423)------------------------------
% 0.21/0.52  % (10423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10423)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10423)Memory used [KB]: 10618
% 0.21/0.52  % (10423)Time elapsed: 0.107 s
% 0.21/0.52  % (10423)------------------------------
% 0.21/0.52  % (10423)------------------------------
% 0.21/0.52  % (10440)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (10441)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (10444)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.52  % (10446)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  % (10432)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (10422)Refutation not found, incomplete strategy% (10422)------------------------------
% 0.21/0.52  % (10422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (10422)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (10422)Memory used [KB]: 10618
% 0.21/0.52  % (10422)Time elapsed: 0.113 s
% 0.21/0.52  % (10422)------------------------------
% 0.21/0.52  % (10422)------------------------------
% 0.21/0.53  % (10436)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.94/0.61  % (10431)Refutation not found, incomplete strategy% (10431)------------------------------
% 1.94/0.61  % (10431)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.94/0.61  % (10431)Termination reason: Refutation not found, incomplete strategy
% 1.94/0.61  
% 1.94/0.61  % (10431)Memory used [KB]: 6140
% 1.94/0.61  % (10431)Time elapsed: 0.196 s
% 1.94/0.61  % (10431)------------------------------
% 1.94/0.61  % (10431)------------------------------
% 4.28/0.92  % (10436)Time limit reached!
% 4.28/0.92  % (10436)------------------------------
% 4.28/0.92  % (10436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/0.92  % (10436)Termination reason: Time limit
% 4.28/0.92  % (10436)Termination phase: Saturation
% 4.28/0.92  
% 4.28/0.92  % (10436)Memory used [KB]: 9338
% 4.28/0.92  % (10436)Time elapsed: 0.500 s
% 4.28/0.92  % (10436)------------------------------
% 4.28/0.92  % (10436)------------------------------
% 7.60/1.32  % (10430)Time limit reached!
% 7.60/1.32  % (10430)------------------------------
% 7.60/1.32  % (10430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.60/1.32  % (10430)Termination reason: Time limit
% 7.60/1.32  % (10430)Termination phase: Saturation
% 7.60/1.32  
% 7.60/1.32  % (10430)Memory used [KB]: 6780
% 7.60/1.32  % (10430)Time elapsed: 0.900 s
% 7.60/1.32  % (10430)------------------------------
% 7.60/1.32  % (10430)------------------------------
% 9.20/1.52  % (10447)Refutation found. Thanks to Tanya!
% 9.20/1.52  % SZS status Theorem for theBenchmark
% 9.20/1.52  % SZS output start Proof for theBenchmark
% 9.20/1.52  fof(f21469,plain,(
% 9.20/1.52    $false),
% 9.20/1.52    inference(avatar_sat_refutation,[],[f1871,f1875,f2879,f4331,f14493,f18487,f21468])).
% 9.20/1.52  fof(f21468,plain,(
% 9.20/1.52    ~spl12_3 | spl12_9 | ~spl12_18 | ~spl12_33),
% 9.20/1.52    inference(avatar_contradiction_clause,[],[f21467])).
% 9.20/1.52  fof(f21467,plain,(
% 9.20/1.52    $false | (~spl12_3 | spl12_9 | ~spl12_18 | ~spl12_33)),
% 9.20/1.52    inference(subsumption_resolution,[],[f21458,f21357])).
% 9.20/1.52  fof(f21357,plain,(
% 9.20/1.52    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | (~spl12_3 | ~spl12_18 | ~spl12_33)),
% 9.20/1.52    inference(subsumption_resolution,[],[f21356,f160])).
% 9.20/1.52  fof(f160,plain,(
% 9.20/1.52    v6_lattices(sK7)),
% 9.20/1.52    inference(resolution,[],[f157,f94])).
% 9.20/1.52  fof(f94,plain,(
% 9.20/1.52    ( ! [X0] : (~sP0(X0) | v6_lattices(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f63])).
% 9.20/1.52  fof(f63,plain,(
% 9.20/1.52    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 9.20/1.52    inference(nnf_transformation,[],[f50])).
% 9.20/1.52  fof(f50,plain,(
% 9.20/1.52    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 9.20/1.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 9.20/1.52  fof(f157,plain,(
% 9.20/1.52    sP0(sK7)),
% 9.20/1.52    inference(subsumption_resolution,[],[f156,f88])).
% 9.20/1.52  fof(f88,plain,(
% 9.20/1.52    l3_lattices(sK7)),
% 9.20/1.52    inference(cnf_transformation,[],[f62])).
% 9.20/1.52  fof(f62,plain,(
% 9.20/1.52    (k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0) | ~l3_lattices(sK7) | ~v13_lattices(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7)) & l3_lattices(sK7) & v4_lattice3(sK7) & v10_lattices(sK7) & ~v2_struct_0(sK7)),
% 9.20/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f22,f61])).
% 9.20/1.52  fof(f61,plain,(
% 9.20/1.52    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0) | ~l3_lattices(sK7) | ~v13_lattices(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7)) & l3_lattices(sK7) & v4_lattice3(sK7) & v10_lattices(sK7) & ~v2_struct_0(sK7))),
% 9.20/1.52    introduced(choice_axiom,[])).
% 9.20/1.52  fof(f22,plain,(
% 9.20/1.52    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 9.20/1.52    inference(flattening,[],[f21])).
% 9.20/1.52  fof(f21,plain,(
% 9.20/1.52    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 9.20/1.52    inference(ennf_transformation,[],[f18])).
% 9.20/1.52  fof(f18,negated_conjecture,(
% 9.20/1.52    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 9.20/1.52    inference(negated_conjecture,[],[f17])).
% 9.20/1.52  fof(f17,conjecture,(
% 9.20/1.52    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 9.20/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).
% 9.20/1.52  fof(f156,plain,(
% 9.20/1.52    sP0(sK7) | ~l3_lattices(sK7)),
% 9.20/1.52    inference(subsumption_resolution,[],[f155,f85])).
% 9.20/1.52  fof(f85,plain,(
% 9.20/1.52    ~v2_struct_0(sK7)),
% 9.20/1.52    inference(cnf_transformation,[],[f62])).
% 9.20/1.52  fof(f155,plain,(
% 9.20/1.52    sP0(sK7) | v2_struct_0(sK7) | ~l3_lattices(sK7)),
% 9.20/1.52    inference(resolution,[],[f97,f86])).
% 9.20/1.52  fof(f86,plain,(
% 9.20/1.52    v10_lattices(sK7)),
% 9.20/1.52    inference(cnf_transformation,[],[f62])).
% 9.20/1.52  fof(f97,plain,(
% 9.20/1.52    ( ! [X0] : (~v10_lattices(X0) | sP0(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f51])).
% 9.20/1.52  fof(f51,plain,(
% 9.20/1.52    ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 9.20/1.52    inference(definition_folding,[],[f25,f50])).
% 9.20/1.52  fof(f25,plain,(
% 9.20/1.52    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 9.20/1.52    inference(flattening,[],[f24])).
% 9.20/1.52  fof(f24,plain,(
% 9.20/1.52    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 9.20/1.52    inference(ennf_transformation,[],[f20])).
% 9.20/1.52  fof(f20,plain,(
% 9.20/1.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 9.20/1.52    inference(pure_predicate_removal,[],[f19])).
% 9.20/1.52  fof(f19,plain,(
% 9.20/1.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 9.20/1.52    inference(pure_predicate_removal,[],[f3])).
% 9.20/1.52  fof(f3,axiom,(
% 9.20/1.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 9.20/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 9.20/1.52  fof(f21356,plain,(
% 9.20/1.52    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | ~v6_lattices(sK7) | (~spl12_3 | ~spl12_18 | ~spl12_33)),
% 9.20/1.52    inference(subsumption_resolution,[],[f21355,f159])).
% 9.20/1.52  fof(f159,plain,(
% 9.20/1.52    v8_lattices(sK7)),
% 9.20/1.52    inference(resolution,[],[f157,f95])).
% 9.20/1.52  fof(f95,plain,(
% 9.20/1.52    ( ! [X0] : (~sP0(X0) | v8_lattices(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f63])).
% 9.20/1.52  fof(f21355,plain,(
% 9.20/1.52    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | (~spl12_3 | ~spl12_18 | ~spl12_33)),
% 9.20/1.52    inference(subsumption_resolution,[],[f21354,f88])).
% 9.20/1.52  fof(f21354,plain,(
% 9.20/1.52    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | ~l3_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | (~spl12_3 | ~spl12_18 | ~spl12_33)),
% 9.20/1.52    inference(subsumption_resolution,[],[f21353,f4323])).
% 9.20/1.52  fof(f4323,plain,(
% 9.20/1.52    m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7)) | ~spl12_18),
% 9.20/1.52    inference(avatar_component_clause,[],[f4322])).
% 9.20/1.52  fof(f4322,plain,(
% 9.20/1.52    spl12_18 <=> m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7))),
% 9.20/1.52    introduced(avatar_definition,[new_symbols(naming,[spl12_18])])).
% 9.20/1.52  fof(f21353,plain,(
% 9.20/1.52    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | ~m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7)) | ~l3_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | (~spl12_3 | ~spl12_18 | ~spl12_33)),
% 9.20/1.52    inference(subsumption_resolution,[],[f21352,f85])).
% 9.20/1.52  fof(f21352,plain,(
% 9.20/1.52    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | v2_struct_0(sK7) | ~m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7)) | ~l3_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | (~spl12_3 | ~spl12_18 | ~spl12_33)),
% 9.20/1.52    inference(subsumption_resolution,[],[f21351,f161])).
% 9.20/1.52  fof(f161,plain,(
% 9.20/1.52    v4_lattices(sK7)),
% 9.20/1.52    inference(resolution,[],[f157,f93])).
% 9.20/1.52  fof(f93,plain,(
% 9.20/1.52    ( ! [X0] : (~sP0(X0) | v4_lattices(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f63])).
% 9.20/1.52  fof(f21351,plain,(
% 9.20/1.52    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | ~v4_lattices(sK7) | v2_struct_0(sK7) | ~m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7)) | ~l3_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | (~spl12_3 | ~spl12_18 | ~spl12_33)),
% 9.20/1.52    inference(subsumption_resolution,[],[f21348,f1865])).
% 9.20/1.52  fof(f1865,plain,(
% 9.20/1.52    m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~spl12_3),
% 9.20/1.52    inference(avatar_component_clause,[],[f1864])).
% 9.20/1.52  fof(f1864,plain,(
% 9.20/1.52    spl12_3 <=> m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))),
% 9.20/1.52    introduced(avatar_definition,[new_symbols(naming,[spl12_3])])).
% 9.20/1.52  fof(f21348,plain,(
% 9.20/1.52    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~v4_lattices(sK7) | v2_struct_0(sK7) | ~m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7)) | ~l3_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | (~spl12_3 | ~spl12_18 | ~spl12_33)),
% 9.20/1.52    inference(resolution,[],[f20460,f1520])).
% 9.20/1.52  fof(f1520,plain,(
% 9.20/1.52    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,k4_lattices(X1,X0,X2)) | k4_lattices(X1,X0,X2) = X0 | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v4_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1)) )),
% 9.20/1.52    inference(global_subsumption,[],[f90,f131,f1519])).
% 9.20/1.52  fof(f1519,plain,(
% 9.20/1.52    ( ! [X2,X0,X1] : (k4_lattices(X1,X0,X2) = X0 | ~r1_lattices(X1,X0,k4_lattices(X1,X0,X2)) | ~m1_subset_1(k4_lattices(X1,X0,X2),u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v4_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1)) )),
% 9.20/1.52    inference(subsumption_resolution,[],[f1518,f91])).
% 9.20/1.52  fof(f91,plain,(
% 9.20/1.52    ( ! [X0] : (~l3_lattices(X0) | l2_lattices(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f23])).
% 9.20/1.52  fof(f23,plain,(
% 9.20/1.52    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 9.20/1.52    inference(ennf_transformation,[],[f8])).
% 9.20/1.52  fof(f8,axiom,(
% 9.20/1.52    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 9.20/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 9.20/1.52  fof(f1518,plain,(
% 9.20/1.52    ( ! [X2,X0,X1] : (k4_lattices(X1,X0,X2) = X0 | ~r1_lattices(X1,X0,k4_lattices(X1,X0,X2)) | ~m1_subset_1(k4_lattices(X1,X0,X2),u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l2_lattices(X1) | ~v4_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1)) )),
% 9.20/1.52    inference(duplicate_literal_removal,[],[f1497])).
% 9.20/1.52  fof(f1497,plain,(
% 9.20/1.52    ( ! [X2,X0,X1] : (k4_lattices(X1,X0,X2) = X0 | ~r1_lattices(X1,X0,k4_lattices(X1,X0,X2)) | ~m1_subset_1(k4_lattices(X1,X0,X2),u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l2_lattices(X1) | ~v4_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1)) )),
% 9.20/1.52    inference(resolution,[],[f98,f105])).
% 9.20/1.52  fof(f105,plain,(
% 9.20/1.52    ( ! [X2,X0,X1] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f33])).
% 9.20/1.52  fof(f33,plain,(
% 9.20/1.52    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 9.20/1.52    inference(flattening,[],[f32])).
% 9.20/1.52  fof(f32,plain,(
% 9.20/1.52    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 9.20/1.52    inference(ennf_transformation,[],[f11])).
% 9.20/1.52  fof(f11,axiom,(
% 9.20/1.52    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 9.20/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).
% 9.20/1.52  fof(f98,plain,(
% 9.20/1.52    ( ! [X2,X0,X1] : (~r1_lattices(X0,X2,X1) | X1 = X2 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f27])).
% 9.20/1.52  fof(f27,plain,(
% 9.20/1.52    ! [X0] : (! [X1] : (! [X2] : (X1 = X2 | ~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 9.20/1.52    inference(flattening,[],[f26])).
% 9.20/1.52  fof(f26,plain,(
% 9.20/1.52    ! [X0] : (! [X1] : (! [X2] : ((X1 = X2 | (~r1_lattices(X0,X2,X1) | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 9.20/1.52    inference(ennf_transformation,[],[f12])).
% 9.20/1.52  fof(f12,axiom,(
% 9.20/1.52    ! [X0] : ((l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r1_lattices(X0,X2,X1) & r1_lattices(X0,X1,X2)) => X1 = X2))))),
% 9.20/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_lattices)).
% 9.20/1.52  fof(f131,plain,(
% 9.20/1.52    ( ! [X2,X0,X1] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f45])).
% 9.20/1.52  fof(f45,plain,(
% 9.20/1.52    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 9.20/1.52    inference(flattening,[],[f44])).
% 9.20/1.52  fof(f44,plain,(
% 9.20/1.52    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 9.20/1.52    inference(ennf_transformation,[],[f6])).
% 9.20/1.52  fof(f6,axiom,(
% 9.20/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 9.20/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).
% 9.20/1.52  fof(f90,plain,(
% 9.20/1.52    ( ! [X0] : (~l3_lattices(X0) | l1_lattices(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f23])).
% 9.20/1.52  fof(f20460,plain,(
% 9.20/1.52    r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))) | (~spl12_3 | ~spl12_18 | ~spl12_33)),
% 9.20/1.52    inference(superposition,[],[f20010,f14195])).
% 9.20/1.52  fof(f14195,plain,(
% 9.20/1.52    sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7))) | ~spl12_18),
% 9.20/1.52    inference(subsumption_resolution,[],[f14194,f85])).
% 9.20/1.52  fof(f14194,plain,(
% 9.20/1.52    sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7))) | v2_struct_0(sK7) | ~spl12_18),
% 9.20/1.52    inference(subsumption_resolution,[],[f14193,f86])).
% 9.20/1.52  fof(f14193,plain,(
% 9.20/1.52    sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7))) | ~v10_lattices(sK7) | v2_struct_0(sK7) | ~spl12_18),
% 9.20/1.52    inference(subsumption_resolution,[],[f14192,f87])).
% 9.20/1.52  fof(f87,plain,(
% 9.20/1.52    v4_lattice3(sK7)),
% 9.20/1.52    inference(cnf_transformation,[],[f62])).
% 9.20/1.52  fof(f14192,plain,(
% 9.20/1.52    sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7))) | ~v4_lattice3(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7) | ~spl12_18),
% 9.20/1.52    inference(subsumption_resolution,[],[f14165,f88])).
% 9.20/1.52  fof(f14165,plain,(
% 9.20/1.52    sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7))) | ~l3_lattices(sK7) | ~v4_lattice3(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7) | ~spl12_18),
% 9.20/1.52    inference(resolution,[],[f4323,f99])).
% 9.20/1.52  fof(f99,plain,(
% 9.20/1.52    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f29])).
% 9.20/1.52  fof(f29,plain,(
% 9.20/1.52    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 9.20/1.52    inference(flattening,[],[f28])).
% 9.20/1.52  fof(f28,plain,(
% 9.20/1.52    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 9.20/1.52    inference(ennf_transformation,[],[f15])).
% 9.20/1.52  fof(f15,axiom,(
% 9.20/1.52    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 9.20/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_lattice3)).
% 9.20/1.52  fof(f20010,plain,(
% 9.20/1.52    ( ! [X24] : (r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X24)))) ) | (~spl12_3 | ~spl12_33)),
% 9.20/1.52    inference(superposition,[],[f10517,f19784])).
% 9.20/1.52  fof(f19784,plain,(
% 9.20/1.52    ( ! [X7] : (k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X7)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X7))))) ) | (~spl12_3 | ~spl12_33)),
% 9.20/1.52    inference(subsumption_resolution,[],[f19783,f85])).
% 9.20/1.52  fof(f19783,plain,(
% 9.20/1.52    ( ! [X7] : (k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X7)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X7)))) | v2_struct_0(sK7)) ) | (~spl12_3 | ~spl12_33)),
% 9.20/1.52    inference(subsumption_resolution,[],[f19769,f88])).
% 9.20/1.52  fof(f19769,plain,(
% 9.20/1.52    ( ! [X7] : (k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X7)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X7)))) | ~l3_lattices(sK7) | v2_struct_0(sK7)) ) | (~spl12_3 | ~spl12_33)),
% 9.20/1.52    inference(resolution,[],[f18719,f125])).
% 9.20/1.52  fof(f125,plain,(
% 9.20/1.52    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f41])).
% 9.20/1.52  fof(f41,plain,(
% 9.20/1.52    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 9.20/1.52    inference(flattening,[],[f40])).
% 9.20/1.52  fof(f40,plain,(
% 9.20/1.52    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 9.20/1.52    inference(ennf_transformation,[],[f14])).
% 9.20/1.52  fof(f14,axiom,(
% 9.20/1.52    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 9.20/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 9.20/1.52  fof(f18719,plain,(
% 9.20/1.52    ( ! [X30] : (~m1_subset_1(X30,u1_struct_0(sK7)) | k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),X30) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),X30)))) ) | (~spl12_3 | ~spl12_33)),
% 9.20/1.52    inference(backward_demodulation,[],[f18569,f18659])).
% 9.20/1.52  fof(f18659,plain,(
% 9.20/1.52    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | (~spl12_3 | ~spl12_33)),
% 9.20/1.52    inference(subsumption_resolution,[],[f18658,f18474])).
% 9.20/1.52  fof(f18474,plain,(
% 9.20/1.52    m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7)) | ~spl12_33),
% 9.20/1.52    inference(avatar_component_clause,[],[f18473])).
% 9.20/1.52  fof(f18473,plain,(
% 9.20/1.52    spl12_33 <=> m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7))),
% 9.20/1.52    introduced(avatar_definition,[new_symbols(naming,[spl12_33])])).
% 9.20/1.52  fof(f18658,plain,(
% 9.20/1.52    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | ~m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7)) | (~spl12_3 | ~spl12_33)),
% 9.20/1.52    inference(subsumption_resolution,[],[f18629,f2683])).
% 9.20/1.52  fof(f2683,plain,(
% 9.20/1.52    r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0)) | ~spl12_3),
% 9.20/1.52    inference(subsumption_resolution,[],[f2682,f85])).
% 9.20/1.52  fof(f2682,plain,(
% 9.20/1.52    r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0)) | v2_struct_0(sK7) | ~spl12_3),
% 9.20/1.52    inference(subsumption_resolution,[],[f2681,f160])).
% 9.20/1.52  fof(f2681,plain,(
% 9.20/1.52    r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0)) | ~v6_lattices(sK7) | v2_struct_0(sK7) | ~spl12_3),
% 9.20/1.52    inference(subsumption_resolution,[],[f2680,f159])).
% 9.20/1.52  fof(f2680,plain,(
% 9.20/1.52    r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0)) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7) | ~spl12_3),
% 9.20/1.52    inference(subsumption_resolution,[],[f2679,f88])).
% 9.20/1.52  fof(f2679,plain,(
% 9.20/1.52    r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0)) | ~l3_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7) | ~spl12_3),
% 9.20/1.52    inference(subsumption_resolution,[],[f2678,f1865])).
% 9.20/1.52  fof(f2678,plain,(
% 9.20/1.52    r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~l3_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7) | ~spl12_3),
% 9.20/1.52    inference(subsumption_resolution,[],[f2676,f326])).
% 9.20/1.52  fof(f326,plain,(
% 9.20/1.52    m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7))),
% 9.20/1.52    inference(subsumption_resolution,[],[f325,f85])).
% 9.20/1.52  fof(f325,plain,(
% 9.20/1.52    m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) | v2_struct_0(sK7)),
% 9.20/1.52    inference(subsumption_resolution,[],[f321,f88])).
% 9.20/1.52  fof(f321,plain,(
% 9.20/1.52    m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) | ~l3_lattices(sK7) | v2_struct_0(sK7)),
% 9.20/1.52    inference(superposition,[],[f125,f317])).
% 9.20/1.52  fof(f317,plain,(
% 9.20/1.52    k5_lattices(sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k5_lattices(sK7)))),
% 9.20/1.52    inference(subsumption_resolution,[],[f316,f85])).
% 9.20/1.52  fof(f316,plain,(
% 9.20/1.52    k5_lattices(sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k5_lattices(sK7))) | v2_struct_0(sK7)),
% 9.20/1.52    inference(subsumption_resolution,[],[f315,f86])).
% 9.20/1.52  fof(f315,plain,(
% 9.20/1.52    k5_lattices(sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k5_lattices(sK7))) | ~v10_lattices(sK7) | v2_struct_0(sK7)),
% 9.20/1.52    inference(subsumption_resolution,[],[f314,f88])).
% 9.20/1.52  fof(f314,plain,(
% 9.20/1.52    ~l3_lattices(sK7) | k5_lattices(sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k5_lattices(sK7))) | ~v10_lattices(sK7) | v2_struct_0(sK7)),
% 9.20/1.52    inference(resolution,[],[f313,f87])).
% 9.20/1.52  fof(f313,plain,(
% 9.20/1.52    ( ! [X1] : (~v4_lattice3(X1) | ~l3_lattices(X1) | k5_lattices(X1) = k15_lattice3(X1,a_2_3_lattice3(X1,k5_lattices(X1))) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 9.20/1.52    inference(subsumption_resolution,[],[f312,f90])).
% 9.20/1.52  fof(f312,plain,(
% 9.20/1.52    ( ! [X1] : (k5_lattices(X1) = k15_lattice3(X1,a_2_3_lattice3(X1,k5_lattices(X1))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l1_lattices(X1)) )),
% 9.20/1.52    inference(duplicate_literal_removal,[],[f306])).
% 9.20/1.52  fof(f306,plain,(
% 9.20/1.52    ( ! [X1] : (k5_lattices(X1) = k15_lattice3(X1,a_2_3_lattice3(X1,k5_lattices(X1))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l1_lattices(X1) | v2_struct_0(X1)) )),
% 9.20/1.52    inference(resolution,[],[f99,f106])).
% 9.20/1.52  fof(f106,plain,(
% 9.20/1.52    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f35])).
% 9.20/1.52  fof(f35,plain,(
% 9.20/1.52    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 9.20/1.52    inference(flattening,[],[f34])).
% 9.20/1.52  fof(f34,plain,(
% 9.20/1.52    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 9.20/1.52    inference(ennf_transformation,[],[f7])).
% 9.20/1.52  fof(f7,axiom,(
% 9.20/1.52    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 9.20/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 9.20/1.52  fof(f2676,plain,(
% 9.20/1.52    r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0)) | ~m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~l3_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7) | ~spl12_3),
% 9.20/1.52    inference(superposition,[],[f105,f2529])).
% 9.20/1.52  fof(f2529,plain,(
% 9.20/1.52    k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | ~spl12_3),
% 9.20/1.52    inference(subsumption_resolution,[],[f2528,f85])).
% 9.20/1.52  fof(f2528,plain,(
% 9.20/1.52    k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | v2_struct_0(sK7) | ~spl12_3),
% 9.20/1.52    inference(subsumption_resolution,[],[f2527,f160])).
% 9.20/1.52  fof(f2527,plain,(
% 9.20/1.52    k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | ~v6_lattices(sK7) | v2_struct_0(sK7) | ~spl12_3),
% 9.20/1.52    inference(subsumption_resolution,[],[f2516,f137])).
% 9.20/1.52  fof(f137,plain,(
% 9.20/1.52    l1_lattices(sK7)),
% 9.20/1.52    inference(resolution,[],[f90,f88])).
% 9.20/1.52  fof(f2516,plain,(
% 9.20/1.52    k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | ~l1_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7) | ~spl12_3),
% 9.20/1.52    inference(resolution,[],[f1078,f1865])).
% 9.20/1.52  fof(f1078,plain,(
% 9.20/1.52    ( ! [X4,X5] : (~m1_subset_1(X5,u1_struct_0(X4)) | k4_lattices(X4,X5,k5_lattices(X4)) = k4_lattices(X4,k5_lattices(X4),X5) | ~l1_lattices(X4) | ~v6_lattices(X4) | v2_struct_0(X4)) )),
% 9.20/1.52    inference(duplicate_literal_removal,[],[f1066])).
% 9.20/1.52  fof(f1066,plain,(
% 9.20/1.52    ( ! [X4,X5] : (k4_lattices(X4,X5,k5_lattices(X4)) = k4_lattices(X4,k5_lattices(X4),X5) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_lattices(X4) | ~v6_lattices(X4) | v2_struct_0(X4) | ~l1_lattices(X4) | v2_struct_0(X4)) )),
% 9.20/1.52    inference(resolution,[],[f132,f106])).
% 9.20/1.52  fof(f132,plain,(
% 9.20/1.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f47])).
% 9.20/1.52  fof(f47,plain,(
% 9.20/1.52    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 9.20/1.52    inference(flattening,[],[f46])).
% 9.20/1.52  fof(f46,plain,(
% 9.20/1.52    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 9.20/1.52    inference(ennf_transformation,[],[f4])).
% 9.20/1.52  fof(f4,axiom,(
% 9.20/1.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k4_lattices(X0,X2,X1))),
% 9.20/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k4_lattices)).
% 9.20/1.52  fof(f18629,plain,(
% 9.20/1.52    ~r1_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),k15_lattice3(sK7,k1_xboole_0)) | k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | ~m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7)) | (~spl12_3 | ~spl12_33)),
% 9.20/1.52    inference(superposition,[],[f3608,f18542])).
% 9.20/1.52  fof(f18542,plain,(
% 9.20/1.52    k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)))) | ~spl12_33),
% 9.20/1.52    inference(subsumption_resolution,[],[f18541,f85])).
% 9.20/1.52  fof(f18541,plain,(
% 9.20/1.52    k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)))) | v2_struct_0(sK7) | ~spl12_33),
% 9.20/1.52    inference(subsumption_resolution,[],[f18540,f86])).
% 9.20/1.52  fof(f18540,plain,(
% 9.20/1.52    k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)))) | ~v10_lattices(sK7) | v2_struct_0(sK7) | ~spl12_33),
% 9.20/1.52    inference(subsumption_resolution,[],[f18539,f87])).
% 9.20/1.52  fof(f18539,plain,(
% 9.20/1.52    k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)))) | ~v4_lattice3(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7) | ~spl12_33),
% 9.20/1.52    inference(subsumption_resolution,[],[f18509,f88])).
% 9.20/1.52  fof(f18509,plain,(
% 9.20/1.52    k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)))) | ~l3_lattices(sK7) | ~v4_lattice3(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7) | ~spl12_33),
% 9.20/1.52    inference(resolution,[],[f18474,f99])).
% 9.20/1.52  fof(f3608,plain,(
% 9.20/1.52    ( ! [X1] : (~r1_lattices(sK7,k15_lattice3(sK7,X1),k15_lattice3(sK7,k1_xboole_0)) | k15_lattice3(sK7,k1_xboole_0) = k15_lattice3(sK7,X1) | ~m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7))) ) | ~spl12_3),
% 9.20/1.52    inference(subsumption_resolution,[],[f3607,f85])).
% 9.20/1.52  fof(f3607,plain,(
% 9.20/1.52    ( ! [X1] : (~m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7)) | k15_lattice3(sK7,k1_xboole_0) = k15_lattice3(sK7,X1) | ~r1_lattices(sK7,k15_lattice3(sK7,X1),k15_lattice3(sK7,k1_xboole_0)) | v2_struct_0(sK7)) ) | ~spl12_3),
% 9.20/1.52    inference(subsumption_resolution,[],[f3606,f161])).
% 9.20/1.52  fof(f3606,plain,(
% 9.20/1.52    ( ! [X1] : (~m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7)) | k15_lattice3(sK7,k1_xboole_0) = k15_lattice3(sK7,X1) | ~r1_lattices(sK7,k15_lattice3(sK7,X1),k15_lattice3(sK7,k1_xboole_0)) | ~v4_lattices(sK7) | v2_struct_0(sK7)) ) | ~spl12_3),
% 9.20/1.52    inference(subsumption_resolution,[],[f3605,f138])).
% 9.20/1.52  fof(f138,plain,(
% 9.20/1.52    l2_lattices(sK7)),
% 9.20/1.52    inference(resolution,[],[f91,f88])).
% 9.20/1.52  fof(f3605,plain,(
% 9.20/1.52    ( ! [X1] : (~m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7)) | k15_lattice3(sK7,k1_xboole_0) = k15_lattice3(sK7,X1) | ~r1_lattices(sK7,k15_lattice3(sK7,X1),k15_lattice3(sK7,k1_xboole_0)) | ~l2_lattices(sK7) | ~v4_lattices(sK7) | v2_struct_0(sK7)) ) | ~spl12_3),
% 9.20/1.52    inference(subsumption_resolution,[],[f3603,f1865])).
% 9.20/1.52  fof(f3603,plain,(
% 9.20/1.52    ( ! [X1] : (~m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7)) | k15_lattice3(sK7,k1_xboole_0) = k15_lattice3(sK7,X1) | ~r1_lattices(sK7,k15_lattice3(sK7,X1),k15_lattice3(sK7,k1_xboole_0)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~l2_lattices(sK7) | ~v4_lattices(sK7) | v2_struct_0(sK7)) ) | ~spl12_3),
% 9.20/1.52    inference(duplicate_literal_removal,[],[f3598])).
% 9.20/1.52  fof(f3598,plain,(
% 9.20/1.52    ( ! [X1] : (~m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7)) | k15_lattice3(sK7,k1_xboole_0) = k15_lattice3(sK7,X1) | ~r1_lattices(sK7,k15_lattice3(sK7,X1),k15_lattice3(sK7,k1_xboole_0)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~m1_subset_1(k15_lattice3(sK7,X1),u1_struct_0(sK7)) | ~l2_lattices(sK7) | ~v4_lattices(sK7) | v2_struct_0(sK7)) ) | ~spl12_3),
% 9.20/1.52    inference(resolution,[],[f3309,f98])).
% 9.20/1.52  fof(f3309,plain,(
% 9.20/1.52    ( ! [X3] : (r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X3)) | ~m1_subset_1(k15_lattice3(sK7,X3),u1_struct_0(sK7))) ) | ~spl12_3),
% 9.20/1.52    inference(subsumption_resolution,[],[f1826,f1865])).
% 9.20/1.52  fof(f1826,plain,(
% 9.20/1.52    ( ! [X3] : (r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X3)) | ~m1_subset_1(k15_lattice3(sK7,X3),u1_struct_0(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))) )),
% 9.20/1.52    inference(subsumption_resolution,[],[f1825,f85])).
% 9.20/1.52  fof(f1825,plain,(
% 9.20/1.52    ( ! [X3] : (r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X3)) | ~m1_subset_1(k15_lattice3(sK7,X3),u1_struct_0(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | v2_struct_0(sK7)) )),
% 9.20/1.52    inference(subsumption_resolution,[],[f1824,f160])).
% 9.20/1.52  fof(f1824,plain,(
% 9.20/1.52    ( ! [X3] : (r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X3)) | ~m1_subset_1(k15_lattice3(sK7,X3),u1_struct_0(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~v6_lattices(sK7) | v2_struct_0(sK7)) )),
% 9.20/1.52    inference(subsumption_resolution,[],[f1823,f159])).
% 9.20/1.52  fof(f1823,plain,(
% 9.20/1.52    ( ! [X3] : (r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X3)) | ~m1_subset_1(k15_lattice3(sK7,X3),u1_struct_0(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7)) )),
% 9.20/1.52    inference(subsumption_resolution,[],[f1822,f158])).
% 9.20/1.52  fof(f158,plain,(
% 9.20/1.52    v9_lattices(sK7)),
% 9.20/1.52    inference(resolution,[],[f157,f96])).
% 9.20/1.52  fof(f96,plain,(
% 9.20/1.52    ( ! [X0] : (~sP0(X0) | v9_lattices(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f63])).
% 9.20/1.52  fof(f1822,plain,(
% 9.20/1.52    ( ! [X3] : (r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X3)) | ~m1_subset_1(k15_lattice3(sK7,X3),u1_struct_0(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~v9_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7)) )),
% 9.20/1.52    inference(subsumption_resolution,[],[f1806,f88])).
% 9.20/1.52  fof(f1806,plain,(
% 9.20/1.52    ( ! [X3] : (r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X3)) | ~m1_subset_1(k15_lattice3(sK7,X3),u1_struct_0(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~l3_lattices(sK7) | ~v9_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7)) )),
% 9.20/1.52    inference(resolution,[],[f129,f489])).
% 9.20/1.52  fof(f489,plain,(
% 9.20/1.52    ( ! [X0] : (r3_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X0))) )),
% 9.20/1.52    inference(resolution,[],[f473,f167])).
% 9.20/1.52  fof(f167,plain,(
% 9.20/1.52    ( ! [X0,X1] : (~sP1(X0,X1,k1_xboole_0)) )),
% 9.20/1.52    inference(resolution,[],[f102,f139])).
% 9.20/1.52  fof(f139,plain,(
% 9.20/1.52    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 9.20/1.52    inference(superposition,[],[f124,f135])).
% 9.20/1.52  fof(f135,plain,(
% 9.20/1.52    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 9.20/1.52    inference(equality_resolution,[],[f128])).
% 9.20/1.52  fof(f128,plain,(
% 9.20/1.52    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 9.20/1.52    inference(cnf_transformation,[],[f83])).
% 9.20/1.52  fof(f83,plain,(
% 9.20/1.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 9.20/1.52    inference(flattening,[],[f82])).
% 9.20/1.52  fof(f82,plain,(
% 9.20/1.52    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 9.20/1.52    inference(nnf_transformation,[],[f1])).
% 9.20/1.52  fof(f1,axiom,(
% 9.20/1.52    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 9.20/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 9.20/1.52  fof(f124,plain,(
% 9.20/1.52    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 9.20/1.52    inference(cnf_transformation,[],[f2])).
% 9.20/1.52  fof(f2,axiom,(
% 9.20/1.52    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 9.20/1.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 9.20/1.52  fof(f102,plain,(
% 9.20/1.52    ( ! [X2,X0,X1] : (r2_hidden(sK8(X0,X1,X2),X2) | ~sP1(X0,X1,X2)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f67])).
% 9.20/1.52  fof(f67,plain,(
% 9.20/1.52    ! [X0,X1,X2] : ((! [X4] : (~r2_hidden(X4,X0) | ~r3_lattices(X1,sK8(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & r2_hidden(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))) | ~sP1(X0,X1,X2))),
% 9.20/1.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f65,f66])).
% 9.20/1.52  fof(f66,plain,(
% 9.20/1.52    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X0) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (! [X4] : (~r2_hidden(X4,X0) | ~r3_lattices(X1,sK8(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & r2_hidden(sK8(X0,X1,X2),X2) & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1))))),
% 9.20/1.52    introduced(choice_axiom,[])).
% 9.20/1.52  fof(f65,plain,(
% 9.20/1.52    ! [X0,X1,X2] : (? [X3] : (! [X4] : (~r2_hidden(X4,X0) | ~r3_lattices(X1,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X1))) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) | ~sP1(X0,X1,X2))),
% 9.20/1.52    inference(rectify,[],[f64])).
% 9.20/1.52  fof(f64,plain,(
% 9.20/1.52    ! [X2,X0,X1] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~sP1(X2,X0,X1))),
% 9.20/1.52    inference(nnf_transformation,[],[f52])).
% 9.20/1.52  fof(f52,plain,(
% 9.20/1.52    ! [X2,X0,X1] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~sP1(X2,X0,X1))),
% 9.20/1.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 9.20/1.52  fof(f473,plain,(
% 9.20/1.52    ( ! [X2,X1] : (sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2) | r3_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1))) )),
% 9.20/1.52    inference(subsumption_resolution,[],[f472,f85])).
% 9.20/1.52  fof(f472,plain,(
% 9.20/1.52    ( ! [X2,X1] : (r3_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1)) | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2) | v2_struct_0(sK7)) )),
% 9.20/1.52    inference(subsumption_resolution,[],[f471,f86])).
% 9.20/1.52  fof(f471,plain,(
% 9.20/1.52    ( ! [X2,X1] : (r3_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1)) | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2) | ~v10_lattices(sK7) | v2_struct_0(sK7)) )),
% 9.20/1.52    inference(subsumption_resolution,[],[f470,f87])).
% 9.20/1.52  fof(f470,plain,(
% 9.20/1.52    ( ! [X2,X1] : (r3_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1)) | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2) | ~v4_lattice3(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7)) )),
% 9.20/1.52    inference(subsumption_resolution,[],[f457,f88])).
% 9.20/1.52  fof(f457,plain,(
% 9.20/1.52    ( ! [X2,X1] : (r3_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1)) | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2) | ~l3_lattices(sK7) | ~v4_lattice3(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7)) )),
% 9.20/1.52    inference(superposition,[],[f104,f365])).
% 9.20/1.52  fof(f365,plain,(
% 9.20/1.52    ( ! [X0] : (k15_lattice3(sK7,X0) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k15_lattice3(sK7,X0)))) )),
% 9.20/1.52    inference(subsumption_resolution,[],[f364,f85])).
% 9.20/1.52  fof(f364,plain,(
% 9.20/1.52    ( ! [X0] : (k15_lattice3(sK7,X0) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k15_lattice3(sK7,X0))) | v2_struct_0(sK7)) )),
% 9.20/1.52    inference(subsumption_resolution,[],[f363,f86])).
% 9.20/1.52  fof(f363,plain,(
% 9.20/1.52    ( ! [X0] : (k15_lattice3(sK7,X0) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k15_lattice3(sK7,X0))) | ~v10_lattices(sK7) | v2_struct_0(sK7)) )),
% 9.20/1.52    inference(subsumption_resolution,[],[f362,f88])).
% 9.20/1.52  fof(f362,plain,(
% 9.20/1.52    ( ! [X0] : (~l3_lattices(sK7) | k15_lattice3(sK7,X0) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k15_lattice3(sK7,X0))) | ~v10_lattices(sK7) | v2_struct_0(sK7)) )),
% 9.20/1.52    inference(resolution,[],[f311,f87])).
% 9.20/1.52  fof(f311,plain,(
% 9.20/1.52    ( ! [X2,X3] : (~v4_lattice3(X2) | ~l3_lattices(X2) | k15_lattice3(X2,X3) = k15_lattice3(X2,a_2_3_lattice3(X2,k15_lattice3(X2,X3))) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 9.20/1.52    inference(duplicate_literal_removal,[],[f307])).
% 9.20/1.52  fof(f307,plain,(
% 9.20/1.52    ( ! [X2,X3] : (k15_lattice3(X2,X3) = k15_lattice3(X2,a_2_3_lattice3(X2,k15_lattice3(X2,X3))) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | ~l3_lattices(X2) | v2_struct_0(X2)) )),
% 9.20/1.52    inference(resolution,[],[f99,f125])).
% 9.20/1.52  fof(f104,plain,(
% 9.20/1.52    ( ! [X2,X0,X1] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | sP1(X2,X0,X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 9.20/1.52    inference(cnf_transformation,[],[f53])).
% 9.20/1.52  fof(f53,plain,(
% 9.20/1.52    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | sP1(X2,X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 9.20/1.52    inference(definition_folding,[],[f31,f52])).
% 9.20/1.52  fof(f31,plain,(
% 9.20/1.52    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 9.20/1.52    inference(flattening,[],[f30])).
% 9.20/1.52  % (10426)Time limit reached!
% 9.20/1.52  % (10426)------------------------------
% 9.20/1.52  % (10426)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.32/1.54  % (10426)Termination reason: Time limit
% 9.32/1.54  
% 9.32/1.54  % (10426)Memory used [KB]: 11641
% 9.32/1.54  % (10426)Time elapsed: 1.117 s
% 9.32/1.54  % (10426)------------------------------
% 9.32/1.54  % (10426)------------------------------
% 9.32/1.54  fof(f30,plain,(
% 9.32/1.54    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 9.32/1.54    inference(ennf_transformation,[],[f16])).
% 9.32/1.54  fof(f16,axiom,(
% 9.32/1.54    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 9.32/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).
% 9.32/1.54  fof(f129,plain,(
% 9.32/1.54    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 9.32/1.54    inference(cnf_transformation,[],[f84])).
% 9.32/1.54  fof(f84,plain,(
% 9.32/1.54    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 9.32/1.54    inference(nnf_transformation,[],[f43])).
% 9.32/1.54  fof(f43,plain,(
% 9.32/1.54    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 9.32/1.54    inference(flattening,[],[f42])).
% 9.32/1.54  fof(f42,plain,(
% 9.32/1.54    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 9.32/1.54    inference(ennf_transformation,[],[f10])).
% 9.32/1.54  fof(f10,axiom,(
% 9.32/1.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 9.32/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 9.32/1.54  fof(f18569,plain,(
% 9.32/1.54    ( ! [X30] : (~m1_subset_1(X30,u1_struct_0(sK7)) | k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30)))) ) | ~spl12_33),
% 9.32/1.54    inference(subsumption_resolution,[],[f18568,f86])).
% 9.32/1.54  fof(f18568,plain,(
% 9.32/1.54    ( ! [X30] : (~m1_subset_1(X30,u1_struct_0(sK7)) | k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30))) | ~v10_lattices(sK7)) ) | ~spl12_33),
% 9.32/1.54    inference(subsumption_resolution,[],[f18567,f87])).
% 9.32/1.54  fof(f18567,plain,(
% 9.32/1.54    ( ! [X30] : (~m1_subset_1(X30,u1_struct_0(sK7)) | k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30))) | ~v4_lattice3(sK7) | ~v10_lattices(sK7)) ) | ~spl12_33),
% 9.32/1.54    inference(subsumption_resolution,[],[f18566,f88])).
% 9.32/1.54  fof(f18566,plain,(
% 9.32/1.54    ( ! [X30] : (~m1_subset_1(X30,u1_struct_0(sK7)) | k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30))) | ~l3_lattices(sK7) | ~v4_lattice3(sK7) | ~v10_lattices(sK7)) ) | ~spl12_33),
% 9.32/1.54    inference(subsumption_resolution,[],[f18523,f85])).
% 9.32/1.54  fof(f18523,plain,(
% 9.32/1.54    ( ! [X30] : (~m1_subset_1(X30,u1_struct_0(sK7)) | v2_struct_0(sK7) | k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30) = k15_lattice3(sK7,a_2_3_lattice3(sK7,k4_lattices(sK7,k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),X30))) | ~l3_lattices(sK7) | ~v4_lattice3(sK7) | ~v10_lattices(sK7)) ) | ~spl12_33),
% 9.32/1.54    inference(resolution,[],[f18474,f589])).
% 9.32/1.54  fof(f589,plain,(
% 9.32/1.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | v2_struct_0(X1) | k4_lattices(X1,X2,X0) = k15_lattice3(X1,a_2_3_lattice3(X1,k4_lattices(X1,X2,X0))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1)) )),
% 9.32/1.54    inference(global_subsumption,[],[f94,f97,f588])).
% 9.32/1.54  fof(f588,plain,(
% 9.32/1.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~v6_lattices(X1) | v2_struct_0(X1) | k4_lattices(X1,X2,X0) = k15_lattice3(X1,a_2_3_lattice3(X1,k4_lattices(X1,X2,X0))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1)) )),
% 9.32/1.54    inference(subsumption_resolution,[],[f587,f90])).
% 9.32/1.54  fof(f587,plain,(
% 9.32/1.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1) | k4_lattices(X1,X2,X0) = k15_lattice3(X1,a_2_3_lattice3(X1,k4_lattices(X1,X2,X0))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1)) )),
% 9.32/1.54    inference(duplicate_literal_removal,[],[f577])).
% 9.32/1.54  fof(f577,plain,(
% 9.32/1.54    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1) | k4_lattices(X1,X2,X0) = k15_lattice3(X1,a_2_3_lattice3(X1,k4_lattices(X1,X2,X0))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 9.32/1.54    inference(resolution,[],[f131,f99])).
% 9.32/1.54  fof(f10517,plain,(
% 9.32/1.54    ( ! [X0] : (r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k15_lattice3(sK7,X0))) )),
% 9.32/1.54    inference(resolution,[],[f10399,f167])).
% 9.32/1.54  fof(f10399,plain,(
% 9.32/1.54    ( ! [X2,X1] : (sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2) | r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1))) )),
% 9.32/1.54    inference(subsumption_resolution,[],[f10398,f86])).
% 9.32/1.54  fof(f10398,plain,(
% 9.32/1.54    ( ! [X2,X1] : (r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1)) | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2) | ~v10_lattices(sK7)) )),
% 9.32/1.54    inference(subsumption_resolution,[],[f10397,f87])).
% 9.32/1.54  fof(f10397,plain,(
% 9.32/1.54    ( ! [X2,X1] : (r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1)) | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2) | ~v4_lattice3(sK7) | ~v10_lattices(sK7)) )),
% 9.32/1.54    inference(subsumption_resolution,[],[f10396,f85])).
% 9.32/1.54  fof(f10396,plain,(
% 9.32/1.54    ( ! [X2,X1] : (r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1)) | v2_struct_0(sK7) | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2) | ~v4_lattice3(sK7) | ~v10_lattices(sK7)) )),
% 9.32/1.54    inference(subsumption_resolution,[],[f10395,f160])).
% 9.32/1.54  fof(f10395,plain,(
% 9.32/1.54    ( ! [X2,X1] : (r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1)) | ~v6_lattices(sK7) | v2_struct_0(sK7) | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2) | ~v4_lattice3(sK7) | ~v10_lattices(sK7)) )),
% 9.32/1.54    inference(subsumption_resolution,[],[f10394,f159])).
% 9.32/1.54  fof(f10394,plain,(
% 9.32/1.54    ( ! [X2,X1] : (r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1)) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7) | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2) | ~v4_lattice3(sK7) | ~v10_lattices(sK7)) )),
% 9.32/1.54    inference(subsumption_resolution,[],[f10393,f158])).
% 9.32/1.54  fof(f10393,plain,(
% 9.32/1.54    ( ! [X2,X1] : (r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1)) | ~v9_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7) | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2) | ~v4_lattice3(sK7) | ~v10_lattices(sK7)) )),
% 9.32/1.54    inference(subsumption_resolution,[],[f10287,f88])).
% 9.32/1.54  fof(f10287,plain,(
% 9.32/1.54    ( ! [X2,X1] : (r1_lattices(sK7,k15_lattice3(sK7,X2),k15_lattice3(sK7,X1)) | ~l3_lattices(sK7) | ~v9_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7) | sP1(a_2_3_lattice3(sK7,k15_lattice3(sK7,X1)),sK7,X2) | ~v4_lattice3(sK7) | ~v10_lattices(sK7)) )),
% 9.32/1.54    inference(superposition,[],[f1815,f365])).
% 9.32/1.54  fof(f1815,plain,(
% 9.32/1.54    ( ! [X2,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | sP1(X2,X0,X1) | ~v4_lattice3(X0) | ~v10_lattices(X0)) )),
% 9.32/1.54    inference(subsumption_resolution,[],[f1814,f125])).
% 9.32/1.54  fof(f1814,plain,(
% 9.32/1.54    ( ! [X2,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | sP1(X2,X0,X1) | ~v4_lattice3(X0) | ~v10_lattices(X0)) )),
% 9.32/1.54    inference(subsumption_resolution,[],[f1813,f125])).
% 9.32/1.54  fof(f1813,plain,(
% 9.32/1.54    ( ! [X2,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | sP1(X2,X0,X1) | ~v4_lattice3(X0) | ~v10_lattices(X0)) )),
% 9.32/1.54    inference(duplicate_literal_removal,[],[f1804])).
% 9.32/1.54  fof(f1804,plain,(
% 9.32/1.54    ( ! [X2,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~m1_subset_1(k15_lattice3(X0,X2),u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | sP1(X2,X0,X1) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 9.32/1.54    inference(resolution,[],[f129,f104])).
% 9.32/1.54  fof(f21458,plain,(
% 9.32/1.54    k15_lattice3(sK7,k1_xboole_0) != k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | (~spl12_3 | spl12_9 | ~spl12_18 | ~spl12_33)),
% 9.32/1.54    inference(superposition,[],[f21442,f19044])).
% 9.32/1.54  fof(f19044,plain,(
% 9.32/1.54    ( ! [X7] : (k4_lattices(sK7,k15_lattice3(sK7,X7),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,k15_lattice3(sK7,X7),sK9(k15_lattice3(sK7,k1_xboole_0),sK7))) ) | ~spl12_18),
% 9.32/1.54    inference(subsumption_resolution,[],[f19043,f85])).
% 9.32/1.54  fof(f19043,plain,(
% 9.32/1.54    ( ! [X7] : (k4_lattices(sK7,k15_lattice3(sK7,X7),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,k15_lattice3(sK7,X7),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | v2_struct_0(sK7)) ) | ~spl12_18),
% 9.32/1.54    inference(subsumption_resolution,[],[f19029,f88])).
% 9.32/1.54  fof(f19029,plain,(
% 9.32/1.54    ( ! [X7] : (k4_lattices(sK7,k15_lattice3(sK7,X7),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,k15_lattice3(sK7,X7),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | ~l3_lattices(sK7) | v2_struct_0(sK7)) ) | ~spl12_18),
% 9.32/1.54    inference(resolution,[],[f14206,f125])).
% 9.32/1.54  fof(f14206,plain,(
% 9.32/1.54    ( ! [X9] : (~m1_subset_1(X9,u1_struct_0(sK7)) | k4_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7))) ) | ~spl12_18),
% 9.32/1.54    inference(subsumption_resolution,[],[f14205,f85])).
% 9.32/1.54  fof(f14205,plain,(
% 9.32/1.54    ( ! [X9] : (k4_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | ~m1_subset_1(X9,u1_struct_0(sK7)) | v2_struct_0(sK7)) ) | ~spl12_18),
% 9.32/1.54    inference(subsumption_resolution,[],[f14204,f160])).
% 9.32/1.54  fof(f14204,plain,(
% 9.32/1.54    ( ! [X9] : (k4_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | ~m1_subset_1(X9,u1_struct_0(sK7)) | ~v6_lattices(sK7) | v2_struct_0(sK7)) ) | ~spl12_18),
% 9.32/1.54    inference(subsumption_resolution,[],[f14174,f137])).
% 9.32/1.54  fof(f14174,plain,(
% 9.32/1.54    ( ! [X9] : (k4_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,X9,sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | ~m1_subset_1(X9,u1_struct_0(sK7)) | ~l1_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7)) ) | ~spl12_18),
% 9.32/1.54    inference(resolution,[],[f4323,f133])).
% 9.32/1.54  fof(f133,plain,(
% 9.32/1.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 9.32/1.54    inference(cnf_transformation,[],[f49])).
% 9.32/1.54  fof(f49,plain,(
% 9.32/1.54    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 9.32/1.54    inference(flattening,[],[f48])).
% 9.32/1.54  fof(f48,plain,(
% 9.32/1.54    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 9.32/1.54    inference(ennf_transformation,[],[f9])).
% 9.32/1.54  fof(f9,axiom,(
% 9.32/1.54    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 9.32/1.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 9.32/1.54  fof(f21442,plain,(
% 9.32/1.54    k15_lattice3(sK7,k1_xboole_0) != k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | (~spl12_3 | spl12_9 | ~spl12_18 | ~spl12_33)),
% 9.32/1.54    inference(trivial_inequality_removal,[],[f21388])).
% 9.32/1.54  fof(f21388,plain,(
% 9.32/1.54    k15_lattice3(sK7,k1_xboole_0) != k15_lattice3(sK7,k1_xboole_0) | k15_lattice3(sK7,k1_xboole_0) != k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | (~spl12_3 | spl12_9 | ~spl12_18 | ~spl12_33)),
% 9.32/1.54    inference(backward_demodulation,[],[f18984,f21357])).
% 9.32/1.54  fof(f18984,plain,(
% 9.32/1.54    k15_lattice3(sK7,k1_xboole_0) != k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | k15_lattice3(sK7,k1_xboole_0) != k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | (~spl12_3 | spl12_9 | ~spl12_18)),
% 9.32/1.54    inference(subsumption_resolution,[],[f18983,f3048])).
% 9.32/1.54  fof(f3048,plain,(
% 9.32/1.54    ~sP2(k15_lattice3(sK7,k1_xboole_0),sK7) | spl12_9),
% 9.32/1.54    inference(avatar_component_clause,[],[f3046])).
% 9.32/1.54  fof(f3046,plain,(
% 9.32/1.54    spl12_9 <=> sP2(k15_lattice3(sK7,k1_xboole_0),sK7)),
% 9.32/1.54    introduced(avatar_definition,[new_symbols(naming,[spl12_9])])).
% 9.32/1.54  fof(f18983,plain,(
% 9.32/1.54    k15_lattice3(sK7,k1_xboole_0) != k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | sP2(k15_lattice3(sK7,k1_xboole_0),sK7) | k15_lattice3(sK7,k1_xboole_0) != k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | (~spl12_3 | ~spl12_18)),
% 9.32/1.54    inference(superposition,[],[f112,f14191])).
% 9.32/1.54  fof(f14191,plain,(
% 9.32/1.54    k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) = k2_lattices(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7),k15_lattice3(sK7,k1_xboole_0)) | (~spl12_3 | ~spl12_18)),
% 9.32/1.54    inference(forward_demodulation,[],[f14160,f14159])).
% 9.32/1.54  fof(f14159,plain,(
% 9.32/1.54    k4_lattices(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7),k15_lattice3(sK7,k1_xboole_0)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK9(k15_lattice3(sK7,k1_xboole_0),sK7)) | (~spl12_3 | ~spl12_18)),
% 9.32/1.54    inference(resolution,[],[f4323,f1893])).
% 9.32/1.54  fof(f1893,plain,(
% 9.32/1.54    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK7)) | k4_lattices(sK7,X4,k15_lattice3(sK7,k1_xboole_0)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),X4)) ) | ~spl12_3),
% 9.32/1.54    inference(subsumption_resolution,[],[f1892,f85])).
% 9.32/1.54  fof(f1892,plain,(
% 9.32/1.54    ( ! [X4] : (k4_lattices(sK7,X4,k15_lattice3(sK7,k1_xboole_0)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),X4) | ~m1_subset_1(X4,u1_struct_0(sK7)) | v2_struct_0(sK7)) ) | ~spl12_3),
% 9.32/1.54    inference(subsumption_resolution,[],[f1891,f160])).
% 9.32/1.54  fof(f1891,plain,(
% 9.32/1.54    ( ! [X4] : (k4_lattices(sK7,X4,k15_lattice3(sK7,k1_xboole_0)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),X4) | ~m1_subset_1(X4,u1_struct_0(sK7)) | ~v6_lattices(sK7) | v2_struct_0(sK7)) ) | ~spl12_3),
% 9.32/1.54    inference(subsumption_resolution,[],[f1888,f137])).
% 9.32/1.54  fof(f1888,plain,(
% 9.32/1.54    ( ! [X4] : (k4_lattices(sK7,X4,k15_lattice3(sK7,k1_xboole_0)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),X4) | ~m1_subset_1(X4,u1_struct_0(sK7)) | ~l1_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7)) ) | ~spl12_3),
% 9.32/1.54    inference(resolution,[],[f1865,f132])).
% 9.32/1.54  fof(f14160,plain,(
% 9.32/1.54    k4_lattices(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7),k15_lattice3(sK7,k1_xboole_0)) = k2_lattices(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7),k15_lattice3(sK7,k1_xboole_0)) | (~spl12_3 | ~spl12_18)),
% 9.32/1.54    inference(resolution,[],[f4323,f1896])).
% 9.32/1.54  fof(f1896,plain,(
% 9.32/1.54    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK7)) | k4_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0)) = k2_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0))) ) | ~spl12_3),
% 9.32/1.54    inference(subsumption_resolution,[],[f1895,f85])).
% 9.32/1.54  fof(f1895,plain,(
% 9.32/1.54    ( ! [X5] : (k4_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0)) = k2_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0)) | ~m1_subset_1(X5,u1_struct_0(sK7)) | v2_struct_0(sK7)) ) | ~spl12_3),
% 9.32/1.54    inference(subsumption_resolution,[],[f1894,f160])).
% 9.32/1.54  fof(f1894,plain,(
% 9.32/1.54    ( ! [X5] : (k4_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0)) = k2_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0)) | ~m1_subset_1(X5,u1_struct_0(sK7)) | ~v6_lattices(sK7) | v2_struct_0(sK7)) ) | ~spl12_3),
% 9.32/1.54    inference(subsumption_resolution,[],[f1889,f137])).
% 9.32/1.54  fof(f1889,plain,(
% 9.32/1.54    ( ! [X5] : (k4_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0)) = k2_lattices(sK7,X5,k15_lattice3(sK7,k1_xboole_0)) | ~m1_subset_1(X5,u1_struct_0(sK7)) | ~l1_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7)) ) | ~spl12_3),
% 9.32/1.54    inference(resolution,[],[f1865,f133])).
% 9.32/1.54  fof(f112,plain,(
% 9.32/1.54    ( ! [X0,X1] : (k2_lattices(X1,sK9(X0,X1),X0) != X0 | sP2(X0,X1) | k2_lattices(X1,X0,sK9(X0,X1)) != X0) )),
% 9.32/1.54    inference(cnf_transformation,[],[f72])).
% 9.32/1.54  fof(f72,plain,(
% 9.32/1.54    ! [X0,X1] : ((sP2(X0,X1) | ((k2_lattices(X1,sK9(X0,X1),X0) != X0 | k2_lattices(X1,X0,sK9(X0,X1)) != X0) & m1_subset_1(sK9(X0,X1),u1_struct_0(X1)))) & (! [X3] : ((k2_lattices(X1,X3,X0) = X0 & k2_lattices(X1,X0,X3) = X0) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP2(X0,X1)))),
% 9.32/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f70,f71])).
% 9.32/1.54  fof(f71,plain,(
% 9.32/1.54    ! [X1,X0] : (? [X2] : ((k2_lattices(X1,X2,X0) != X0 | k2_lattices(X1,X0,X2) != X0) & m1_subset_1(X2,u1_struct_0(X1))) => ((k2_lattices(X1,sK9(X0,X1),X0) != X0 | k2_lattices(X1,X0,sK9(X0,X1)) != X0) & m1_subset_1(sK9(X0,X1),u1_struct_0(X1))))),
% 9.32/1.54    introduced(choice_axiom,[])).
% 9.32/1.54  fof(f70,plain,(
% 9.32/1.54    ! [X0,X1] : ((sP2(X0,X1) | ? [X2] : ((k2_lattices(X1,X2,X0) != X0 | k2_lattices(X1,X0,X2) != X0) & m1_subset_1(X2,u1_struct_0(X1)))) & (! [X3] : ((k2_lattices(X1,X3,X0) = X0 & k2_lattices(X1,X0,X3) = X0) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP2(X0,X1)))),
% 9.32/1.54    inference(rectify,[],[f69])).
% 9.32/1.54  fof(f69,plain,(
% 9.32/1.54    ! [X1,X0] : ((sP2(X1,X0) | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP2(X1,X0)))),
% 9.32/1.54    inference(nnf_transformation,[],[f54])).
% 9.32/1.54  fof(f54,plain,(
% 9.32/1.54    ! [X1,X0] : (sP2(X1,X0) <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 9.32/1.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 9.32/1.54  fof(f18487,plain,(
% 9.32/1.54    ~spl12_3 | spl12_33),
% 9.32/1.54    inference(avatar_contradiction_clause,[],[f18486])).
% 9.32/1.54  fof(f18486,plain,(
% 9.32/1.54    $false | (~spl12_3 | spl12_33)),
% 9.32/1.54    inference(subsumption_resolution,[],[f18485,f85])).
% 9.32/1.54  fof(f18485,plain,(
% 9.32/1.54    v2_struct_0(sK7) | (~spl12_3 | spl12_33)),
% 9.32/1.54    inference(subsumption_resolution,[],[f18484,f160])).
% 9.32/1.54  fof(f18484,plain,(
% 9.32/1.54    ~v6_lattices(sK7) | v2_struct_0(sK7) | (~spl12_3 | spl12_33)),
% 9.32/1.54    inference(subsumption_resolution,[],[f18483,f137])).
% 9.32/1.54  fof(f18483,plain,(
% 9.32/1.54    ~l1_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7) | (~spl12_3 | spl12_33)),
% 9.32/1.54    inference(subsumption_resolution,[],[f18482,f326])).
% 9.32/1.54  fof(f18482,plain,(
% 9.32/1.54    ~m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) | ~l1_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7) | (~spl12_3 | spl12_33)),
% 9.32/1.54    inference(subsumption_resolution,[],[f18481,f1865])).
% 9.32/1.54  fof(f18481,plain,(
% 9.32/1.54    ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) | ~l1_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7) | spl12_33),
% 9.32/1.54    inference(resolution,[],[f18475,f131])).
% 9.32/1.54  fof(f18475,plain,(
% 9.32/1.54    ~m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7)) | spl12_33),
% 9.32/1.54    inference(avatar_component_clause,[],[f18473])).
% 9.32/1.54  fof(f14493,plain,(
% 9.32/1.54    spl12_2 | ~spl12_3 | ~spl12_9),
% 9.32/1.54    inference(avatar_contradiction_clause,[],[f14492])).
% 9.32/1.54  fof(f14492,plain,(
% 9.32/1.54    $false | (spl12_2 | ~spl12_3 | ~spl12_9)),
% 9.32/1.54    inference(subsumption_resolution,[],[f14491,f13994])).
% 9.32/1.54  fof(f13994,plain,(
% 9.32/1.54    k15_lattice3(sK7,k1_xboole_0) = k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK11(k15_lattice3(sK7,k1_xboole_0),sK7)) | (spl12_2 | ~spl12_3 | ~spl12_9)),
% 9.32/1.54    inference(resolution,[],[f3047,f3739])).
% 9.32/1.54  fof(f3739,plain,(
% 9.32/1.54    ( ! [X0] : (~sP2(X0,sK7) | k2_lattices(sK7,X0,sK11(k15_lattice3(sK7,k1_xboole_0),sK7)) = X0) ) | (spl12_2 | ~spl12_3)),
% 9.32/1.54    inference(resolution,[],[f3722,f109])).
% 9.32/1.54  fof(f109,plain,(
% 9.32/1.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(X1)) | k2_lattices(X1,X0,X3) = X0 | ~sP2(X0,X1)) )),
% 9.32/1.54    inference(cnf_transformation,[],[f72])).
% 9.32/1.54  fof(f3722,plain,(
% 9.32/1.54    m1_subset_1(sK11(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7)) | (spl12_2 | ~spl12_3)),
% 9.32/1.54    inference(subsumption_resolution,[],[f3721,f85])).
% 9.32/1.54  fof(f3721,plain,(
% 9.32/1.54    m1_subset_1(sK11(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7)) | v2_struct_0(sK7) | (spl12_2 | ~spl12_3)),
% 9.32/1.54    inference(subsumption_resolution,[],[f3717,f88])).
% 9.32/1.54  fof(f3717,plain,(
% 9.32/1.54    m1_subset_1(sK11(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7)) | ~l3_lattices(sK7) | v2_struct_0(sK7) | (spl12_2 | ~spl12_3)),
% 9.32/1.54    inference(superposition,[],[f125,f1905])).
% 9.32/1.54  fof(f1905,plain,(
% 9.32/1.54    sK11(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK11(k15_lattice3(sK7,k1_xboole_0),sK7))) | (spl12_2 | ~spl12_3)),
% 9.32/1.54    inference(subsumption_resolution,[],[f1904,f85])).
% 9.32/1.54  fof(f1904,plain,(
% 9.32/1.54    v2_struct_0(sK7) | sK11(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK11(k15_lattice3(sK7,k1_xboole_0),sK7))) | (spl12_2 | ~spl12_3)),
% 9.32/1.54    inference(subsumption_resolution,[],[f1903,f86])).
% 9.32/1.54  fof(f1903,plain,(
% 9.32/1.54    ~v10_lattices(sK7) | v2_struct_0(sK7) | sK11(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK11(k15_lattice3(sK7,k1_xboole_0),sK7))) | (spl12_2 | ~spl12_3)),
% 9.32/1.54    inference(subsumption_resolution,[],[f1902,f87])).
% 9.32/1.54  fof(f1902,plain,(
% 9.32/1.54    ~v4_lattice3(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7) | sK11(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK11(k15_lattice3(sK7,k1_xboole_0),sK7))) | (spl12_2 | ~spl12_3)),
% 9.32/1.54    inference(subsumption_resolution,[],[f1897,f88])).
% 9.32/1.54  fof(f1897,plain,(
% 9.32/1.54    ~l3_lattices(sK7) | ~v4_lattice3(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7) | sK11(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK11(k15_lattice3(sK7,k1_xboole_0),sK7))) | (spl12_2 | ~spl12_3)),
% 9.32/1.54    inference(resolution,[],[f1890,f309])).
% 9.32/1.54  fof(f309,plain,(
% 9.32/1.54    ( ! [X6,X7] : (sP4(X7,X6) | ~l3_lattices(X6) | ~v4_lattice3(X6) | ~v10_lattices(X6) | v2_struct_0(X6) | sK11(X7,X6) = k15_lattice3(X6,a_2_3_lattice3(X6,sK11(X7,X6)))) )),
% 9.32/1.54    inference(resolution,[],[f99,f121])).
% 9.32/1.54  fof(f121,plain,(
% 9.32/1.54    ( ! [X0,X1] : (m1_subset_1(sK11(X0,X1),u1_struct_0(X1)) | sP4(X0,X1)) )),
% 9.32/1.54    inference(cnf_transformation,[],[f81])).
% 9.32/1.54  fof(f81,plain,(
% 9.32/1.54    ! [X0,X1] : ((sP4(X0,X1) | ((k2_lattices(X1,sK11(X0,X1),X0) != X0 | k2_lattices(X1,X0,sK11(X0,X1)) != X0) & m1_subset_1(sK11(X0,X1),u1_struct_0(X1)))) & (! [X3] : ((k2_lattices(X1,X3,X0) = X0 & k2_lattices(X1,X0,X3) = X0) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP4(X0,X1)))),
% 9.32/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f79,f80])).
% 9.32/1.54  fof(f80,plain,(
% 9.32/1.54    ! [X1,X0] : (? [X2] : ((k2_lattices(X1,X2,X0) != X0 | k2_lattices(X1,X0,X2) != X0) & m1_subset_1(X2,u1_struct_0(X1))) => ((k2_lattices(X1,sK11(X0,X1),X0) != X0 | k2_lattices(X1,X0,sK11(X0,X1)) != X0) & m1_subset_1(sK11(X0,X1),u1_struct_0(X1))))),
% 9.32/1.54    introduced(choice_axiom,[])).
% 9.32/1.54  fof(f79,plain,(
% 9.32/1.54    ! [X0,X1] : ((sP4(X0,X1) | ? [X2] : ((k2_lattices(X1,X2,X0) != X0 | k2_lattices(X1,X0,X2) != X0) & m1_subset_1(X2,u1_struct_0(X1)))) & (! [X3] : ((k2_lattices(X1,X3,X0) = X0 & k2_lattices(X1,X0,X3) = X0) | ~m1_subset_1(X3,u1_struct_0(X1))) | ~sP4(X0,X1)))),
% 9.32/1.54    inference(rectify,[],[f78])).
% 9.32/1.54  fof(f78,plain,(
% 9.32/1.54    ! [X1,X0] : ((sP4(X1,X0) | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~sP4(X1,X0)))),
% 9.32/1.54    inference(nnf_transformation,[],[f57])).
% 9.32/1.54  fof(f57,plain,(
% 9.32/1.54    ! [X1,X0] : (sP4(X1,X0) <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))))),
% 9.32/1.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 9.32/1.54  fof(f1890,plain,(
% 9.32/1.54    ~sP4(k15_lattice3(sK7,k1_xboole_0),sK7) | (spl12_2 | ~spl12_3)),
% 9.32/1.54    inference(subsumption_resolution,[],[f1885,f152])).
% 9.32/1.54  fof(f152,plain,(
% 9.32/1.54    ~sP5(sK7) | spl12_2),
% 9.32/1.54    inference(avatar_component_clause,[],[f150])).
% 9.32/1.54  fof(f150,plain,(
% 9.32/1.54    spl12_2 <=> sP5(sK7)),
% 9.32/1.54    introduced(avatar_definition,[new_symbols(naming,[spl12_2])])).
% 9.32/1.54  fof(f1885,plain,(
% 9.32/1.54    ~sP4(k15_lattice3(sK7,k1_xboole_0),sK7) | sP5(sK7) | ~spl12_3),
% 9.32/1.54    inference(resolution,[],[f1865,f118])).
% 9.32/1.54  fof(f118,plain,(
% 9.32/1.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~sP4(X1,X0) | sP5(X0)) )),
% 9.32/1.54    inference(cnf_transformation,[],[f77])).
% 9.32/1.54  fof(f77,plain,(
% 9.32/1.54    ! [X0] : ((sP5(X0) | ! [X1] : (~sP4(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((sP4(sK10(X0),X0) & m1_subset_1(sK10(X0),u1_struct_0(X0))) | ~sP5(X0)))),
% 9.32/1.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f75,f76])).
% 9.32/1.54  fof(f76,plain,(
% 9.32/1.54    ! [X0] : (? [X2] : (sP4(X2,X0) & m1_subset_1(X2,u1_struct_0(X0))) => (sP4(sK10(X0),X0) & m1_subset_1(sK10(X0),u1_struct_0(X0))))),
% 9.32/1.54    introduced(choice_axiom,[])).
% 9.32/1.54  fof(f75,plain,(
% 9.32/1.54    ! [X0] : ((sP5(X0) | ! [X1] : (~sP4(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X2] : (sP4(X2,X0) & m1_subset_1(X2,u1_struct_0(X0))) | ~sP5(X0)))),
% 9.32/1.54    inference(rectify,[],[f74])).
% 9.32/1.54  fof(f74,plain,(
% 9.32/1.54    ! [X0] : ((sP5(X0) | ! [X1] : (~sP4(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (sP4(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))) | ~sP5(X0)))),
% 9.32/1.54    inference(nnf_transformation,[],[f58])).
% 9.32/1.54  fof(f58,plain,(
% 9.32/1.54    ! [X0] : (sP5(X0) <=> ? [X1] : (sP4(X1,X0) & m1_subset_1(X1,u1_struct_0(X0))))),
% 9.32/1.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 9.32/1.54  fof(f3047,plain,(
% 9.32/1.54    sP2(k15_lattice3(sK7,k1_xboole_0),sK7) | ~spl12_9),
% 9.32/1.54    inference(avatar_component_clause,[],[f3046])).
% 9.32/1.54  fof(f14491,plain,(
% 9.32/1.54    k15_lattice3(sK7,k1_xboole_0) != k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK11(k15_lattice3(sK7,k1_xboole_0),sK7)) | (spl12_2 | ~spl12_3 | ~spl12_9)),
% 9.32/1.54    inference(subsumption_resolution,[],[f14490,f1890])).
% 9.32/1.54  fof(f14490,plain,(
% 9.32/1.54    sP4(k15_lattice3(sK7,k1_xboole_0),sK7) | k15_lattice3(sK7,k1_xboole_0) != k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK11(k15_lattice3(sK7,k1_xboole_0),sK7)) | (spl12_2 | ~spl12_3 | ~spl12_9)),
% 9.32/1.54    inference(trivial_inequality_removal,[],[f14489])).
% 9.32/1.54  fof(f14489,plain,(
% 9.32/1.54    k15_lattice3(sK7,k1_xboole_0) != k15_lattice3(sK7,k1_xboole_0) | sP4(k15_lattice3(sK7,k1_xboole_0),sK7) | k15_lattice3(sK7,k1_xboole_0) != k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),sK11(k15_lattice3(sK7,k1_xboole_0),sK7)) | (spl12_2 | ~spl12_3 | ~spl12_9)),
% 9.32/1.54    inference(superposition,[],[f122,f13995])).
% 9.32/1.54  fof(f13995,plain,(
% 9.32/1.54    k15_lattice3(sK7,k1_xboole_0) = k2_lattices(sK7,sK11(k15_lattice3(sK7,k1_xboole_0),sK7),k15_lattice3(sK7,k1_xboole_0)) | (spl12_2 | ~spl12_3 | ~spl12_9)),
% 9.32/1.54    inference(resolution,[],[f3047,f3740])).
% 9.32/1.54  fof(f3740,plain,(
% 9.32/1.54    ( ! [X1] : (~sP2(X1,sK7) | k2_lattices(sK7,sK11(k15_lattice3(sK7,k1_xboole_0),sK7),X1) = X1) ) | (spl12_2 | ~spl12_3)),
% 9.32/1.54    inference(resolution,[],[f3722,f110])).
% 9.32/1.54  fof(f110,plain,(
% 9.32/1.54    ( ! [X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(X1)) | k2_lattices(X1,X3,X0) = X0 | ~sP2(X0,X1)) )),
% 9.32/1.54    inference(cnf_transformation,[],[f72])).
% 9.32/1.54  fof(f122,plain,(
% 9.32/1.54    ( ! [X0,X1] : (k2_lattices(X1,sK11(X0,X1),X0) != X0 | sP4(X0,X1) | k2_lattices(X1,X0,sK11(X0,X1)) != X0) )),
% 9.32/1.54    inference(cnf_transformation,[],[f81])).
% 9.32/1.54  fof(f4331,plain,(
% 9.32/1.54    spl12_9 | spl12_18),
% 9.32/1.54    inference(avatar_contradiction_clause,[],[f4330])).
% 9.32/1.54  fof(f4330,plain,(
% 9.32/1.54    $false | (spl12_9 | spl12_18)),
% 9.32/1.54    inference(subsumption_resolution,[],[f4324,f3839])).
% 9.32/1.54  fof(f3839,plain,(
% 9.32/1.54    m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7)) | spl12_9),
% 9.32/1.54    inference(subsumption_resolution,[],[f3838,f85])).
% 9.32/1.54  fof(f3838,plain,(
% 9.32/1.54    m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7)) | v2_struct_0(sK7) | spl12_9),
% 9.32/1.54    inference(subsumption_resolution,[],[f3834,f88])).
% 9.32/1.54  fof(f3834,plain,(
% 9.32/1.54    m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7)) | ~l3_lattices(sK7) | v2_struct_0(sK7) | spl12_9),
% 9.32/1.54    inference(superposition,[],[f125,f3329])).
% 9.32/1.54  fof(f3329,plain,(
% 9.32/1.54    sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7))) | spl12_9),
% 9.32/1.54    inference(subsumption_resolution,[],[f3328,f85])).
% 9.32/1.54  fof(f3328,plain,(
% 9.32/1.54    v2_struct_0(sK7) | sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7))) | spl12_9),
% 9.32/1.54    inference(subsumption_resolution,[],[f3327,f86])).
% 9.32/1.54  fof(f3327,plain,(
% 9.32/1.54    ~v10_lattices(sK7) | v2_struct_0(sK7) | sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7))) | spl12_9),
% 9.32/1.54    inference(subsumption_resolution,[],[f3326,f87])).
% 9.32/1.54  fof(f3326,plain,(
% 9.32/1.54    ~v4_lattice3(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7) | sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7))) | spl12_9),
% 9.32/1.54    inference(subsumption_resolution,[],[f3317,f88])).
% 9.32/1.54  fof(f3317,plain,(
% 9.32/1.54    ~l3_lattices(sK7) | ~v4_lattice3(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7) | sK9(k15_lattice3(sK7,k1_xboole_0),sK7) = k15_lattice3(sK7,a_2_3_lattice3(sK7,sK9(k15_lattice3(sK7,k1_xboole_0),sK7))) | spl12_9),
% 9.32/1.54    inference(resolution,[],[f3048,f308])).
% 9.32/1.54  fof(f308,plain,(
% 9.32/1.54    ( ! [X4,X5] : (sP2(X5,X4) | ~l3_lattices(X4) | ~v4_lattice3(X4) | ~v10_lattices(X4) | v2_struct_0(X4) | sK9(X5,X4) = k15_lattice3(X4,a_2_3_lattice3(X4,sK9(X5,X4)))) )),
% 9.32/1.54    inference(resolution,[],[f99,f111])).
% 9.32/1.54  fof(f111,plain,(
% 9.32/1.54    ( ! [X0,X1] : (m1_subset_1(sK9(X0,X1),u1_struct_0(X1)) | sP2(X0,X1)) )),
% 9.32/1.54    inference(cnf_transformation,[],[f72])).
% 9.32/1.54  fof(f4324,plain,(
% 9.32/1.54    ~m1_subset_1(sK9(k15_lattice3(sK7,k1_xboole_0),sK7),u1_struct_0(sK7)) | spl12_18),
% 9.32/1.54    inference(avatar_component_clause,[],[f4322])).
% 9.32/1.54  fof(f2879,plain,(
% 9.32/1.54    ~spl12_2 | ~spl12_3 | ~spl12_4),
% 9.32/1.54    inference(avatar_contradiction_clause,[],[f2878])).
% 9.32/1.55  fof(f2878,plain,(
% 9.32/1.55    $false | (~spl12_2 | ~spl12_3 | ~spl12_4)),
% 9.32/1.55    inference(global_subsumption,[],[f143,f151,f2056,f2877])).
% 9.32/1.55  fof(f2877,plain,(
% 9.32/1.55    k5_lattices(sK7) = k15_lattice3(sK7,k1_xboole_0) | (~spl12_2 | ~spl12_3 | ~spl12_4)),
% 9.32/1.55    inference(subsumption_resolution,[],[f2876,f1870])).
% 9.32/1.55  fof(f1870,plain,(
% 9.32/1.55    r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) | ~spl12_4),
% 9.32/1.55    inference(avatar_component_clause,[],[f1868])).
% 9.32/1.55  fof(f1868,plain,(
% 9.32/1.55    spl12_4 <=> r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))),
% 9.32/1.55    introduced(avatar_definition,[new_symbols(naming,[spl12_4])])).
% 9.32/1.55  fof(f2876,plain,(
% 9.32/1.55    ~r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) | k5_lattices(sK7) = k15_lattice3(sK7,k1_xboole_0) | (~spl12_2 | ~spl12_3)),
% 9.32/1.55    inference(forward_demodulation,[],[f2875,f2865])).
% 9.32/1.55  fof(f2865,plain,(
% 9.32/1.55    k5_lattices(sK7) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | (~spl12_2 | ~spl12_3)),
% 9.32/1.55    inference(backward_demodulation,[],[f2706,f2806])).
% 9.32/1.55  fof(f2806,plain,(
% 9.32/1.55    ( ! [X1] : (k5_lattices(sK7) = k2_lattices(sK7,k15_lattice3(sK7,X1),k5_lattices(sK7))) ) | ~spl12_2),
% 9.32/1.55    inference(backward_demodulation,[],[f2220,f2746])).
% 9.32/1.55  fof(f2746,plain,(
% 9.32/1.55    k5_lattices(sK7) = sK10(sK7) | ~spl12_2),
% 9.32/1.55    inference(global_subsumption,[],[f143,f151,f2745])).
% 9.32/1.55  fof(f2745,plain,(
% 9.32/1.55    k5_lattices(sK7) = sK10(sK7) | ~v13_lattices(sK7) | ~spl12_2),
% 9.32/1.55    inference(forward_demodulation,[],[f2744,f2214])).
% 9.32/1.55  fof(f2214,plain,(
% 9.32/1.55    sK10(sK7) = k2_lattices(sK7,k5_lattices(sK7),sK10(sK7)) | ~spl12_2),
% 9.32/1.55    inference(subsumption_resolution,[],[f2213,f85])).
% 9.32/1.55  fof(f2213,plain,(
% 9.32/1.55    v2_struct_0(sK7) | sK10(sK7) = k2_lattices(sK7,k5_lattices(sK7),sK10(sK7)) | ~spl12_2),
% 9.32/1.55    inference(subsumption_resolution,[],[f2071,f137])).
% 9.32/1.55  fof(f2071,plain,(
% 9.32/1.55    ~l1_lattices(sK7) | v2_struct_0(sK7) | sK10(sK7) = k2_lattices(sK7,k5_lattices(sK7),sK10(sK7)) | ~spl12_2),
% 9.32/1.55    inference(resolution,[],[f151,f229])).
% 9.32/1.55  fof(f229,plain,(
% 9.32/1.55    ( ! [X0] : (~sP5(X0) | ~l1_lattices(X0) | v2_struct_0(X0) | sK10(X0) = k2_lattices(X0,k5_lattices(X0),sK10(X0))) )),
% 9.32/1.55    inference(resolution,[],[f209,f117])).
% 9.32/1.55  fof(f117,plain,(
% 9.32/1.55    ( ! [X0] : (sP4(sK10(X0),X0) | ~sP5(X0)) )),
% 9.32/1.55    inference(cnf_transformation,[],[f77])).
% 9.32/1.55  fof(f209,plain,(
% 9.32/1.55    ( ! [X2,X3] : (~sP4(X3,X2) | k2_lattices(X2,k5_lattices(X2),X3) = X3 | ~l1_lattices(X2) | v2_struct_0(X2)) )),
% 9.32/1.55    inference(resolution,[],[f120,f106])).
% 9.32/1.55  fof(f120,plain,(
% 9.32/1.55    ( ! [X0,X3,X1] : (~m1_subset_1(X3,u1_struct_0(X1)) | k2_lattices(X1,X3,X0) = X0 | ~sP4(X0,X1)) )),
% 9.32/1.55    inference(cnf_transformation,[],[f81])).
% 9.32/1.55  fof(f2744,plain,(
% 9.32/1.55    ~v13_lattices(sK7) | k5_lattices(sK7) = k2_lattices(sK7,k5_lattices(sK7),sK10(sK7)) | ~spl12_2),
% 9.32/1.55    inference(subsumption_resolution,[],[f2205,f137])).
% 9.32/1.55  fof(f2205,plain,(
% 9.32/1.55    ~v13_lattices(sK7) | k5_lattices(sK7) = k2_lattices(sK7,k5_lattices(sK7),sK10(sK7)) | ~l1_lattices(sK7) | ~spl12_2),
% 9.32/1.55    inference(subsumption_resolution,[],[f2068,f85])).
% 9.32/1.55  fof(f2068,plain,(
% 9.32/1.55    v2_struct_0(sK7) | ~v13_lattices(sK7) | k5_lattices(sK7) = k2_lattices(sK7,k5_lattices(sK7),sK10(sK7)) | ~l1_lattices(sK7) | ~spl12_2),
% 9.32/1.55    inference(resolution,[],[f151,f198])).
% 9.32/1.55  fof(f198,plain,(
% 9.32/1.55    ( ! [X1] : (~sP5(X1) | v2_struct_0(X1) | ~v13_lattices(X1) | k5_lattices(X1) = k2_lattices(X1,k5_lattices(X1),sK10(X1)) | ~l1_lattices(X1)) )),
% 9.32/1.55    inference(resolution,[],[f194,f172])).
% 9.32/1.55  fof(f172,plain,(
% 9.32/1.55    ( ! [X0,X1] : (~sP2(X1,X0) | k2_lattices(X0,X1,sK10(X0)) = X1 | ~sP5(X0)) )),
% 9.32/1.55    inference(resolution,[],[f109,f116])).
% 9.32/1.55  fof(f116,plain,(
% 9.32/1.55    ( ! [X0] : (m1_subset_1(sK10(X0),u1_struct_0(X0)) | ~sP5(X0)) )),
% 9.32/1.55    inference(cnf_transformation,[],[f77])).
% 9.32/1.55  fof(f194,plain,(
% 9.32/1.55    ( ! [X0] : (sP2(k5_lattices(X0),X0) | ~l1_lattices(X0) | v2_struct_0(X0) | ~v13_lattices(X0)) )),
% 9.32/1.55    inference(resolution,[],[f191,f134])).
% 9.32/1.55  fof(f134,plain,(
% 9.32/1.55    ( ! [X0] : (~sP3(X0,k5_lattices(X0)) | sP2(k5_lattices(X0),X0)) )),
% 9.32/1.55    inference(equality_resolution,[],[f107])).
% 9.32/1.55  fof(f107,plain,(
% 9.32/1.55    ( ! [X0,X1] : (sP2(X1,X0) | k5_lattices(X0) != X1 | ~sP3(X0,X1)) )),
% 9.32/1.55    inference(cnf_transformation,[],[f68])).
% 9.32/1.55  fof(f68,plain,(
% 9.32/1.55    ! [X0,X1] : (((k5_lattices(X0) = X1 | ~sP2(X1,X0)) & (sP2(X1,X0) | k5_lattices(X0) != X1)) | ~sP3(X0,X1))),
% 9.32/1.55    inference(nnf_transformation,[],[f55])).
% 9.32/1.55  fof(f55,plain,(
% 9.32/1.55    ! [X0,X1] : ((k5_lattices(X0) = X1 <=> sP2(X1,X0)) | ~sP3(X0,X1))),
% 9.32/1.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 9.32/1.55  fof(f191,plain,(
% 9.32/1.55    ( ! [X1] : (sP3(X1,k5_lattices(X1)) | ~v13_lattices(X1) | ~l1_lattices(X1) | v2_struct_0(X1)) )),
% 9.32/1.55    inference(duplicate_literal_removal,[],[f185])).
% 9.32/1.55  fof(f185,plain,(
% 9.32/1.55    ( ! [X1] : (sP3(X1,k5_lattices(X1)) | ~v13_lattices(X1) | ~l1_lattices(X1) | v2_struct_0(X1) | ~l1_lattices(X1) | v2_struct_0(X1)) )),
% 9.32/1.55    inference(resolution,[],[f113,f106])).
% 9.32/1.55  fof(f113,plain,(
% 9.32/1.55    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP3(X0,X1) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 9.32/1.55    inference(cnf_transformation,[],[f56])).
% 9.32/1.55  fof(f56,plain,(
% 9.32/1.55    ! [X0] : (! [X1] : (sP3(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 9.32/1.55    inference(definition_folding,[],[f37,f55,f54])).
% 9.32/1.55  fof(f37,plain,(
% 9.32/1.55    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 9.32/1.55    inference(flattening,[],[f36])).
% 9.32/1.55  fof(f36,plain,(
% 9.32/1.55    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 9.32/1.55    inference(ennf_transformation,[],[f5])).
% 9.32/1.55  fof(f5,axiom,(
% 9.32/1.55    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 9.32/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 9.32/1.55  fof(f2220,plain,(
% 9.32/1.55    ( ! [X1] : (sK10(sK7) = k2_lattices(sK7,k15_lattice3(sK7,X1),sK10(sK7))) ) | ~spl12_2),
% 9.32/1.55    inference(subsumption_resolution,[],[f2219,f85])).
% 9.32/1.55  fof(f2219,plain,(
% 9.32/1.55    ( ! [X1] : (v2_struct_0(sK7) | sK10(sK7) = k2_lattices(sK7,k15_lattice3(sK7,X1),sK10(sK7))) ) | ~spl12_2),
% 9.32/1.55    inference(subsumption_resolution,[],[f2073,f88])).
% 9.32/1.55  fof(f2073,plain,(
% 9.32/1.55    ( ! [X1] : (~l3_lattices(sK7) | v2_struct_0(sK7) | sK10(sK7) = k2_lattices(sK7,k15_lattice3(sK7,X1),sK10(sK7))) ) | ~spl12_2),
% 9.32/1.55    inference(resolution,[],[f151,f239])).
% 9.32/1.55  fof(f239,plain,(
% 9.32/1.55    ( ! [X0,X1] : (~sP5(X0) | ~l3_lattices(X0) | v2_struct_0(X0) | sK10(X0) = k2_lattices(X0,k15_lattice3(X0,X1),sK10(X0))) )),
% 9.32/1.55    inference(resolution,[],[f210,f117])).
% 9.32/1.55  fof(f210,plain,(
% 9.32/1.55    ( ! [X6,X4,X5] : (~sP4(X6,X4) | k2_lattices(X4,k15_lattice3(X4,X5),X6) = X6 | ~l3_lattices(X4) | v2_struct_0(X4)) )),
% 9.32/1.55    inference(resolution,[],[f120,f125])).
% 9.32/1.55  fof(f2706,plain,(
% 9.32/1.55    k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | ~spl12_3),
% 9.32/1.55    inference(forward_demodulation,[],[f2705,f2529])).
% 9.32/1.55  fof(f2705,plain,(
% 9.32/1.55    k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) | ~spl12_3),
% 9.32/1.55    inference(subsumption_resolution,[],[f2704,f85])).
% 9.32/1.55  fof(f2704,plain,(
% 9.32/1.55    k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) | v2_struct_0(sK7) | ~spl12_3),
% 9.32/1.55    inference(subsumption_resolution,[],[f2703,f160])).
% 9.32/1.55  fof(f2703,plain,(
% 9.32/1.55    k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) | ~v6_lattices(sK7) | v2_struct_0(sK7) | ~spl12_3),
% 9.32/1.55    inference(subsumption_resolution,[],[f2692,f137])).
% 9.32/1.55  fof(f2692,plain,(
% 9.32/1.55    k2_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) = k4_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) | ~l1_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7) | ~spl12_3),
% 9.32/1.55    inference(resolution,[],[f1271,f1865])).
% 9.32/1.55  fof(f1271,plain,(
% 9.32/1.55    ( ! [X4,X5] : (~m1_subset_1(X5,u1_struct_0(X4)) | k4_lattices(X4,X5,k5_lattices(X4)) = k2_lattices(X4,X5,k5_lattices(X4)) | ~l1_lattices(X4) | ~v6_lattices(X4) | v2_struct_0(X4)) )),
% 9.32/1.55    inference(duplicate_literal_removal,[],[f1259])).
% 9.32/1.55  fof(f1259,plain,(
% 9.32/1.55    ( ! [X4,X5] : (k4_lattices(X4,X5,k5_lattices(X4)) = k2_lattices(X4,X5,k5_lattices(X4)) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~l1_lattices(X4) | ~v6_lattices(X4) | v2_struct_0(X4) | ~l1_lattices(X4) | v2_struct_0(X4)) )),
% 9.32/1.55    inference(resolution,[],[f133,f106])).
% 9.32/1.55  fof(f2875,plain,(
% 9.32/1.55    k5_lattices(sK7) = k15_lattice3(sK7,k1_xboole_0) | ~r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))) | (~spl12_2 | ~spl12_3)),
% 9.32/1.55    inference(forward_demodulation,[],[f2874,f2865])).
% 9.32/1.55  fof(f2874,plain,(
% 9.32/1.55    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | ~r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))) | (~spl12_2 | ~spl12_3)),
% 9.32/1.55    inference(subsumption_resolution,[],[f2869,f326])).
% 9.32/1.55  fof(f2869,plain,(
% 9.32/1.55    ~m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) | k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | ~r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))) | (~spl12_2 | ~spl12_3)),
% 9.32/1.55    inference(backward_demodulation,[],[f2742,f2865])).
% 9.32/1.55  fof(f2742,plain,(
% 9.32/1.55    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | ~r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))) | ~m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7)) | ~spl12_3),
% 9.32/1.55    inference(subsumption_resolution,[],[f2741,f85])).
% 9.32/1.55  fof(f2741,plain,(
% 9.32/1.55    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | ~r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))) | ~m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7)) | v2_struct_0(sK7) | ~spl12_3),
% 9.32/1.55    inference(subsumption_resolution,[],[f2740,f161])).
% 9.32/1.55  fof(f2740,plain,(
% 9.32/1.55    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | ~r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))) | ~m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7)) | ~v4_lattices(sK7) | v2_struct_0(sK7) | ~spl12_3),
% 9.32/1.55    inference(subsumption_resolution,[],[f2739,f138])).
% 9.32/1.55  fof(f2739,plain,(
% 9.32/1.55    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | ~r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))) | ~m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7)) | ~l2_lattices(sK7) | ~v4_lattices(sK7) | v2_struct_0(sK7) | ~spl12_3),
% 9.32/1.55    inference(subsumption_resolution,[],[f2732,f1865])).
% 9.32/1.55  fof(f2732,plain,(
% 9.32/1.55    k15_lattice3(sK7,k1_xboole_0) = k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)) | ~r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0))) | ~m1_subset_1(k4_lattices(sK7,k5_lattices(sK7),k15_lattice3(sK7,k1_xboole_0)),u1_struct_0(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~l2_lattices(sK7) | ~v4_lattices(sK7) | v2_struct_0(sK7) | ~spl12_3),
% 9.32/1.55    inference(resolution,[],[f2683,f98])).
% 9.32/1.55  fof(f2056,plain,(
% 9.32/1.55    k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0) | ~v13_lattices(sK7)),
% 9.32/1.55    inference(subsumption_resolution,[],[f2055,f85])).
% 9.32/1.55  fof(f2055,plain,(
% 9.32/1.55    k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0) | ~v13_lattices(sK7) | v2_struct_0(sK7)),
% 9.32/1.55    inference(subsumption_resolution,[],[f2054,f86])).
% 9.32/1.55  fof(f2054,plain,(
% 9.32/1.55    k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0) | ~v13_lattices(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7)),
% 9.32/1.55    inference(subsumption_resolution,[],[f89,f88])).
% 9.32/1.55  fof(f89,plain,(
% 9.32/1.55    k5_lattices(sK7) != k15_lattice3(sK7,k1_xboole_0) | ~l3_lattices(sK7) | ~v13_lattices(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7)),
% 9.32/1.55    inference(cnf_transformation,[],[f62])).
% 9.32/1.55  fof(f151,plain,(
% 9.32/1.55    sP5(sK7) | ~spl12_2),
% 9.32/1.55    inference(avatar_component_clause,[],[f150])).
% 9.32/1.55  fof(f143,plain,(
% 9.32/1.55    ~sP5(sK7) | v13_lattices(sK7)),
% 9.32/1.55    inference(resolution,[],[f142,f115])).
% 9.32/1.55  fof(f115,plain,(
% 9.32/1.55    ( ! [X0] : (~sP6(X0) | ~sP5(X0) | v13_lattices(X0)) )),
% 9.32/1.55    inference(cnf_transformation,[],[f73])).
% 9.32/1.55  fof(f73,plain,(
% 9.32/1.55    ! [X0] : (((v13_lattices(X0) | ~sP5(X0)) & (sP5(X0) | ~v13_lattices(X0))) | ~sP6(X0))),
% 9.32/1.55    inference(nnf_transformation,[],[f59])).
% 9.32/1.55  fof(f59,plain,(
% 9.32/1.55    ! [X0] : ((v13_lattices(X0) <=> sP5(X0)) | ~sP6(X0))),
% 9.32/1.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 9.32/1.55  fof(f142,plain,(
% 9.32/1.55    sP6(sK7)),
% 9.32/1.55    inference(subsumption_resolution,[],[f141,f85])).
% 9.32/1.55  fof(f141,plain,(
% 9.32/1.55    sP6(sK7) | v2_struct_0(sK7)),
% 9.32/1.55    inference(resolution,[],[f123,f137])).
% 9.32/1.55  fof(f123,plain,(
% 9.32/1.55    ( ! [X0] : (~l1_lattices(X0) | sP6(X0) | v2_struct_0(X0)) )),
% 9.32/1.55    inference(cnf_transformation,[],[f60])).
% 9.32/1.55  fof(f60,plain,(
% 9.32/1.55    ! [X0] : (sP6(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 9.32/1.55    inference(definition_folding,[],[f39,f59,f58,f57])).
% 9.32/1.55  fof(f39,plain,(
% 9.32/1.55    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 9.32/1.55    inference(flattening,[],[f38])).
% 9.32/1.55  fof(f38,plain,(
% 9.32/1.55    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 9.32/1.55    inference(ennf_transformation,[],[f13])).
% 9.32/1.55  fof(f13,axiom,(
% 9.32/1.55    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 9.32/1.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).
% 9.32/1.55  fof(f1875,plain,(
% 9.32/1.55    spl12_3),
% 9.32/1.55    inference(avatar_contradiction_clause,[],[f1874])).
% 9.32/1.55  fof(f1874,plain,(
% 9.32/1.55    $false | spl12_3),
% 9.32/1.55    inference(subsumption_resolution,[],[f1873,f85])).
% 9.32/1.55  fof(f1873,plain,(
% 9.32/1.55    v2_struct_0(sK7) | spl12_3),
% 9.32/1.55    inference(subsumption_resolution,[],[f1872,f88])).
% 9.32/1.55  fof(f1872,plain,(
% 9.32/1.55    ~l3_lattices(sK7) | v2_struct_0(sK7) | spl12_3),
% 9.32/1.55    inference(resolution,[],[f1866,f125])).
% 9.32/1.55  fof(f1866,plain,(
% 9.32/1.55    ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | spl12_3),
% 9.32/1.55    inference(avatar_component_clause,[],[f1864])).
% 9.32/1.55  fof(f1871,plain,(
% 9.32/1.55    ~spl12_3 | spl12_4),
% 9.32/1.55    inference(avatar_split_clause,[],[f1821,f1868,f1864])).
% 9.32/1.55  fof(f1821,plain,(
% 9.32/1.55    r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7))),
% 9.32/1.55    inference(subsumption_resolution,[],[f1820,f85])).
% 9.32/1.55  fof(f1820,plain,(
% 9.32/1.55    r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | v2_struct_0(sK7)),
% 9.32/1.55    inference(subsumption_resolution,[],[f1819,f160])).
% 9.32/1.55  fof(f1819,plain,(
% 9.32/1.55    r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~v6_lattices(sK7) | v2_struct_0(sK7)),
% 9.32/1.55    inference(subsumption_resolution,[],[f1818,f159])).
% 9.32/1.55  fof(f1818,plain,(
% 9.32/1.55    r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7)),
% 9.32/1.55    inference(subsumption_resolution,[],[f1817,f158])).
% 9.32/1.55  fof(f1817,plain,(
% 9.32/1.55    r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~v9_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7)),
% 9.32/1.55    inference(subsumption_resolution,[],[f1816,f88])).
% 9.32/1.55  fof(f1816,plain,(
% 9.32/1.55    r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~l3_lattices(sK7) | ~v9_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7)),
% 9.32/1.55    inference(subsumption_resolution,[],[f1805,f326])).
% 9.32/1.55  fof(f1805,plain,(
% 9.32/1.55    r1_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7)) | ~m1_subset_1(k5_lattices(sK7),u1_struct_0(sK7)) | ~m1_subset_1(k15_lattice3(sK7,k1_xboole_0),u1_struct_0(sK7)) | ~l3_lattices(sK7) | ~v9_lattices(sK7) | ~v8_lattices(sK7) | ~v6_lattices(sK7) | v2_struct_0(sK7)),
% 9.32/1.55    inference(resolution,[],[f129,f478])).
% 9.32/1.55  fof(f478,plain,(
% 9.32/1.55    r3_lattices(sK7,k15_lattice3(sK7,k1_xboole_0),k5_lattices(sK7))),
% 9.32/1.55    inference(resolution,[],[f469,f167])).
% 9.32/1.55  fof(f469,plain,(
% 9.32/1.55    ( ! [X0] : (sP1(a_2_3_lattice3(sK7,k5_lattices(sK7)),sK7,X0) | r3_lattices(sK7,k15_lattice3(sK7,X0),k5_lattices(sK7))) )),
% 9.32/1.55    inference(subsumption_resolution,[],[f468,f85])).
% 9.32/1.55  fof(f468,plain,(
% 9.32/1.55    ( ! [X0] : (r3_lattices(sK7,k15_lattice3(sK7,X0),k5_lattices(sK7)) | sP1(a_2_3_lattice3(sK7,k5_lattices(sK7)),sK7,X0) | v2_struct_0(sK7)) )),
% 9.32/1.55    inference(subsumption_resolution,[],[f467,f86])).
% 9.32/1.55  fof(f467,plain,(
% 9.32/1.55    ( ! [X0] : (r3_lattices(sK7,k15_lattice3(sK7,X0),k5_lattices(sK7)) | sP1(a_2_3_lattice3(sK7,k5_lattices(sK7)),sK7,X0) | ~v10_lattices(sK7) | v2_struct_0(sK7)) )),
% 9.32/1.55    inference(subsumption_resolution,[],[f466,f87])).
% 9.32/1.55  fof(f466,plain,(
% 9.32/1.55    ( ! [X0] : (r3_lattices(sK7,k15_lattice3(sK7,X0),k5_lattices(sK7)) | sP1(a_2_3_lattice3(sK7,k5_lattices(sK7)),sK7,X0) | ~v4_lattice3(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7)) )),
% 9.32/1.55    inference(subsumption_resolution,[],[f456,f88])).
% 9.32/1.55  fof(f456,plain,(
% 9.32/1.55    ( ! [X0] : (r3_lattices(sK7,k15_lattice3(sK7,X0),k5_lattices(sK7)) | sP1(a_2_3_lattice3(sK7,k5_lattices(sK7)),sK7,X0) | ~l3_lattices(sK7) | ~v4_lattice3(sK7) | ~v10_lattices(sK7) | v2_struct_0(sK7)) )),
% 9.32/1.55    inference(superposition,[],[f104,f317])).
% 9.32/1.55  % SZS output end Proof for theBenchmark
% 9.32/1.55  % (10447)------------------------------
% 9.32/1.55  % (10447)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.32/1.55  % (10447)Termination reason: Refutation
% 9.32/1.55  
% 9.32/1.55  % (10447)Memory used [KB]: 22899
% 9.32/1.55  % (10447)Time elapsed: 1.108 s
% 9.32/1.55  % (10447)------------------------------
% 9.32/1.55  % (10447)------------------------------
% 9.32/1.55  % (10417)Success in time 1.19 s
%------------------------------------------------------------------------------
