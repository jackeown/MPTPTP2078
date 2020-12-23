%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 585 expanded)
%              Number of leaves         :   26 ( 205 expanded)
%              Depth                    :   30
%              Number of atoms          : 1038 (5158 expanded)
%              Number of equality atoms :   54 ( 489 expanded)
%              Maximal formula depth    :   19 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f407,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f297,f315,f351,f361,f400])).

fof(f400,plain,
    ( ~ spl14_3
    | spl14_5 ),
    inference(avatar_contradiction_clause,[],[f399])).

fof(f399,plain,
    ( $false
    | ~ spl14_3
    | spl14_5 ),
    inference(subsumption_resolution,[],[f398,f66])).

fof(f66,plain,(
    l3_lattices(sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( k4_filter_0(sK8,sK9,sK10) != k15_lattice3(sK8,a_3_6_lattice3(sK8,sK9,sK10))
    & l3_lattices(sK8)
    & v3_filter_0(sK8)
    & v10_lattices(sK8)
    & ~ v2_struct_0(sK8)
    & m1_subset_1(sK10,u1_struct_0(sK8))
    & m1_subset_1(sK9,u1_struct_0(sK8))
    & l3_lattices(sK8)
    & v4_lattice3(sK8)
    & v10_lattices(sK8)
    & ~ v2_struct_0(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f11,f40,f39,f38])).

fof(f38,plain,
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
              ( k4_filter_0(sK8,X1,X2) != k15_lattice3(sK8,a_3_6_lattice3(sK8,X1,X2))
              & l3_lattices(sK8)
              & v3_filter_0(sK8)
              & v10_lattices(sK8)
              & ~ v2_struct_0(sK8)
              & m1_subset_1(X2,u1_struct_0(sK8)) )
          & m1_subset_1(X1,u1_struct_0(sK8)) )
      & l3_lattices(sK8)
      & v4_lattice3(sK8)
      & v10_lattices(sK8)
      & ~ v2_struct_0(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k4_filter_0(sK8,X1,X2) != k15_lattice3(sK8,a_3_6_lattice3(sK8,X1,X2))
            & l3_lattices(sK8)
            & v3_filter_0(sK8)
            & v10_lattices(sK8)
            & ~ v2_struct_0(sK8)
            & m1_subset_1(X2,u1_struct_0(sK8)) )
        & m1_subset_1(X1,u1_struct_0(sK8)) )
   => ( ? [X2] :
          ( k4_filter_0(sK8,sK9,X2) != k15_lattice3(sK8,a_3_6_lattice3(sK8,sK9,X2))
          & l3_lattices(sK8)
          & v3_filter_0(sK8)
          & v10_lattices(sK8)
          & ~ v2_struct_0(sK8)
          & m1_subset_1(X2,u1_struct_0(sK8)) )
      & m1_subset_1(sK9,u1_struct_0(sK8)) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( k4_filter_0(sK8,sK9,X2) != k15_lattice3(sK8,a_3_6_lattice3(sK8,sK9,X2))
        & l3_lattices(sK8)
        & v3_filter_0(sK8)
        & v10_lattices(sK8)
        & ~ v2_struct_0(sK8)
        & m1_subset_1(X2,u1_struct_0(sK8)) )
   => ( k4_filter_0(sK8,sK9,sK10) != k15_lattice3(sK8,a_3_6_lattice3(sK8,sK9,sK10))
      & l3_lattices(sK8)
      & v3_filter_0(sK8)
      & v10_lattices(sK8)
      & ~ v2_struct_0(sK8)
      & m1_subset_1(sK10,u1_struct_0(sK8)) ) ),
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

fof(f398,plain,
    ( ~ l3_lattices(sK8)
    | ~ spl14_3
    | spl14_5 ),
    inference(subsumption_resolution,[],[f397,f67])).

fof(f67,plain,(
    m1_subset_1(sK9,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f41])).

fof(f397,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ spl14_3
    | spl14_5 ),
    inference(subsumption_resolution,[],[f396,f68])).

fof(f68,plain,(
    m1_subset_1(sK10,u1_struct_0(sK8)) ),
    inference(cnf_transformation,[],[f41])).

fof(f396,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ spl14_3
    | spl14_5 ),
    inference(subsumption_resolution,[],[f395,f63])).

fof(f63,plain,(
    ~ v2_struct_0(sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f395,plain,
    ( v2_struct_0(sK8)
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ spl14_3
    | spl14_5 ),
    inference(subsumption_resolution,[],[f394,f64])).

fof(f64,plain,(
    v10_lattices(sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f394,plain,
    ( ~ v10_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ spl14_3
    | spl14_5 ),
    inference(subsumption_resolution,[],[f389,f71])).

fof(f71,plain,(
    v3_filter_0(sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f389,plain,
    ( ~ v3_filter_0(sK8)
    | ~ v10_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ spl14_3
    | spl14_5 ),
    inference(resolution,[],[f379,f198])).

fof(f198,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X2,X0,k4_filter_0(X0,X1,X2))
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f196,f102])).

fof(f102,plain,(
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

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP2(X1,X2,X0,k4_filter_0(X0,X1,X2)) ) ),
    inference(resolution,[],[f112,f110])).

fof(f110,plain,(
    ! [X2,X3,X1] :
      ( ~ sP3(k4_filter_0(X1,X3,X2),X1,X2,X3)
      | sP2(X3,X2,X1,k4_filter_0(X1,X3,X2)) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X3,X2,X1,X0)
      | k4_filter_0(X1,X3,X2) != X0
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k4_filter_0(X1,X3,X2) = X0
          | ~ sP2(X3,X2,X1,X0) )
        & ( sP2(X3,X2,X1,X0)
          | k4_filter_0(X1,X3,X2) != X0 ) )
      | ~ sP3(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f43])).

fof(f43,plain,(
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

fof(f112,plain,(
    ! [X2,X0,X3,X1] :
      ( sP3(X3,X0,X2,X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f92])).

fof(f92,plain,(
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
    inference(definition_folding,[],[f17,f30,f29,f28])).

fof(f28,plain,(
    ! [X3,X0,X2,X1] :
      ( sP1(X3,X0,X2,X1)
    <=> ! [X4] :
          ( r3_lattices(X0,X4,X3)
          | ~ r3_lattices(X0,k4_lattices(X0,X1,X4),X2)
          | ~ m1_subset_1(X4,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
    ! [X1,X2,X0,X3] :
      ( sP2(X1,X2,X0,X3)
    <=> ( sP1(X3,X0,X2,X1)
        & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f379,plain,
    ( ~ sP2(sK9,sK10,sK8,k4_filter_0(sK8,sK9,sK10))
    | ~ spl14_3
    | spl14_5 ),
    inference(subsumption_resolution,[],[f376,f279])).

fof(f279,plain,
    ( m1_subset_1(k4_filter_0(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl14_3
  <=> m1_subset_1(k4_filter_0(sK8,sK9,sK10),u1_struct_0(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f376,plain,
    ( ~ m1_subset_1(k4_filter_0(sK8,sK9,sK10),u1_struct_0(sK8))
    | ~ sP2(sK9,sK10,sK8,k4_filter_0(sK8,sK9,sK10))
    | spl14_5 ),
    inference(resolution,[],[f350,f143])).

fof(f143,plain,(
    ! [X6,X4,X7,X5] :
      ( sP6(X4,X5,X6,X7)
      | ~ m1_subset_1(X7,u1_struct_0(X6))
      | ~ sP2(X5,X4,X6,X7) ) ),
    inference(resolution,[],[f111,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X2,k4_lattices(X2,X0,X3),X1)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP2(X0,X1,X2,X3)
        | ~ sP1(X3,X2,X1,X0)
        | ~ r3_lattices(X2,k4_lattices(X2,X0,X3),X1) )
      & ( ( sP1(X3,X2,X1,X0)
          & r3_lattices(X2,k4_lattices(X2,X0,X3),X1) )
        | ~ sP2(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X2,X0,X3] :
      ( ( sP2(X1,X2,X0,X3)
        | ~ sP1(X3,X0,X2,X1)
        | ~ r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
      & ( ( sP1(X3,X0,X2,X1)
          & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
        | ~ sP2(X1,X2,X0,X3) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X1,X2,X0,X3] :
      ( ( sP2(X1,X2,X0,X3)
        | ~ sP1(X3,X0,X2,X1)
        | ~ r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
      & ( ( sP1(X3,X0,X2,X1)
          & r3_lattices(X0,k4_lattices(X0,X1,X3),X2) )
        | ~ sP2(X1,X2,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f111,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r3_lattices(X2,k4_lattices(X2,X1,X4),X0)
      | sP6(X0,X1,X2,X4)
      | ~ m1_subset_1(X4,u1_struct_0(X2)) ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP6(X0,X1,X2,X3)
      | ~ r3_lattices(X2,k4_lattices(X2,X1,X4),X0)
      | X3 != X4
      | ~ m1_subset_1(X4,u1_struct_0(X2)) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP6(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r3_lattices(X2,k4_lattices(X2,X1,X4),X0)
            | X3 != X4
            | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
      & ( ( r3_lattices(X2,k4_lattices(X2,X1,sK13(X0,X1,X2,X3)),X0)
          & sK13(X0,X1,X2,X3) = X3
          & m1_subset_1(sK13(X0,X1,X2,X3),u1_struct_0(X2)) )
        | ~ sP6(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f60,f61])).

fof(f61,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( r3_lattices(X2,k4_lattices(X2,X1,X5),X0)
          & X3 = X5
          & m1_subset_1(X5,u1_struct_0(X2)) )
     => ( r3_lattices(X2,k4_lattices(X2,X1,sK13(X0,X1,X2,X3)),X0)
        & sK13(X0,X1,X2,X3) = X3
        & m1_subset_1(sK13(X0,X1,X2,X3),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP6(X0,X1,X2,X3)
        | ! [X4] :
            ( ~ r3_lattices(X2,k4_lattices(X2,X1,X4),X0)
            | X3 != X4
            | ~ m1_subset_1(X4,u1_struct_0(X2)) ) )
      & ( ? [X5] :
            ( r3_lattices(X2,k4_lattices(X2,X1,X5),X0)
            & X3 = X5
            & m1_subset_1(X5,u1_struct_0(X2)) )
        | ~ sP6(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f59])).

fof(f59,plain,(
    ! [X3,X2,X1,X0] :
      ( ( sP6(X3,X2,X1,X0)
        | ! [X4] :
            ( ~ r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
            | X0 != X4
            | ~ m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
            & X0 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP6(X3,X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X3,X2,X1,X0] :
      ( sP6(X3,X2,X1,X0)
    <=> ? [X4] :
          ( r3_lattices(X1,k4_lattices(X1,X2,X4),X3)
          & X0 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f350,plain,
    ( ~ sP6(sK10,sK9,sK8,k4_filter_0(sK8,sK9,sK10))
    | spl14_5 ),
    inference(avatar_component_clause,[],[f348])).

fof(f348,plain,
    ( spl14_5
  <=> sP6(sK10,sK9,sK8,k4_filter_0(sK8,sK9,sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f361,plain,(
    spl14_4 ),
    inference(avatar_contradiction_clause,[],[f360])).

fof(f360,plain,
    ( $false
    | spl14_4 ),
    inference(subsumption_resolution,[],[f359,f63])).

fof(f359,plain,
    ( v2_struct_0(sK8)
    | spl14_4 ),
    inference(subsumption_resolution,[],[f358,f64])).

fof(f358,plain,
    ( ~ v10_lattices(sK8)
    | v2_struct_0(sK8)
    | spl14_4 ),
    inference(subsumption_resolution,[],[f357,f65])).

fof(f65,plain,(
    v4_lattice3(sK8) ),
    inference(cnf_transformation,[],[f41])).

fof(f357,plain,
    ( ~ v4_lattice3(sK8)
    | ~ v10_lattices(sK8)
    | v2_struct_0(sK8)
    | spl14_4 ),
    inference(subsumption_resolution,[],[f356,f66])).

fof(f356,plain,
    ( ~ l3_lattices(sK8)
    | ~ v4_lattice3(sK8)
    | ~ v10_lattices(sK8)
    | v2_struct_0(sK8)
    | spl14_4 ),
    inference(subsumption_resolution,[],[f355,f67])).

fof(f355,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v4_lattice3(sK8)
    | ~ v10_lattices(sK8)
    | v2_struct_0(sK8)
    | spl14_4 ),
    inference(subsumption_resolution,[],[f352,f68])).

fof(f352,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v4_lattice3(sK8)
    | ~ v10_lattices(sK8)
    | v2_struct_0(sK8)
    | spl14_4 ),
    inference(resolution,[],[f346,f109])).

fof(f109,plain,(
    ! [X2,X0,X3,X1] :
      ( sP7(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( sP7(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f25,f36,f35])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      <=> sP6(X3,X2,X1,X0) )
      | ~ sP7(X0,X1,X2,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f346,plain,
    ( ~ sP7(k4_filter_0(sK8,sK9,sK10),sK8,sK9,sK10)
    | spl14_4 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl14_4
  <=> sP7(k4_filter_0(sK8,sK9,sK10),sK8,sK9,sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f351,plain,
    ( ~ spl14_4
    | ~ spl14_5
    | ~ spl14_1 ),
    inference(avatar_split_clause,[],[f342,f271,f348,f344])).

fof(f271,plain,
    ( spl14_1
  <=> sP1(k4_filter_0(sK8,sK9,sK10),sK8,sK10,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f342,plain,
    ( ~ sP6(sK10,sK9,sK8,k4_filter_0(sK8,sK9,sK10))
    | ~ sP7(k4_filter_0(sK8,sK9,sK10),sK8,sK9,sK10)
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f335,f272])).

fof(f272,plain,
    ( sP1(k4_filter_0(sK8,sK9,sK10),sK8,sK10,sK9)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f271])).

fof(f335,plain,
    ( ~ sP1(k4_filter_0(sK8,sK9,sK10),sK8,sK10,sK9)
    | ~ sP6(sK10,sK9,sK8,k4_filter_0(sK8,sK9,sK10))
    | ~ sP7(k4_filter_0(sK8,sK9,sK10),sK8,sK9,sK10) ),
    inference(equality_resolution,[],[f282])).

fof(f282,plain,(
    ! [X2] :
      ( k4_filter_0(sK8,sK9,sK10) != X2
      | ~ sP1(X2,sK8,sK10,sK9)
      | ~ sP6(sK10,sK9,sK8,X2)
      | ~ sP7(X2,sK8,sK9,sK10) ) ),
    inference(subsumption_resolution,[],[f268,f132])).

fof(f132,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X0,X1,X2,X3)
      | m1_subset_1(X3,u1_struct_0(X2)) ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(X3,u1_struct_0(X2))
      | ~ sP6(X0,X1,X2,X3)
      | ~ sP6(X0,X1,X2,X3) ) ),
    inference(superposition,[],[f105,f106])).

fof(f106,plain,(
    ! [X2,X0,X3,X1] :
      ( sK13(X0,X1,X2,X3) = X3
      | ~ sP6(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK13(X0,X1,X2,X3),u1_struct_0(X2))
      | ~ sP6(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f268,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK8))
      | k4_filter_0(sK8,sK9,sK10) != X2
      | ~ sP1(X2,sK8,sK10,sK9)
      | ~ sP6(sK10,sK9,sK8,X2)
      | ~ sP7(X2,sK8,sK9,sK10) ) ),
    inference(resolution,[],[f266,f104])).

fof(f104,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      | ~ sP6(X3,X2,X1,X0)
      | ~ sP7(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
          | ~ sP6(X3,X2,X1,X0) )
        & ( sP6(X3,X2,X1,X0)
          | ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) ) )
      | ~ sP7(X0,X1,X2,X3) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f266,plain,(
    ! [X10] :
      ( ~ r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10))
      | ~ m1_subset_1(X10,u1_struct_0(sK8))
      | k4_filter_0(sK8,sK9,sK10) != X10
      | ~ sP1(X10,sK8,sK10,sK9) ) ),
    inference(subsumption_resolution,[],[f265,f67])).

fof(f265,plain,(
    ! [X10] :
      ( ~ sP1(X10,sK8,sK10,sK9)
      | ~ m1_subset_1(X10,u1_struct_0(sK8))
      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
      | k4_filter_0(sK8,sK9,sK10) != X10
      | ~ r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10)) ) ),
    inference(subsumption_resolution,[],[f264,f68])).

fof(f264,plain,(
    ! [X10] :
      ( ~ sP1(X10,sK8,sK10,sK9)
      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
      | ~ m1_subset_1(X10,u1_struct_0(sK8))
      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
      | k4_filter_0(sK8,sK9,sK10) != X10
      | ~ r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10)) ) ),
    inference(subsumption_resolution,[],[f263,f63])).

fof(f263,plain,(
    ! [X10] :
      ( v2_struct_0(sK8)
      | ~ sP1(X10,sK8,sK10,sK9)
      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
      | ~ m1_subset_1(X10,u1_struct_0(sK8))
      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
      | k4_filter_0(sK8,sK9,sK10) != X10
      | ~ r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10)) ) ),
    inference(subsumption_resolution,[],[f262,f64])).

fof(f262,plain,(
    ! [X10] :
      ( ~ v10_lattices(sK8)
      | v2_struct_0(sK8)
      | ~ sP1(X10,sK8,sK10,sK9)
      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
      | ~ m1_subset_1(X10,u1_struct_0(sK8))
      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
      | k4_filter_0(sK8,sK9,sK10) != X10
      | ~ r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10)) ) ),
    inference(subsumption_resolution,[],[f261,f65])).

fof(f261,plain,(
    ! [X10] :
      ( ~ v4_lattice3(sK8)
      | ~ v10_lattices(sK8)
      | v2_struct_0(sK8)
      | ~ sP1(X10,sK8,sK10,sK9)
      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
      | ~ m1_subset_1(X10,u1_struct_0(sK8))
      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
      | k4_filter_0(sK8,sK9,sK10) != X10
      | ~ r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10)) ) ),
    inference(subsumption_resolution,[],[f258,f66])).

fof(f258,plain,(
    ! [X10] :
      ( ~ l3_lattices(sK8)
      | ~ v4_lattice3(sK8)
      | ~ v10_lattices(sK8)
      | v2_struct_0(sK8)
      | ~ sP1(X10,sK8,sK10,sK9)
      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
      | ~ m1_subset_1(X10,u1_struct_0(sK8))
      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
      | k4_filter_0(sK8,sK9,sK10) != X10
      | ~ r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10)) ) ),
    inference(duplicate_literal_removal,[],[f257])).

fof(f257,plain,(
    ! [X10] :
      ( ~ l3_lattices(sK8)
      | ~ v4_lattice3(sK8)
      | ~ v10_lattices(sK8)
      | v2_struct_0(sK8)
      | ~ sP1(X10,sK8,sK10,sK9)
      | ~ m1_subset_1(sK10,u1_struct_0(sK8))
      | ~ m1_subset_1(X10,u1_struct_0(sK8))
      | ~ m1_subset_1(sK9,u1_struct_0(sK8))
      | k4_filter_0(sK8,sK9,sK10) != X10
      | ~ r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10))
      | ~ m1_subset_1(X10,u1_struct_0(sK8)) ) ),
    inference(resolution,[],[f254,f189])).

fof(f189,plain,(
    ! [X0] :
      ( ~ r4_lattice3(sK8,X0,a_3_6_lattice3(sK8,sK9,sK10))
      | k4_filter_0(sK8,sK9,sK10) != X0
      | ~ r2_hidden(X0,a_3_6_lattice3(sK8,sK9,sK10))
      | ~ m1_subset_1(X0,u1_struct_0(sK8)) ) ),
    inference(subsumption_resolution,[],[f188,f63])).

fof(f188,plain,(
    ! [X0] :
      ( k4_filter_0(sK8,sK9,sK10) != X0
      | ~ r4_lattice3(sK8,X0,a_3_6_lattice3(sK8,sK9,sK10))
      | ~ r2_hidden(X0,a_3_6_lattice3(sK8,sK9,sK10))
      | ~ m1_subset_1(X0,u1_struct_0(sK8))
      | v2_struct_0(sK8) ) ),
    inference(subsumption_resolution,[],[f187,f64])).

fof(f187,plain,(
    ! [X0] :
      ( k4_filter_0(sK8,sK9,sK10) != X0
      | ~ r4_lattice3(sK8,X0,a_3_6_lattice3(sK8,sK9,sK10))
      | ~ r2_hidden(X0,a_3_6_lattice3(sK8,sK9,sK10))
      | ~ m1_subset_1(X0,u1_struct_0(sK8))
      | ~ v10_lattices(sK8)
      | v2_struct_0(sK8) ) ),
    inference(subsumption_resolution,[],[f186,f65])).

fof(f186,plain,(
    ! [X0] :
      ( k4_filter_0(sK8,sK9,sK10) != X0
      | ~ r4_lattice3(sK8,X0,a_3_6_lattice3(sK8,sK9,sK10))
      | ~ r2_hidden(X0,a_3_6_lattice3(sK8,sK9,sK10))
      | ~ m1_subset_1(X0,u1_struct_0(sK8))
      | ~ v4_lattice3(sK8)
      | ~ v10_lattices(sK8)
      | v2_struct_0(sK8) ) ),
    inference(subsumption_resolution,[],[f184,f66])).

fof(f184,plain,(
    ! [X0] :
      ( k4_filter_0(sK8,sK9,sK10) != X0
      | ~ r4_lattice3(sK8,X0,a_3_6_lattice3(sK8,sK9,sK10))
      | ~ r2_hidden(X0,a_3_6_lattice3(sK8,sK9,sK10))
      | ~ m1_subset_1(X0,u1_struct_0(sK8))
      | ~ l3_lattices(sK8)
      | ~ v4_lattice3(sK8)
      | ~ v10_lattices(sK8)
      | v2_struct_0(sK8) ) ),
    inference(superposition,[],[f73,f82])).

fof(f82,plain,(
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

fof(f73,plain,(
    k4_filter_0(sK8,sK9,sK10) != k15_lattice3(sK8,a_3_6_lattice3(sK8,sK9,sK10)) ),
    inference(cnf_transformation,[],[f41])).

fof(f254,plain,(
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
    inference(subsumption_resolution,[],[f253,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP5(X0,X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP5(X0,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f19,f33,f32])).

fof(f32,plain,(
    ! [X1,X0,X2] :
      ( sP4(X1,X0,X2)
    <=> ! [X3] :
          ( r1_lattices(X0,X3,X1)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r4_lattice3(X0,X1,X2)
        <=> sP4(X1,X0,X2) )
      | ~ sP5(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

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

fof(f253,plain,(
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
      | ~ sP5(X6,X7) ) ),
    inference(resolution,[],[f251,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ sP4(X1,X0,X2)
      | r4_lattice3(X0,X1,X2)
      | ~ sP5(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X0,X1,X2)
            | ~ sP4(X1,X0,X2) )
          & ( sP4(X1,X0,X2)
            | ~ r4_lattice3(X0,X1,X2) ) )
      | ~ sP5(X0,X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f251,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,a_3_6_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP1(X3,X1,X0,X2)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f250,f116])).

fof(f116,plain,(
    ! [X3] :
      ( v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3) ) ),
    inference(resolution,[],[f81,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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

fof(f81,plain,(
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

fof(f250,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP1(X3,X1,X0,X2)
      | sP4(X3,X1,a_3_6_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v6_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f249,f118])).

fof(f118,plain,(
    ! [X5] :
      ( v8_lattices(X5)
      | v2_struct_0(X5)
      | ~ l3_lattices(X5)
      | ~ v10_lattices(X5) ) ),
    inference(resolution,[],[f81,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f249,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP1(X3,X1,X0,X2)
      | sP4(X3,X1,a_3_6_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f248,f119])).

fof(f119,plain,(
    ! [X6] :
      ( v9_lattices(X6)
      | v2_struct_0(X6)
      | ~ l3_lattices(X6)
      | ~ v10_lattices(X6) ) ),
    inference(resolution,[],[f81,f80])).

fof(f80,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f248,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP1(X3,X1,X0,X2)
      | sP4(X3,X1,a_3_6_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ sP1(X3,X1,X0,X2)
      | sP4(X3,X1,a_3_6_lattice3(X1,X2,X0))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | sP4(X3,X1,a_3_6_lattice3(X1,X2,X0)) ) ),
    inference(resolution,[],[f214,f200])).

fof(f200,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,sK12(X1,X0,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP4(X1,X0,X2) ) ),
    inference(subsumption_resolution,[],[f199,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))
      | sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ~ r1_lattices(X1,sK12(X0,X1,X2),X0)
          & r2_hidden(sK12(X0,X1,X2),X2)
          & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,sK12(X0,X1,X2),X0)
        & r2_hidden(sK12(X0,X1,X2),X2)
        & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f32])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,sK12(X1,X0,X2),X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(sK12(X1,X0,X2),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | sP4(X1,X0,X2) ) ),
    inference(resolution,[],[f100,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,sK12(X0,X1,X2),X0)
      | sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f100,plain,(
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
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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

fof(f214,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r3_lattices(X2,sK12(X0,X1,a_3_6_lattice3(X2,X3,X4)),X5)
      | ~ m1_subset_1(X4,u1_struct_0(X2))
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ sP1(X5,X2,X4,X3)
      | sP4(X0,X1,a_3_6_lattice3(X2,X3,X4)) ) ),
    inference(resolution,[],[f212,f166])).

fof(f166,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP6(X3,X4,X0,X1)
      | ~ sP1(X2,X0,X3,X4)
      | r3_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f162,f132])).

fof(f162,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ sP1(X2,X0,X3,X4)
      | ~ sP6(X3,X4,X0,X1) ) ),
    inference(resolution,[],[f88,f139])).

fof(f139,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X2,k4_lattices(X2,X1,X3),X0)
      | ~ sP6(X0,X1,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X2,k4_lattices(X2,X1,X3),X0)
      | ~ sP6(X0,X1,X2,X3)
      | ~ sP6(X0,X1,X2,X3) ) ),
    inference(superposition,[],[f107,f106])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( r3_lattices(X2,k4_lattices(X2,X1,sK13(X0,X1,X2,X3)),X0)
      | ~ sP6(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f88,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( ~ r3_lattices(X1,k4_lattices(X1,X3,X5),X2)
      | r3_lattices(X1,X5,X0)
      | ~ m1_subset_1(X5,u1_struct_0(X1))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ~ r3_lattices(X1,sK11(X0,X1,X2,X3),X0)
          & r3_lattices(X1,k4_lattices(X1,X3,sK11(X0,X1,X2,X3)),X2)
          & m1_subset_1(sK11(X0,X1,X2,X3),u1_struct_0(X1)) ) )
      & ( ! [X5] :
            ( r3_lattices(X1,X5,X0)
            | ~ r3_lattices(X1,k4_lattices(X1,X3,X5),X2)
            | ~ m1_subset_1(X5,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f49,f50])).

fof(f50,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ~ r3_lattices(X1,X4,X0)
          & r3_lattices(X1,k4_lattices(X1,X3,X4),X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r3_lattices(X1,sK11(X0,X1,X2,X3),X0)
        & r3_lattices(X1,k4_lattices(X1,X3,sK11(X0,X1,X2,X3)),X2)
        & m1_subset_1(sK11(X0,X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f48,plain,(
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

fof(f212,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( sP6(X0,X1,X2,sK12(X3,X4,a_3_6_lattice3(X2,X1,X0)))
      | sP4(X3,X4,a_3_6_lattice3(X2,X1,X0))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ m1_subset_1(X1,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(resolution,[],[f135,f109])).

fof(f135,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP7(sK12(X3,X4,a_3_6_lattice3(X2,X1,X0)),X2,X1,X0)
      | sP6(X0,X1,X2,sK12(X3,X4,a_3_6_lattice3(X2,X1,X0)))
      | sP4(X3,X4,a_3_6_lattice3(X2,X1,X0)) ) ),
    inference(resolution,[],[f103,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK12(X0,X1,X2),X2)
      | sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,a_3_6_lattice3(X1,X2,X3))
      | sP6(X3,X2,X1,X0)
      | ~ sP7(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f315,plain,(
    spl14_3 ),
    inference(avatar_contradiction_clause,[],[f314])).

fof(f314,plain,
    ( $false
    | spl14_3 ),
    inference(subsumption_resolution,[],[f313,f63])).

fof(f313,plain,
    ( v2_struct_0(sK8)
    | spl14_3 ),
    inference(subsumption_resolution,[],[f312,f64])).

fof(f312,plain,
    ( ~ v10_lattices(sK8)
    | v2_struct_0(sK8)
    | spl14_3 ),
    inference(subsumption_resolution,[],[f311,f66])).

fof(f311,plain,
    ( ~ l3_lattices(sK8)
    | ~ v10_lattices(sK8)
    | v2_struct_0(sK8)
    | spl14_3 ),
    inference(subsumption_resolution,[],[f310,f67])).

fof(f310,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v10_lattices(sK8)
    | v2_struct_0(sK8)
    | spl14_3 ),
    inference(subsumption_resolution,[],[f306,f68])).

fof(f306,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v10_lattices(sK8)
    | v2_struct_0(sK8)
    | spl14_3 ),
    inference(resolution,[],[f280,f102])).

fof(f280,plain,
    ( ~ m1_subset_1(k4_filter_0(sK8,sK9,sK10),u1_struct_0(sK8))
    | spl14_3 ),
    inference(avatar_component_clause,[],[f278])).

fof(f297,plain,(
    spl14_1 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | spl14_1 ),
    inference(subsumption_resolution,[],[f295,f71])).

fof(f295,plain,
    ( ~ v3_filter_0(sK8)
    | spl14_1 ),
    inference(subsumption_resolution,[],[f294,f66])).

fof(f294,plain,
    ( ~ l3_lattices(sK8)
    | ~ v3_filter_0(sK8)
    | spl14_1 ),
    inference(subsumption_resolution,[],[f293,f67])).

fof(f293,plain,
    ( ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v3_filter_0(sK8)
    | spl14_1 ),
    inference(subsumption_resolution,[],[f292,f68])).

fof(f292,plain,
    ( ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v3_filter_0(sK8)
    | spl14_1 ),
    inference(subsumption_resolution,[],[f291,f63])).

fof(f291,plain,
    ( v2_struct_0(sK8)
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v3_filter_0(sK8)
    | spl14_1 ),
    inference(subsumption_resolution,[],[f288,f64])).

fof(f288,plain,
    ( ~ v10_lattices(sK8)
    | v2_struct_0(sK8)
    | ~ m1_subset_1(sK10,u1_struct_0(sK8))
    | ~ m1_subset_1(sK9,u1_struct_0(sK8))
    | ~ l3_lattices(sK8)
    | ~ v3_filter_0(sK8)
    | spl14_1 ),
    inference(resolution,[],[f273,f202])).

fof(f202,plain,(
    ! [X6,X4,X5] :
      ( sP1(k4_filter_0(X4,X6,X5),X4,X5,X6)
      | ~ v10_lattices(X4)
      | v2_struct_0(X4)
      | ~ m1_subset_1(X5,u1_struct_0(X4))
      | ~ m1_subset_1(X6,u1_struct_0(X4))
      | ~ l3_lattices(X4)
      | ~ v3_filter_0(X4) ) ),
    inference(resolution,[],[f198,f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | sP1(X3,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f273,plain,
    ( ~ sP1(k4_filter_0(sK8,sK9,sK10),sK8,sK10,sK9)
    | spl14_1 ),
    inference(avatar_component_clause,[],[f271])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:16:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (32039)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.47  % (32048)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.49  % (32038)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.20/0.50  % (32027)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.20/0.51  % (32044)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.20/0.51  % (32042)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.20/0.51  % (32045)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (32036)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.20/0.52  % (32049)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.52  % (32034)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.20/0.52  % (32031)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.52  % (32032)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.52  % (32041)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.52  % (32029)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.20/0.52  % (32030)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.20/0.52  % (32033)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.52  % (32046)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.52  % (32052)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.20/0.53  % (32040)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (32037)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.20/0.53  % (32043)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.54  % (32035)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.54  % (32050)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.20/0.54  % (32051)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.20/0.54  % (32028)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.55  % (32028)Refutation not found, incomplete strategy% (32028)------------------------------
% 0.20/0.55  % (32028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (32028)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (32028)Memory used [KB]: 10746
% 0.20/0.55  % (32028)Time elapsed: 0.133 s
% 0.20/0.55  % (32028)------------------------------
% 0.20/0.55  % (32028)------------------------------
% 0.20/0.56  % (32031)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f407,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f297,f315,f351,f361,f400])).
% 0.20/0.56  fof(f400,plain,(
% 0.20/0.56    ~spl14_3 | spl14_5),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f399])).
% 0.20/0.56  fof(f399,plain,(
% 0.20/0.56    $false | (~spl14_3 | spl14_5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f398,f66])).
% 0.20/0.56  fof(f66,plain,(
% 0.20/0.56    l3_lattices(sK8)),
% 0.20/0.56    inference(cnf_transformation,[],[f41])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ((k4_filter_0(sK8,sK9,sK10) != k15_lattice3(sK8,a_3_6_lattice3(sK8,sK9,sK10)) & l3_lattices(sK8) & v3_filter_0(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8) & m1_subset_1(sK10,u1_struct_0(sK8))) & m1_subset_1(sK9,u1_struct_0(sK8))) & l3_lattices(sK8) & v4_lattice3(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10])],[f11,f40,f39,f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : (k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (k4_filter_0(sK8,X1,X2) != k15_lattice3(sK8,a_3_6_lattice3(sK8,X1,X2)) & l3_lattices(sK8) & v3_filter_0(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8) & m1_subset_1(X2,u1_struct_0(sK8))) & m1_subset_1(X1,u1_struct_0(sK8))) & l3_lattices(sK8) & v4_lattice3(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ? [X1] : (? [X2] : (k4_filter_0(sK8,X1,X2) != k15_lattice3(sK8,a_3_6_lattice3(sK8,X1,X2)) & l3_lattices(sK8) & v3_filter_0(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8) & m1_subset_1(X2,u1_struct_0(sK8))) & m1_subset_1(X1,u1_struct_0(sK8))) => (? [X2] : (k4_filter_0(sK8,sK9,X2) != k15_lattice3(sK8,a_3_6_lattice3(sK8,sK9,X2)) & l3_lattices(sK8) & v3_filter_0(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8) & m1_subset_1(X2,u1_struct_0(sK8))) & m1_subset_1(sK9,u1_struct_0(sK8)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ? [X2] : (k4_filter_0(sK8,sK9,X2) != k15_lattice3(sK8,a_3_6_lattice3(sK8,sK9,X2)) & l3_lattices(sK8) & v3_filter_0(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8) & m1_subset_1(X2,u1_struct_0(sK8))) => (k4_filter_0(sK8,sK9,sK10) != k15_lattice3(sK8,a_3_6_lattice3(sK8,sK9,sK10)) & l3_lattices(sK8) & v3_filter_0(sK8) & v10_lattices(sK8) & ~v2_struct_0(sK8) & m1_subset_1(sK10,u1_struct_0(sK8)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f11,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : (k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f10])).
% 0.20/0.56  fof(f10,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (? [X2] : ((k4_filter_0(X0,X1,X2) != k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2)) & (l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,negated_conjecture,(
% 0.20/0.56    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => k4_filter_0(X0,X1,X2) = k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))))))),
% 0.20/0.56    inference(negated_conjecture,[],[f8])).
% 0.20/0.56  fof(f8,conjecture,(
% 0.20/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => k4_filter_0(X0,X1,X2) = k15_lattice3(X0,a_3_6_lattice3(X0,X1,X2))))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_lattice3)).
% 0.20/0.56  fof(f398,plain,(
% 0.20/0.56    ~l3_lattices(sK8) | (~spl14_3 | spl14_5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f397,f67])).
% 0.20/0.56  fof(f67,plain,(
% 0.20/0.56    m1_subset_1(sK9,u1_struct_0(sK8))),
% 0.20/0.56    inference(cnf_transformation,[],[f41])).
% 0.20/0.56  fof(f397,plain,(
% 0.20/0.56    ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~l3_lattices(sK8) | (~spl14_3 | spl14_5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f396,f68])).
% 0.20/0.56  fof(f68,plain,(
% 0.20/0.56    m1_subset_1(sK10,u1_struct_0(sK8))),
% 0.20/0.56    inference(cnf_transformation,[],[f41])).
% 0.20/0.56  fof(f396,plain,(
% 0.20/0.56    ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~l3_lattices(sK8) | (~spl14_3 | spl14_5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f395,f63])).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    ~v2_struct_0(sK8)),
% 0.20/0.56    inference(cnf_transformation,[],[f41])).
% 0.20/0.56  fof(f395,plain,(
% 0.20/0.56    v2_struct_0(sK8) | ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~l3_lattices(sK8) | (~spl14_3 | spl14_5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f394,f64])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    v10_lattices(sK8)),
% 0.20/0.56    inference(cnf_transformation,[],[f41])).
% 0.20/0.56  fof(f394,plain,(
% 0.20/0.56    ~v10_lattices(sK8) | v2_struct_0(sK8) | ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~l3_lattices(sK8) | (~spl14_3 | spl14_5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f389,f71])).
% 0.20/0.56  fof(f71,plain,(
% 0.20/0.56    v3_filter_0(sK8)),
% 0.20/0.56    inference(cnf_transformation,[],[f41])).
% 0.20/0.56  fof(f389,plain,(
% 0.20/0.56    ~v3_filter_0(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8) | ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~l3_lattices(sK8) | (~spl14_3 | spl14_5)),
% 0.20/0.56    inference(resolution,[],[f379,f198])).
% 0.20/0.56  fof(f198,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (sP2(X1,X2,X0,k4_filter_0(X0,X1,X2)) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f196,f102])).
% 0.20/0.56  fof(f102,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_filter_0)).
% 0.20/0.56  fof(f196,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(k4_filter_0(X0,X1,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | sP2(X1,X2,X0,k4_filter_0(X0,X1,X2))) )),
% 0.20/0.56    inference(resolution,[],[f112,f110])).
% 0.20/0.56  fof(f110,plain,(
% 0.20/0.56    ( ! [X2,X3,X1] : (~sP3(k4_filter_0(X1,X3,X2),X1,X2,X3) | sP2(X3,X2,X1,k4_filter_0(X1,X3,X2))) )),
% 0.20/0.56    inference(equality_resolution,[],[f83])).
% 0.20/0.56  fof(f83,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (sP2(X3,X2,X1,X0) | k4_filter_0(X1,X3,X2) != X0 | ~sP3(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f44])).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (((k4_filter_0(X1,X3,X2) = X0 | ~sP2(X3,X2,X1,X0)) & (sP2(X3,X2,X1,X0) | k4_filter_0(X1,X3,X2) != X0)) | ~sP3(X0,X1,X2,X3))),
% 0.20/0.56    inference(rectify,[],[f43])).
% 0.20/0.56  fof(f43,plain,(
% 0.20/0.56    ! [X3,X0,X2,X1] : (((k4_filter_0(X0,X1,X2) = X3 | ~sP2(X1,X2,X0,X3)) & (sP2(X1,X2,X0,X3) | k4_filter_0(X0,X1,X2) != X3)) | ~sP3(X3,X0,X2,X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X3,X0,X2,X1] : ((k4_filter_0(X0,X1,X2) = X3 <=> sP2(X1,X2,X0,X3)) | ~sP3(X3,X0,X2,X1))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.20/0.56  fof(f112,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (sP3(X3,X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f92])).
% 0.20/0.56  fof(f92,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (sP3(X3,X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (sP3(X3,X0,X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(definition_folding,[],[f17,f30,f29,f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ! [X3,X0,X2,X1] : (sP1(X3,X0,X2,X1) <=> ! [X4] : (r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2) | ~m1_subset_1(X4,u1_struct_0(X0))))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X1,X2,X0,X3] : (sP2(X1,X2,X0,X3) <=> (sP1(X3,X0,X2,X1) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2)))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k4_filter_0(X0,X1,X2) = X3 <=> (! [X4] : (r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k4_filter_0(X0,X1,X2) = X3 <=> (! [X4] : ((r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2))) | ~m1_subset_1(X3,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v3_filter_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0] : ((l3_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((l3_lattices(X0) & v3_filter_0(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (k4_filter_0(X0,X1,X2) = X3 <=> (! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => (r3_lattices(X0,k4_lattices(X0,X1,X4),X2) => r3_lattices(X0,X4,X3))) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2))))))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_filter_0)).
% 0.20/0.56  fof(f379,plain,(
% 0.20/0.56    ~sP2(sK9,sK10,sK8,k4_filter_0(sK8,sK9,sK10)) | (~spl14_3 | spl14_5)),
% 0.20/0.56    inference(subsumption_resolution,[],[f376,f279])).
% 0.20/0.56  fof(f279,plain,(
% 0.20/0.56    m1_subset_1(k4_filter_0(sK8,sK9,sK10),u1_struct_0(sK8)) | ~spl14_3),
% 0.20/0.56    inference(avatar_component_clause,[],[f278])).
% 0.20/0.56  fof(f278,plain,(
% 0.20/0.56    spl14_3 <=> m1_subset_1(k4_filter_0(sK8,sK9,sK10),u1_struct_0(sK8))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).
% 0.20/0.56  fof(f376,plain,(
% 0.20/0.56    ~m1_subset_1(k4_filter_0(sK8,sK9,sK10),u1_struct_0(sK8)) | ~sP2(sK9,sK10,sK8,k4_filter_0(sK8,sK9,sK10)) | spl14_5),
% 0.20/0.56    inference(resolution,[],[f350,f143])).
% 0.20/0.56  fof(f143,plain,(
% 0.20/0.56    ( ! [X6,X4,X7,X5] : (sP6(X4,X5,X6,X7) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~sP2(X5,X4,X6,X7)) )),
% 0.20/0.56    inference(resolution,[],[f111,f85])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (r3_lattices(X2,k4_lattices(X2,X0,X3),X1) | ~sP2(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f47])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((sP2(X0,X1,X2,X3) | ~sP1(X3,X2,X1,X0) | ~r3_lattices(X2,k4_lattices(X2,X0,X3),X1)) & ((sP1(X3,X2,X1,X0) & r3_lattices(X2,k4_lattices(X2,X0,X3),X1)) | ~sP2(X0,X1,X2,X3)))),
% 0.20/0.56    inference(rectify,[],[f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ! [X1,X2,X0,X3] : ((sP2(X1,X2,X0,X3) | ~sP1(X3,X0,X2,X1) | ~r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) & ((sP1(X3,X0,X2,X1) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) | ~sP2(X1,X2,X0,X3)))),
% 0.20/0.56    inference(flattening,[],[f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ! [X1,X2,X0,X3] : ((sP2(X1,X2,X0,X3) | (~sP1(X3,X0,X2,X1) | ~r3_lattices(X0,k4_lattices(X0,X1,X3),X2))) & ((sP1(X3,X0,X2,X1) & r3_lattices(X0,k4_lattices(X0,X1,X3),X2)) | ~sP2(X1,X2,X0,X3)))),
% 0.20/0.56    inference(nnf_transformation,[],[f29])).
% 0.20/0.56  fof(f111,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X1] : (~r3_lattices(X2,k4_lattices(X2,X1,X4),X0) | sP6(X0,X1,X2,X4) | ~m1_subset_1(X4,u1_struct_0(X2))) )),
% 0.20/0.56    inference(equality_resolution,[],[f108])).
% 0.20/0.56  fof(f108,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (sP6(X0,X1,X2,X3) | ~r3_lattices(X2,k4_lattices(X2,X1,X4),X0) | X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f62])).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((sP6(X0,X1,X2,X3) | ! [X4] : (~r3_lattices(X2,k4_lattices(X2,X1,X4),X0) | X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & ((r3_lattices(X2,k4_lattices(X2,X1,sK13(X0,X1,X2,X3)),X0) & sK13(X0,X1,X2,X3) = X3 & m1_subset_1(sK13(X0,X1,X2,X3),u1_struct_0(X2))) | ~sP6(X0,X1,X2,X3)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f60,f61])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    ! [X3,X2,X1,X0] : (? [X5] : (r3_lattices(X2,k4_lattices(X2,X1,X5),X0) & X3 = X5 & m1_subset_1(X5,u1_struct_0(X2))) => (r3_lattices(X2,k4_lattices(X2,X1,sK13(X0,X1,X2,X3)),X0) & sK13(X0,X1,X2,X3) = X3 & m1_subset_1(sK13(X0,X1,X2,X3),u1_struct_0(X2))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f60,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((sP6(X0,X1,X2,X3) | ! [X4] : (~r3_lattices(X2,k4_lattices(X2,X1,X4),X0) | X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2)))) & (? [X5] : (r3_lattices(X2,k4_lattices(X2,X1,X5),X0) & X3 = X5 & m1_subset_1(X5,u1_struct_0(X2))) | ~sP6(X0,X1,X2,X3)))),
% 0.20/0.56    inference(rectify,[],[f59])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    ! [X3,X2,X1,X0] : ((sP6(X3,X2,X1,X0) | ! [X4] : (~r3_lattices(X1,k4_lattices(X1,X2,X4),X3) | X0 != X4 | ~m1_subset_1(X4,u1_struct_0(X1)))) & (? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP6(X3,X2,X1,X0)))),
% 0.20/0.56    inference(nnf_transformation,[],[f35])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ! [X3,X2,X1,X0] : (sP6(X3,X2,X1,X0) <=> ? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1))))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 0.20/0.56  fof(f350,plain,(
% 0.20/0.56    ~sP6(sK10,sK9,sK8,k4_filter_0(sK8,sK9,sK10)) | spl14_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f348])).
% 0.20/0.56  fof(f348,plain,(
% 0.20/0.56    spl14_5 <=> sP6(sK10,sK9,sK8,k4_filter_0(sK8,sK9,sK10))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).
% 0.20/0.56  fof(f361,plain,(
% 0.20/0.56    spl14_4),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f360])).
% 0.20/0.56  fof(f360,plain,(
% 0.20/0.56    $false | spl14_4),
% 0.20/0.56    inference(subsumption_resolution,[],[f359,f63])).
% 0.20/0.56  fof(f359,plain,(
% 0.20/0.56    v2_struct_0(sK8) | spl14_4),
% 0.20/0.56    inference(subsumption_resolution,[],[f358,f64])).
% 0.20/0.56  fof(f358,plain,(
% 0.20/0.56    ~v10_lattices(sK8) | v2_struct_0(sK8) | spl14_4),
% 0.20/0.56    inference(subsumption_resolution,[],[f357,f65])).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    v4_lattice3(sK8)),
% 0.20/0.56    inference(cnf_transformation,[],[f41])).
% 0.20/0.56  fof(f357,plain,(
% 0.20/0.56    ~v4_lattice3(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8) | spl14_4),
% 0.20/0.56    inference(subsumption_resolution,[],[f356,f66])).
% 0.20/0.56  fof(f356,plain,(
% 0.20/0.56    ~l3_lattices(sK8) | ~v4_lattice3(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8) | spl14_4),
% 0.20/0.56    inference(subsumption_resolution,[],[f355,f67])).
% 0.20/0.56  fof(f355,plain,(
% 0.20/0.56    ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v4_lattice3(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8) | spl14_4),
% 0.20/0.56    inference(subsumption_resolution,[],[f352,f68])).
% 0.20/0.56  fof(f352,plain,(
% 0.20/0.56    ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v4_lattice3(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8) | spl14_4),
% 0.20/0.56    inference(resolution,[],[f346,f109])).
% 0.20/0.56  fof(f109,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (sP7(X0,X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (sP7(X0,X1,X2,X3) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 0.20/0.56    inference(definition_folding,[],[f25,f36,f35])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) <=> sP6(X3,X2,X1,X0)) | ~sP7(X0,X1,X2,X3))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) <=> ? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1)))) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 0.20/0.56    inference(flattening,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) <=> ? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1)))) | (~m1_subset_1(X3,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 0.20/0.56    inference(ennf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,u1_struct_0(X1)) & m1_subset_1(X2,u1_struct_0(X1)) & l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) <=> ? [X4] : (r3_lattices(X1,k4_lattices(X1,X2,X4),X3) & X0 = X4 & m1_subset_1(X4,u1_struct_0(X1)))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_3_6_lattice3)).
% 0.20/0.56  fof(f346,plain,(
% 0.20/0.56    ~sP7(k4_filter_0(sK8,sK9,sK10),sK8,sK9,sK10) | spl14_4),
% 0.20/0.56    inference(avatar_component_clause,[],[f344])).
% 0.20/0.56  fof(f344,plain,(
% 0.20/0.56    spl14_4 <=> sP7(k4_filter_0(sK8,sK9,sK10),sK8,sK9,sK10)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).
% 0.20/0.56  fof(f351,plain,(
% 0.20/0.56    ~spl14_4 | ~spl14_5 | ~spl14_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f342,f271,f348,f344])).
% 0.20/0.56  fof(f271,plain,(
% 0.20/0.56    spl14_1 <=> sP1(k4_filter_0(sK8,sK9,sK10),sK8,sK10,sK9)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 0.20/0.56  fof(f342,plain,(
% 0.20/0.56    ~sP6(sK10,sK9,sK8,k4_filter_0(sK8,sK9,sK10)) | ~sP7(k4_filter_0(sK8,sK9,sK10),sK8,sK9,sK10) | ~spl14_1),
% 0.20/0.56    inference(subsumption_resolution,[],[f335,f272])).
% 0.20/0.56  fof(f272,plain,(
% 0.20/0.56    sP1(k4_filter_0(sK8,sK9,sK10),sK8,sK10,sK9) | ~spl14_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f271])).
% 0.20/0.56  fof(f335,plain,(
% 0.20/0.56    ~sP1(k4_filter_0(sK8,sK9,sK10),sK8,sK10,sK9) | ~sP6(sK10,sK9,sK8,k4_filter_0(sK8,sK9,sK10)) | ~sP7(k4_filter_0(sK8,sK9,sK10),sK8,sK9,sK10)),
% 0.20/0.56    inference(equality_resolution,[],[f282])).
% 0.20/0.56  fof(f282,plain,(
% 0.20/0.56    ( ! [X2] : (k4_filter_0(sK8,sK9,sK10) != X2 | ~sP1(X2,sK8,sK10,sK9) | ~sP6(sK10,sK9,sK8,X2) | ~sP7(X2,sK8,sK9,sK10)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f268,f132])).
% 0.20/0.56  fof(f132,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~sP6(X0,X1,X2,X3) | m1_subset_1(X3,u1_struct_0(X2))) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f131])).
% 0.20/0.56  fof(f131,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(X3,u1_struct_0(X2)) | ~sP6(X0,X1,X2,X3) | ~sP6(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(superposition,[],[f105,f106])).
% 0.20/0.56  fof(f106,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (sK13(X0,X1,X2,X3) = X3 | ~sP6(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f62])).
% 0.20/0.56  fof(f105,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK13(X0,X1,X2,X3),u1_struct_0(X2)) | ~sP6(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f62])).
% 0.20/0.56  fof(f268,plain,(
% 0.20/0.56    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK8)) | k4_filter_0(sK8,sK9,sK10) != X2 | ~sP1(X2,sK8,sK10,sK9) | ~sP6(sK10,sK9,sK8,X2) | ~sP7(X2,sK8,sK9,sK10)) )),
% 0.20/0.56    inference(resolution,[],[f266,f104])).
% 0.20/0.56  fof(f104,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ~sP6(X3,X2,X1,X0) | ~sP7(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f58])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : (((r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | ~sP6(X3,X2,X1,X0)) & (sP6(X3,X2,X1,X0) | ~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)))) | ~sP7(X0,X1,X2,X3))),
% 0.20/0.56    inference(nnf_transformation,[],[f36])).
% 0.20/0.56  fof(f266,plain,(
% 0.20/0.56    ( ! [X10] : (~r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10)) | ~m1_subset_1(X10,u1_struct_0(sK8)) | k4_filter_0(sK8,sK9,sK10) != X10 | ~sP1(X10,sK8,sK10,sK9)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f265,f67])).
% 0.20/0.56  fof(f265,plain,(
% 0.20/0.56    ( ! [X10] : (~sP1(X10,sK8,sK10,sK9) | ~m1_subset_1(X10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | k4_filter_0(sK8,sK9,sK10) != X10 | ~r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f264,f68])).
% 0.20/0.56  fof(f264,plain,(
% 0.20/0.56    ( ! [X10] : (~sP1(X10,sK8,sK10,sK9) | ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(X10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | k4_filter_0(sK8,sK9,sK10) != X10 | ~r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f263,f63])).
% 0.20/0.56  fof(f263,plain,(
% 0.20/0.56    ( ! [X10] : (v2_struct_0(sK8) | ~sP1(X10,sK8,sK10,sK9) | ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(X10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | k4_filter_0(sK8,sK9,sK10) != X10 | ~r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f262,f64])).
% 0.20/0.56  fof(f262,plain,(
% 0.20/0.56    ( ! [X10] : (~v10_lattices(sK8) | v2_struct_0(sK8) | ~sP1(X10,sK8,sK10,sK9) | ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(X10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | k4_filter_0(sK8,sK9,sK10) != X10 | ~r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f261,f65])).
% 0.20/0.56  fof(f261,plain,(
% 0.20/0.56    ( ! [X10] : (~v4_lattice3(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8) | ~sP1(X10,sK8,sK10,sK9) | ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(X10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | k4_filter_0(sK8,sK9,sK10) != X10 | ~r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f258,f66])).
% 0.20/0.56  fof(f258,plain,(
% 0.20/0.56    ( ! [X10] : (~l3_lattices(sK8) | ~v4_lattice3(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8) | ~sP1(X10,sK8,sK10,sK9) | ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(X10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | k4_filter_0(sK8,sK9,sK10) != X10 | ~r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10))) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f257])).
% 0.20/0.56  fof(f257,plain,(
% 0.20/0.56    ( ! [X10] : (~l3_lattices(sK8) | ~v4_lattice3(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8) | ~sP1(X10,sK8,sK10,sK9) | ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(X10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | k4_filter_0(sK8,sK9,sK10) != X10 | ~r2_hidden(X10,a_3_6_lattice3(sK8,sK9,sK10)) | ~m1_subset_1(X10,u1_struct_0(sK8))) )),
% 0.20/0.56    inference(resolution,[],[f254,f189])).
% 0.20/0.56  fof(f189,plain,(
% 0.20/0.56    ( ! [X0] : (~r4_lattice3(sK8,X0,a_3_6_lattice3(sK8,sK9,sK10)) | k4_filter_0(sK8,sK9,sK10) != X0 | ~r2_hidden(X0,a_3_6_lattice3(sK8,sK9,sK10)) | ~m1_subset_1(X0,u1_struct_0(sK8))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f188,f63])).
% 0.20/0.56  fof(f188,plain,(
% 0.20/0.56    ( ! [X0] : (k4_filter_0(sK8,sK9,sK10) != X0 | ~r4_lattice3(sK8,X0,a_3_6_lattice3(sK8,sK9,sK10)) | ~r2_hidden(X0,a_3_6_lattice3(sK8,sK9,sK10)) | ~m1_subset_1(X0,u1_struct_0(sK8)) | v2_struct_0(sK8)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f187,f64])).
% 0.20/0.56  fof(f187,plain,(
% 0.20/0.56    ( ! [X0] : (k4_filter_0(sK8,sK9,sK10) != X0 | ~r4_lattice3(sK8,X0,a_3_6_lattice3(sK8,sK9,sK10)) | ~r2_hidden(X0,a_3_6_lattice3(sK8,sK9,sK10)) | ~m1_subset_1(X0,u1_struct_0(sK8)) | ~v10_lattices(sK8) | v2_struct_0(sK8)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f186,f65])).
% 0.20/0.56  fof(f186,plain,(
% 0.20/0.56    ( ! [X0] : (k4_filter_0(sK8,sK9,sK10) != X0 | ~r4_lattice3(sK8,X0,a_3_6_lattice3(sK8,sK9,sK10)) | ~r2_hidden(X0,a_3_6_lattice3(sK8,sK9,sK10)) | ~m1_subset_1(X0,u1_struct_0(sK8)) | ~v4_lattice3(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f184,f66])).
% 0.20/0.56  fof(f184,plain,(
% 0.20/0.56    ( ! [X0] : (k4_filter_0(sK8,sK9,sK10) != X0 | ~r4_lattice3(sK8,X0,a_3_6_lattice3(sK8,sK9,sK10)) | ~r2_hidden(X0,a_3_6_lattice3(sK8,sK9,sK10)) | ~m1_subset_1(X0,u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v4_lattice3(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8)) )),
% 0.20/0.56    inference(superposition,[],[f73,f82])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | ~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (k15_lattice3(X0,X2) = X1 | (~r4_lattice3(X0,X1,X2) | ~r2_hidden(X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((r4_lattice3(X0,X1,X2) & r2_hidden(X1,X2)) => k15_lattice3(X0,X2) = X1)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice3)).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    k4_filter_0(sK8,sK9,sK10) != k15_lattice3(sK8,a_3_6_lattice3(sK8,sK9,sK10))),
% 0.20/0.56    inference(cnf_transformation,[],[f41])).
% 0.20/0.56  fof(f254,plain,(
% 0.20/0.56    ( ! [X6,X8,X7,X5] : (r4_lattice3(X6,X7,a_3_6_lattice3(X6,X5,X8)) | ~l3_lattices(X6) | ~v4_lattice3(X6) | ~v10_lattices(X6) | v2_struct_0(X6) | ~sP1(X7,X6,X8,X5) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~m1_subset_1(X7,u1_struct_0(X6)) | ~m1_subset_1(X5,u1_struct_0(X6))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f253,f99])).
% 0.20/0.56  fof(f99,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP5(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f34])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (sP5(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(definition_folding,[],[f19,f33,f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X1,X0,X2] : (sP4(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ! [X0,X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> sP4(X1,X0,X2)) | ~sP5(X0,X1))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_lattice3)).
% 0.20/0.56  fof(f253,plain,(
% 0.20/0.56    ( ! [X6,X8,X7,X5] : (~m1_subset_1(X5,u1_struct_0(X6)) | ~l3_lattices(X6) | ~v4_lattice3(X6) | ~v10_lattices(X6) | v2_struct_0(X6) | ~sP1(X7,X6,X8,X5) | ~m1_subset_1(X8,u1_struct_0(X6)) | ~m1_subset_1(X7,u1_struct_0(X6)) | r4_lattice3(X6,X7,a_3_6_lattice3(X6,X5,X8)) | ~sP5(X6,X7)) )),
% 0.20/0.56    inference(resolution,[],[f251,f94])).
% 0.20/0.56  fof(f94,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~sP4(X1,X0,X2) | r4_lattice3(X0,X1,X2) | ~sP5(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ! [X0,X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ~sP4(X1,X0,X2)) & (sP4(X1,X0,X2) | ~r4_lattice3(X0,X1,X2))) | ~sP5(X0,X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f33])).
% 0.20/0.56  fof(f251,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,a_3_6_lattice3(X1,X2,X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~sP1(X3,X1,X0,X2) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f250,f116])).
% 0.20/0.56  fof(f116,plain,(
% 0.20/0.56    ( ! [X3] : (v6_lattices(X3) | v2_struct_0(X3) | ~l3_lattices(X3) | ~v10_lattices(X3)) )),
% 0.20/0.56    inference(resolution,[],[f81,f77])).
% 0.20/0.56  fof(f77,plain,(
% 0.20/0.56    ( ! [X0] : (~sP0(X0) | v6_lattices(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f42])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 0.20/0.56    inference(nnf_transformation,[],[f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 0.20/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.20/0.56  fof(f81,plain,(
% 0.20/0.56    ( ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.56    inference(definition_folding,[],[f13,f26])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.56    inference(flattening,[],[f12])).
% 0.20/0.56  fof(f12,plain,(
% 0.20/0.56    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.20/0.56  fof(f250,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~sP1(X3,X1,X0,X2) | sP4(X3,X1,a_3_6_lattice3(X1,X2,X0)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v6_lattices(X1)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f249,f118])).
% 0.20/0.56  fof(f118,plain,(
% 0.20/0.56    ( ! [X5] : (v8_lattices(X5) | v2_struct_0(X5) | ~l3_lattices(X5) | ~v10_lattices(X5)) )),
% 0.20/0.56    inference(resolution,[],[f81,f79])).
% 0.20/0.56  fof(f79,plain,(
% 0.20/0.56    ( ! [X0] : (~sP0(X0) | v8_lattices(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f42])).
% 0.20/0.56  fof(f249,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~sP1(X3,X1,X0,X2) | sP4(X3,X1,a_3_6_lattice3(X1,X2,X0)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v8_lattices(X1) | ~v6_lattices(X1)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f248,f119])).
% 0.20/0.56  fof(f119,plain,(
% 0.20/0.56    ( ! [X6] : (v9_lattices(X6) | v2_struct_0(X6) | ~l3_lattices(X6) | ~v10_lattices(X6)) )),
% 0.20/0.56    inference(resolution,[],[f81,f80])).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    ( ! [X0] : (~sP0(X0) | v9_lattices(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f42])).
% 0.20/0.56  fof(f248,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~sP1(X3,X1,X0,X2) | sP4(X3,X1,a_3_6_lattice3(X1,X2,X0)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~v9_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f247])).
% 0.20/0.56  fof(f247,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~sP1(X3,X1,X0,X2) | sP4(X3,X1,a_3_6_lattice3(X1,X2,X0)) | ~m1_subset_1(X3,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1) | sP4(X3,X1,a_3_6_lattice3(X1,X2,X0))) )),
% 0.20/0.56    inference(resolution,[],[f214,f200])).
% 0.20/0.56  fof(f200,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r3_lattices(X0,sK12(X1,X0,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | sP4(X1,X0,X2)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f199,f96])).
% 0.20/0.56  fof(f96,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)) | sP4(X0,X1,X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f56])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | (~r1_lattices(X1,sK12(X0,X1,X2),X0) & r2_hidden(sK12(X0,X1,X2),X2) & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12])],[f54,f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,sK12(X0,X1,X2),X0) & r2_hidden(sK12(X0,X1,X2),X2) & m1_subset_1(sK12(X0,X1,X2),u1_struct_0(X1))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X3,X0) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X4,X0) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 0.20/0.56    inference(rectify,[],[f53])).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ! [X1,X0,X2] : ((sP4(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP4(X1,X0,X2)))),
% 0.20/0.56    inference(nnf_transformation,[],[f32])).
% 0.20/0.56  fof(f199,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r3_lattices(X0,sK12(X1,X0,X2),X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(sK12(X1,X0,X2),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | sP4(X1,X0,X2)) )),
% 0.20/0.56    inference(resolution,[],[f100,f98])).
% 0.20/0.56  fof(f98,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r1_lattices(X1,sK12(X0,X1,X2),X0) | sP4(X0,X1,X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f56])).
% 0.20/0.56  fof(f100,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f57])).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(nnf_transformation,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.20/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.20/0.56  fof(f214,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (r3_lattices(X2,sK12(X0,X1,a_3_6_lattice3(X2,X3,X4)),X5) | ~m1_subset_1(X4,u1_struct_0(X2)) | ~m1_subset_1(X3,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2) | ~sP1(X5,X2,X4,X3) | sP4(X0,X1,a_3_6_lattice3(X2,X3,X4))) )),
% 0.20/0.56    inference(resolution,[],[f212,f166])).
% 0.20/0.56  fof(f166,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (~sP6(X3,X4,X0,X1) | ~sP1(X2,X0,X3,X4) | r3_lattices(X0,X1,X2)) )),
% 0.20/0.56    inference(subsumption_resolution,[],[f162,f132])).
% 0.20/0.56  fof(f162,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (r3_lattices(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~sP1(X2,X0,X3,X4) | ~sP6(X3,X4,X0,X1)) )),
% 0.20/0.56    inference(resolution,[],[f88,f139])).
% 0.20/0.56  fof(f139,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (r3_lattices(X2,k4_lattices(X2,X1,X3),X0) | ~sP6(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f138])).
% 0.20/0.56  fof(f138,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (r3_lattices(X2,k4_lattices(X2,X1,X3),X0) | ~sP6(X0,X1,X2,X3) | ~sP6(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(superposition,[],[f107,f106])).
% 0.20/0.56  fof(f107,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (r3_lattices(X2,k4_lattices(X2,X1,sK13(X0,X1,X2,X3)),X0) | ~sP6(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f62])).
% 0.20/0.56  fof(f88,plain,(
% 0.20/0.56    ( ! [X2,X0,X5,X3,X1] : (~r3_lattices(X1,k4_lattices(X1,X3,X5),X2) | r3_lattices(X1,X5,X0) | ~m1_subset_1(X5,u1_struct_0(X1)) | ~sP1(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f51])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (~r3_lattices(X1,sK11(X0,X1,X2,X3),X0) & r3_lattices(X1,k4_lattices(X1,X3,sK11(X0,X1,X2,X3)),X2) & m1_subset_1(sK11(X0,X1,X2,X3),u1_struct_0(X1)))) & (! [X5] : (r3_lattices(X1,X5,X0) | ~r3_lattices(X1,k4_lattices(X1,X3,X5),X2) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~sP1(X0,X1,X2,X3)))),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11])],[f49,f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ! [X3,X2,X1,X0] : (? [X4] : (~r3_lattices(X1,X4,X0) & r3_lattices(X1,k4_lattices(X1,X3,X4),X2) & m1_subset_1(X4,u1_struct_0(X1))) => (~r3_lattices(X1,sK11(X0,X1,X2,X3),X0) & r3_lattices(X1,k4_lattices(X1,X3,sK11(X0,X1,X2,X3)),X2) & m1_subset_1(sK11(X0,X1,X2,X3),u1_struct_0(X1))))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f49,plain,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (~r3_lattices(X1,X4,X0) & r3_lattices(X1,k4_lattices(X1,X3,X4),X2) & m1_subset_1(X4,u1_struct_0(X1)))) & (! [X5] : (r3_lattices(X1,X5,X0) | ~r3_lattices(X1,k4_lattices(X1,X3,X5),X2) | ~m1_subset_1(X5,u1_struct_0(X1))) | ~sP1(X0,X1,X2,X3)))),
% 0.20/0.56    inference(rectify,[],[f48])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ! [X3,X0,X2,X1] : ((sP1(X3,X0,X2,X1) | ? [X4] : (~r3_lattices(X0,X4,X3) & r3_lattices(X0,k4_lattices(X0,X1,X4),X2) & m1_subset_1(X4,u1_struct_0(X0)))) & (! [X4] : (r3_lattices(X0,X4,X3) | ~r3_lattices(X0,k4_lattices(X0,X1,X4),X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~sP1(X3,X0,X2,X1)))),
% 0.20/0.56    inference(nnf_transformation,[],[f28])).
% 0.20/0.56  fof(f212,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (sP6(X0,X1,X2,sK12(X3,X4,a_3_6_lattice3(X2,X1,X0))) | sP4(X3,X4,a_3_6_lattice3(X2,X1,X0)) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~m1_subset_1(X1,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v4_lattice3(X2) | ~v10_lattices(X2) | v2_struct_0(X2)) )),
% 0.20/0.56    inference(resolution,[],[f135,f109])).
% 0.20/0.56  fof(f135,plain,(
% 0.20/0.56    ( ! [X4,X2,X0,X3,X1] : (~sP7(sK12(X3,X4,a_3_6_lattice3(X2,X1,X0)),X2,X1,X0) | sP6(X0,X1,X2,sK12(X3,X4,a_3_6_lattice3(X2,X1,X0))) | sP4(X3,X4,a_3_6_lattice3(X2,X1,X0))) )),
% 0.20/0.56    inference(resolution,[],[f103,f97])).
% 0.20/0.56  fof(f97,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK12(X0,X1,X2),X2) | sP4(X0,X1,X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f56])).
% 0.20/0.56  fof(f103,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,a_3_6_lattice3(X1,X2,X3)) | sP6(X3,X2,X1,X0) | ~sP7(X0,X1,X2,X3)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f58])).
% 0.20/0.56  fof(f315,plain,(
% 0.20/0.56    spl14_3),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f314])).
% 0.20/0.56  fof(f314,plain,(
% 0.20/0.56    $false | spl14_3),
% 0.20/0.56    inference(subsumption_resolution,[],[f313,f63])).
% 0.20/0.56  fof(f313,plain,(
% 0.20/0.56    v2_struct_0(sK8) | spl14_3),
% 0.20/0.56    inference(subsumption_resolution,[],[f312,f64])).
% 0.20/0.56  fof(f312,plain,(
% 0.20/0.56    ~v10_lattices(sK8) | v2_struct_0(sK8) | spl14_3),
% 0.20/0.56    inference(subsumption_resolution,[],[f311,f66])).
% 0.20/0.56  fof(f311,plain,(
% 0.20/0.56    ~l3_lattices(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8) | spl14_3),
% 0.20/0.56    inference(subsumption_resolution,[],[f310,f67])).
% 0.20/0.56  fof(f310,plain,(
% 0.20/0.56    ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8) | spl14_3),
% 0.20/0.56    inference(subsumption_resolution,[],[f306,f68])).
% 0.20/0.56  fof(f306,plain,(
% 0.20/0.56    ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v10_lattices(sK8) | v2_struct_0(sK8) | spl14_3),
% 0.20/0.56    inference(resolution,[],[f280,f102])).
% 0.20/0.56  fof(f280,plain,(
% 0.20/0.56    ~m1_subset_1(k4_filter_0(sK8,sK9,sK10),u1_struct_0(sK8)) | spl14_3),
% 0.20/0.56    inference(avatar_component_clause,[],[f278])).
% 0.20/0.56  fof(f297,plain,(
% 0.20/0.56    spl14_1),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f296])).
% 0.20/0.56  fof(f296,plain,(
% 0.20/0.56    $false | spl14_1),
% 0.20/0.56    inference(subsumption_resolution,[],[f295,f71])).
% 0.20/0.56  fof(f295,plain,(
% 0.20/0.56    ~v3_filter_0(sK8) | spl14_1),
% 0.20/0.56    inference(subsumption_resolution,[],[f294,f66])).
% 0.20/0.56  fof(f294,plain,(
% 0.20/0.56    ~l3_lattices(sK8) | ~v3_filter_0(sK8) | spl14_1),
% 0.20/0.56    inference(subsumption_resolution,[],[f293,f67])).
% 0.20/0.56  fof(f293,plain,(
% 0.20/0.56    ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v3_filter_0(sK8) | spl14_1),
% 0.20/0.56    inference(subsumption_resolution,[],[f292,f68])).
% 0.20/0.56  fof(f292,plain,(
% 0.20/0.56    ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v3_filter_0(sK8) | spl14_1),
% 0.20/0.56    inference(subsumption_resolution,[],[f291,f63])).
% 0.20/0.56  fof(f291,plain,(
% 0.20/0.56    v2_struct_0(sK8) | ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v3_filter_0(sK8) | spl14_1),
% 0.20/0.56    inference(subsumption_resolution,[],[f288,f64])).
% 0.20/0.56  fof(f288,plain,(
% 0.20/0.56    ~v10_lattices(sK8) | v2_struct_0(sK8) | ~m1_subset_1(sK10,u1_struct_0(sK8)) | ~m1_subset_1(sK9,u1_struct_0(sK8)) | ~l3_lattices(sK8) | ~v3_filter_0(sK8) | spl14_1),
% 0.20/0.56    inference(resolution,[],[f273,f202])).
% 0.20/0.56  fof(f202,plain,(
% 0.20/0.56    ( ! [X6,X4,X5] : (sP1(k4_filter_0(X4,X6,X5),X4,X5,X6) | ~v10_lattices(X4) | v2_struct_0(X4) | ~m1_subset_1(X5,u1_struct_0(X4)) | ~m1_subset_1(X6,u1_struct_0(X4)) | ~l3_lattices(X4) | ~v3_filter_0(X4)) )),
% 0.20/0.56    inference(resolution,[],[f198,f86])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (~sP2(X0,X1,X2,X3) | sP1(X3,X2,X1,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f47])).
% 0.20/0.56  fof(f273,plain,(
% 0.20/0.56    ~sP1(k4_filter_0(sK8,sK9,sK10),sK8,sK10,sK9) | spl14_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f271])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (32031)------------------------------
% 0.20/0.56  % (32031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (32031)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (32031)Memory used [KB]: 6396
% 0.20/0.56  % (32031)Time elapsed: 0.150 s
% 0.20/0.56  % (32031)------------------------------
% 0.20/0.56  % (32031)------------------------------
% 0.20/0.56  % (32026)Success in time 0.205 s
%------------------------------------------------------------------------------
