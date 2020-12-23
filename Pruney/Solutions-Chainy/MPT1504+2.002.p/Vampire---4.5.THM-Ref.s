%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:39 EST 2020

% Result     : Theorem 1.44s
% Output     : Refutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :  218 ( 576 expanded)
%              Number of leaves         :   35 ( 185 expanded)
%              Depth                    :   23
%              Number of atoms          : 1027 (2824 expanded)
%              Number of equality atoms :   50 ( 348 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f606,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f462,f467,f472,f477,f513,f531,f543,f557,f571,f587,f601])).

fof(f601,plain,(
    spl17_7 ),
    inference(avatar_contradiction_clause,[],[f600])).

fof(f600,plain,
    ( $false
    | spl17_7 ),
    inference(subsumption_resolution,[],[f599,f75])).

fof(f75,plain,(
    ~ v2_struct_0(sK11) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( k15_lattice3(sK11,sK12) != k16_lattice3(sK11,a_2_2_lattice3(sK11,sK12))
    & l3_lattices(sK11)
    & v4_lattice3(sK11)
    & v10_lattices(sK11)
    & ~ v2_struct_0(sK11) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f11,f43,f42])).

fof(f42,plain,
    ( ? [X0] :
        ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] : k15_lattice3(sK11,X1) != k16_lattice3(sK11,a_2_2_lattice3(sK11,X1))
      & l3_lattices(sK11)
      & v4_lattice3(sK11)
      & v10_lattices(sK11)
      & ~ v2_struct_0(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X1] : k15_lattice3(sK11,X1) != k16_lattice3(sK11,a_2_2_lattice3(sK11,X1))
   => k15_lattice3(sK11,sK12) != k16_lattice3(sK11,a_2_2_lattice3(sK11,sK12)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1))
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
       => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).

fof(f599,plain,
    ( v2_struct_0(sK11)
    | spl17_7 ),
    inference(subsumption_resolution,[],[f598,f76])).

fof(f76,plain,(
    v10_lattices(sK11) ),
    inference(cnf_transformation,[],[f44])).

fof(f598,plain,
    ( ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl17_7 ),
    inference(subsumption_resolution,[],[f597,f77])).

fof(f77,plain,(
    v4_lattice3(sK11) ),
    inference(cnf_transformation,[],[f44])).

fof(f597,plain,
    ( ~ v4_lattice3(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl17_7 ),
    inference(subsumption_resolution,[],[f594,f78])).

fof(f78,plain,(
    l3_lattices(sK11) ),
    inference(cnf_transformation,[],[f44])).

fof(f594,plain,
    ( ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl17_7 ),
    inference(resolution,[],[f512,f182])).

fof(f182,plain,(
    ! [X0,X1] :
      ( sP3(k15_lattice3(X0,X1),X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f177])).

fof(f177,plain,(
    ! [X0,X1] :
      ( sP3(k15_lattice3(X0,X1),X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f97,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP3(X1,X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( sP3(X1,X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f15,f30,f29,f28])).

fof(f28,plain,(
    ! [X1,X0,X2] :
      ( sP1(X1,X0,X2)
    <=> ! [X3] :
          ( r3_lattices(X0,X3,X1)
          | ~ r3_lattice3(X0,X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( sP2(X2,X0,X1)
    <=> ( sP1(X1,X0,X2)
        & r3_lattice3(X0,X1,X2) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f30,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( k16_lattice3(X0,X2) = X1
        <=> sP2(X2,X0,X1) )
      | ~ sP3(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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

fof(f512,plain,
    ( ~ sP3(k15_lattice3(sK11,sK12),sK11)
    | spl17_7 ),
    inference(avatar_component_clause,[],[f510])).

fof(f510,plain,
    ( spl17_7
  <=> sP3(k15_lattice3(sK11,sK12),sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_7])])).

fof(f587,plain,(
    spl17_11 ),
    inference(avatar_contradiction_clause,[],[f586])).

fof(f586,plain,
    ( $false
    | spl17_11 ),
    inference(subsumption_resolution,[],[f585,f77])).

fof(f585,plain,
    ( ~ v4_lattice3(sK11)
    | spl17_11 ),
    inference(subsumption_resolution,[],[f584,f78])).

fof(f584,plain,
    ( ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | spl17_11 ),
    inference(subsumption_resolution,[],[f583,f75])).

fof(f583,plain,
    ( v2_struct_0(sK11)
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | spl17_11 ),
    inference(subsumption_resolution,[],[f580,f76])).

fof(f580,plain,
    ( ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | spl17_11 ),
    inference(resolution,[],[f556,f194])).

fof(f194,plain,(
    ! [X2,X3] :
      ( r4_lattice3(X2,k15_lattice3(X2,X3),X3)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2)
      | ~ l3_lattices(X2)
      | ~ v4_lattice3(X2) ) ),
    inference(resolution,[],[f192,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | r4_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X0,X1,X2)
        | ~ sP4(X2,X1,X0)
        | ~ r4_lattice3(X1,X2,X0) )
      & ( ( sP4(X2,X1,X0)
          & r4_lattice3(X1,X2,X0) )
        | ~ sP5(X0,X1,X2) ) ) ),
    inference(rectify,[],[f58])).

fof(f58,plain,(
    ! [X1,X0,X2] :
      ( ( sP5(X1,X0,X2)
        | ~ sP4(X2,X0,X1)
        | ~ r4_lattice3(X0,X2,X1) )
      & ( ( sP4(X2,X0,X1)
          & r4_lattice3(X0,X2,X1) )
        | ~ sP5(X1,X0,X2) ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
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

fof(f192,plain,(
    ! [X0,X1] :
      ( sP5(X1,X0,k15_lattice3(X0,X1))
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f189,f115])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP5(X1,X0,k15_lattice3(X0,X1)) ) ),
    inference(resolution,[],[f128,f126])).

fof(f126,plain,(
    ! [X2,X1] :
      ( ~ sP6(k15_lattice3(X1,X2),X1,X2)
      | sP5(X2,X1,k15_lattice3(X1,X2)) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( sP5(X2,X1,X0)
      | k15_lattice3(X1,X2) != X0
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( ( k15_lattice3(X1,X2) = X0
          | ~ sP5(X2,X1,X0) )
        & ( sP5(X2,X1,X0)
          | k15_lattice3(X1,X2) != X0 ) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
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

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f556,plain,
    ( ~ r4_lattice3(sK11,k15_lattice3(sK11,sK12),sK12)
    | spl17_11 ),
    inference(avatar_component_clause,[],[f554])).

fof(f554,plain,
    ( spl17_11
  <=> r4_lattice3(sK11,k15_lattice3(sK11,sK12),sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_11])])).

fof(f571,plain,(
    spl17_5 ),
    inference(avatar_contradiction_clause,[],[f570])).

fof(f570,plain,
    ( $false
    | spl17_5 ),
    inference(subsumption_resolution,[],[f569,f75])).

fof(f569,plain,
    ( v2_struct_0(sK11)
    | spl17_5 ),
    inference(subsumption_resolution,[],[f565,f78])).

fof(f565,plain,
    ( ~ l3_lattices(sK11)
    | v2_struct_0(sK11)
    | spl17_5 ),
    inference(resolution,[],[f504,f115])).

fof(f504,plain,
    ( ~ m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))
    | spl17_5 ),
    inference(avatar_component_clause,[],[f502])).

fof(f502,plain,
    ( spl17_5
  <=> m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_5])])).

fof(f557,plain,
    ( ~ spl17_5
    | ~ spl17_11
    | spl17_10 ),
    inference(avatar_split_clause,[],[f550,f528,f554,f502])).

fof(f528,plain,
    ( spl17_10
  <=> sP9(sK12,sK11,k15_lattice3(sK11,sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_10])])).

fof(f550,plain,
    ( ~ r4_lattice3(sK11,k15_lattice3(sK11,sK12),sK12)
    | ~ m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))
    | spl17_10 ),
    inference(resolution,[],[f530,f127])).

fof(f127,plain,(
    ! [X0,X3,X1] :
      ( sP9(X0,X1,X3)
      | ~ r4_lattice3(X1,X3,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f123])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( sP9(X0,X1,X2)
      | ~ r4_lattice3(X1,X3,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( sP9(X0,X1,X2)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( r4_lattice3(X1,sK16(X0,X1,X2),X0)
          & sK16(X0,X1,X2) = X2
          & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP9(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f72,f73])).

fof(f73,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r4_lattice3(X1,X4,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( r4_lattice3(X1,sK16(X0,X1,X2),X0)
        & sK16(X0,X1,X2) = X2
        & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( sP9(X0,X1,X2)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( r4_lattice3(X1,X4,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP9(X0,X1,X2) ) ) ),
    inference(rectify,[],[f71])).

fof(f71,plain,(
    ! [X2,X1,X0] :
      ( ( sP9(X2,X1,X0)
        | ! [X3] :
            ( ~ r4_lattice3(X1,X3,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( r4_lattice3(X1,X3,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP9(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( sP9(X2,X1,X0)
    <=> ? [X3] :
          ( r4_lattice3(X1,X3,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).

fof(f530,plain,
    ( ~ sP9(sK12,sK11,k15_lattice3(sK11,sK12))
    | spl17_10 ),
    inference(avatar_component_clause,[],[f528])).

fof(f543,plain,(
    spl17_9 ),
    inference(avatar_contradiction_clause,[],[f542])).

fof(f542,plain,
    ( $false
    | spl17_9 ),
    inference(subsumption_resolution,[],[f541,f75])).

fof(f541,plain,
    ( v2_struct_0(sK11)
    | spl17_9 ),
    inference(subsumption_resolution,[],[f540,f76])).

fof(f540,plain,
    ( ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl17_9 ),
    inference(subsumption_resolution,[],[f539,f77])).

fof(f539,plain,
    ( ~ v4_lattice3(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl17_9 ),
    inference(subsumption_resolution,[],[f536,f78])).

fof(f536,plain,
    ( ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ v10_lattices(sK11)
    | v2_struct_0(sK11)
    | spl17_9 ),
    inference(resolution,[],[f526,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( sP10(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( sP10(X0,X1,X2)
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f25,f40,f39])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      <=> sP9(X2,X1,X0) )
      | ~ sP10(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f526,plain,
    ( ~ sP10(k15_lattice3(sK11,sK12),sK11,sK12)
    | spl17_9 ),
    inference(avatar_component_clause,[],[f524])).

fof(f524,plain,
    ( spl17_9
  <=> sP10(k15_lattice3(sK11,sK12),sK11,sK12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_9])])).

fof(f531,plain,
    ( ~ spl17_9
    | ~ spl17_10
    | spl17_6 ),
    inference(avatar_split_clause,[],[f520,f506,f528,f524])).

fof(f506,plain,
    ( spl17_6
  <=> r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_6])])).

fof(f520,plain,
    ( ~ sP9(sK12,sK11,k15_lattice3(sK11,sK12))
    | ~ sP10(k15_lattice3(sK11,sK12),sK11,sK12)
    | spl17_6 ),
    inference(resolution,[],[f508,f119])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | ~ sP9(X2,X1,X0)
      | ~ sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_2_lattice3(X1,X2))
          | ~ sP9(X2,X1,X0) )
        & ( sP9(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_2_lattice3(X1,X2)) ) )
      | ~ sP10(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f508,plain,
    ( ~ r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12))
    | spl17_6 ),
    inference(avatar_component_clause,[],[f506])).

fof(f513,plain,
    ( ~ spl17_5
    | ~ spl17_6
    | ~ spl17_7
    | ~ spl17_4 ),
    inference(avatar_split_clause,[],[f500,f460,f510,f506,f502])).

fof(f460,plain,
    ( spl17_4
  <=> ! [X0] :
        ( ~ r2_hidden(X0,a_2_2_lattice3(sK11,sK12))
        | ~ sP3(X0,sK11)
        | k15_lattice3(sK11,sK12) != X0
        | ~ r3_lattice3(sK11,X0,a_2_2_lattice3(sK11,sK12))
        | ~ m1_subset_1(X0,u1_struct_0(sK11)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).

fof(f500,plain,
    ( ~ sP3(k15_lattice3(sK11,sK12),sK11)
    | ~ r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12))
    | ~ m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))
    | ~ spl17_4 ),
    inference(subsumption_resolution,[],[f499,f77])).

fof(f499,plain,
    ( ~ sP3(k15_lattice3(sK11,sK12),sK11)
    | ~ r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12))
    | ~ m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))
    | ~ v4_lattice3(sK11)
    | ~ spl17_4 ),
    inference(subsumption_resolution,[],[f498,f78])).

fof(f498,plain,
    ( ~ sP3(k15_lattice3(sK11,sK12),sK11)
    | ~ r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12))
    | ~ m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ spl17_4 ),
    inference(subsumption_resolution,[],[f497,f76])).

fof(f497,plain,
    ( ~ sP3(k15_lattice3(sK11,sK12),sK11)
    | ~ r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12))
    | ~ m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))
    | ~ v10_lattices(sK11)
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ spl17_4 ),
    inference(subsumption_resolution,[],[f491,f75])).

fof(f491,plain,
    ( ~ sP3(k15_lattice3(sK11,sK12),sK11)
    | ~ r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12))
    | ~ m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))
    | v2_struct_0(sK11)
    | ~ v10_lattices(sK11)
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ spl17_4 ),
    inference(trivial_inequality_removal,[],[f487])).

fof(f487,plain,
    ( ~ sP3(k15_lattice3(sK11,sK12),sK11)
    | k15_lattice3(sK11,sK12) != k15_lattice3(sK11,sK12)
    | ~ r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12))
    | ~ m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))
    | v2_struct_0(sK11)
    | ~ v10_lattices(sK11)
    | ~ l3_lattices(sK11)
    | ~ v4_lattice3(sK11)
    | ~ spl17_4 ),
    inference(resolution,[],[f461,f294])).

fof(f294,plain,(
    ! [X4,X3] :
      ( r3_lattice3(X3,k15_lattice3(X3,X4),a_2_2_lattice3(X3,X4))
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3) ) ),
    inference(subsumption_resolution,[],[f292,f142])).

fof(f142,plain,(
    ! [X0,X1] :
      ( sP8(X0,k15_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( sP8(X0,k15_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f114,f115])).

% (25867)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (25866)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% (25860)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
fof(f114,plain,(
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
          ( r1_lattices(X0,X1,X3)
          | ~ r2_hidden(X3,X2)
          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r3_lattice3(X0,X1,X2)
        <=> sP7(X1,X0,X2) )
      | ~ sP8(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f292,plain,(
    ! [X4,X3] :
      ( ~ v4_lattice3(X3)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | ~ l3_lattices(X3)
      | r3_lattice3(X3,k15_lattice3(X3,X4),a_2_2_lattice3(X3,X4))
      | ~ sP8(X3,k15_lattice3(X3,X4)) ) ),
    inference(resolution,[],[f290,f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X1,X0,X2)
      | r3_lattice3(X0,X1,X2)
      | ~ sP8(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r3_lattice3(X0,X1,X2)
            | ~ sP7(X1,X0,X2) )
          & ( sP7(X1,X0,X2)
            | ~ r3_lattice3(X0,X1,X2) ) )
      | ~ sP8(X0,X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f290,plain,(
    ! [X0,X1] :
      ( sP7(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1))
      | ~ v4_lattice3(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f288])).

fof(f288,plain,(
    ! [X0,X1] :
      ( ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | sP7(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | sP7(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1)) ) ),
    inference(resolution,[],[f243,f270])).

fof(f270,plain,(
    ! [X10,X8,X11,X9] :
      ( r4_lattice3(X10,sK15(X8,X9,a_2_2_lattice3(X10,X11)),X11)
      | ~ l3_lattices(X10)
      | ~ v4_lattice3(X10)
      | ~ v10_lattices(X10)
      | v2_struct_0(X10)
      | sP7(X8,X9,a_2_2_lattice3(X10,X11)) ) ),
    inference(resolution,[],[f225,f147])).

fof(f147,plain,(
    ! [X2,X0,X1] :
      ( ~ sP9(X0,X1,X2)
      | r4_lattice3(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,X2,X0)
      | ~ sP9(X0,X1,X2)
      | ~ sP9(X0,X1,X2) ) ),
    inference(superposition,[],[f122,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( sK16(X0,X1,X2) = X2
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( r4_lattice3(X1,sK16(X0,X1,X2),X0)
      | ~ sP9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f225,plain,(
    ! [X2,X0,X3,X1] :
      ( sP9(X0,X1,sK15(X2,X3,a_2_2_lattice3(X1,X0)))
      | sP7(X2,X3,a_2_2_lattice3(X1,X0))
      | ~ l3_lattices(X1)
      | ~ v4_lattice3(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f174,f124])).

fof(f174,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP10(sK15(X2,X3,a_2_2_lattice3(X1,X0)),X1,X0)
      | sP9(X0,X1,sK15(X2,X3,a_2_2_lattice3(X1,X0)))
      | sP7(X2,X3,a_2_2_lattice3(X1,X0)) ) ),
    inference(resolution,[],[f118,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK15(X0,X1,X2),X2)
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( sP7(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK15(X0,X1,X2))
          & r2_hidden(sK15(X0,X1,X2),X2)
          & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP7(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f66,f67])).

fof(f67,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK15(X0,X1,X2))
        & r2_hidden(sK15(X0,X1,X2),X2)
        & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,(
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
    inference(rectify,[],[f65])).

fof(f65,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(X1,X2))
      | sP9(X2,X1,X0)
      | ~ sP10(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f243,plain,(
    ! [X4,X5,X3] :
      ( ~ r4_lattice3(X3,sK15(k15_lattice3(X3,X4),X3,X5),X4)
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | v2_struct_0(X3)
      | ~ v10_lattices(X3)
      | sP7(k15_lattice3(X3,X4),X3,X5) ) ),
    inference(subsumption_resolution,[],[f238,f111])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f238,plain,(
    ! [X4,X5,X3] :
      ( v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ v4_lattice3(X3)
      | ~ r4_lattice3(X3,sK15(k15_lattice3(X3,X4),X3,X5),X4)
      | ~ m1_subset_1(sK15(k15_lattice3(X3,X4),X3,X5),u1_struct_0(X3))
      | ~ v10_lattices(X3)
      | sP7(k15_lattice3(X3,X4),X3,X5) ) ),
    inference(resolution,[],[f196,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X1,X0,sK15(X0,X1,X2))
      | sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f196,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k15_lattice3(X0,X2),X1)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ r4_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v10_lattices(X0) ) ),
    inference(resolution,[],[f193,f103])).

fof(f103,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP4(X0,X1,X2)
      | ~ r4_lattice3(X1,X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ( sP4(X0,X1,X2)
        | ( ~ r1_lattices(X1,X0,sK14(X0,X1,X2))
          & r4_lattice3(X1,sK14(X0,X1,X2),X2)
          & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r1_lattices(X1,X0,X4)
            | ~ r4_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP4(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f61,f62])).

fof(f62,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X1,X0,X3)
          & r4_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r1_lattices(X1,X0,sK14(X0,X1,X2))
        & r4_lattice3(X1,sK14(X0,X1,X2),X2)
        & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
    inference(rectify,[],[f60])).

fof(f60,plain,(
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

fof(f193,plain,(
    ! [X0,X1] :
      ( sP4(k15_lattice3(X0,X1),X0,X1)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0) ) ),
    inference(resolution,[],[f192,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ sP5(X0,X1,X2)
      | sP4(X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f461,plain,
    ( ! [X0] :
        ( ~ r3_lattice3(sK11,X0,a_2_2_lattice3(sK11,sK12))
        | ~ sP3(X0,sK11)
        | k15_lattice3(sK11,sK12) != X0
        | ~ r2_hidden(X0,a_2_2_lattice3(sK11,sK12))
        | ~ m1_subset_1(X0,u1_struct_0(sK11)) )
    | ~ spl17_4 ),
    inference(avatar_component_clause,[],[f460])).

fof(f477,plain,(
    spl17_3 ),
    inference(avatar_contradiction_clause,[],[f476])).

fof(f476,plain,
    ( $false
    | spl17_3 ),
    inference(subsumption_resolution,[],[f475,f76])).

fof(f475,plain,
    ( ~ v10_lattices(sK11)
    | spl17_3 ),
    inference(subsumption_resolution,[],[f474,f78])).

fof(f474,plain,
    ( ~ l3_lattices(sK11)
    | ~ v10_lattices(sK11)
    | spl17_3 ),
    inference(subsumption_resolution,[],[f473,f75])).

fof(f473,plain,
    ( v2_struct_0(sK11)
    | ~ l3_lattices(sK11)
    | ~ v10_lattices(sK11)
    | spl17_3 ),
    inference(resolution,[],[f458,f135])).

fof(f135,plain,(
    ! [X6] :
      ( v9_lattices(X6)
      | v2_struct_0(X6)
      | ~ l3_lattices(X6)
      | ~ v10_lattices(X6) ) ),
    inference(resolution,[],[f87,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v9_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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

fof(f87,plain,(
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

fof(f458,plain,
    ( ~ v9_lattices(sK11)
    | spl17_3 ),
    inference(avatar_component_clause,[],[f456])).

fof(f456,plain,
    ( spl17_3
  <=> v9_lattices(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_3])])).

fof(f472,plain,(
    spl17_2 ),
    inference(avatar_contradiction_clause,[],[f471])).

fof(f471,plain,
    ( $false
    | spl17_2 ),
    inference(subsumption_resolution,[],[f470,f76])).

fof(f470,plain,
    ( ~ v10_lattices(sK11)
    | spl17_2 ),
    inference(subsumption_resolution,[],[f469,f78])).

fof(f469,plain,
    ( ~ l3_lattices(sK11)
    | ~ v10_lattices(sK11)
    | spl17_2 ),
    inference(subsumption_resolution,[],[f468,f75])).

fof(f468,plain,
    ( v2_struct_0(sK11)
    | ~ l3_lattices(sK11)
    | ~ v10_lattices(sK11)
    | spl17_2 ),
    inference(resolution,[],[f454,f134])).

fof(f134,plain,(
    ! [X5] :
      ( v8_lattices(X5)
      | v2_struct_0(X5)
      | ~ l3_lattices(X5)
      | ~ v10_lattices(X5) ) ),
    inference(resolution,[],[f87,f85])).

fof(f85,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v8_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f454,plain,
    ( ~ v8_lattices(sK11)
    | spl17_2 ),
    inference(avatar_component_clause,[],[f452])).

fof(f452,plain,
    ( spl17_2
  <=> v8_lattices(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).

fof(f467,plain,(
    spl17_1 ),
    inference(avatar_contradiction_clause,[],[f466])).

fof(f466,plain,
    ( $false
    | spl17_1 ),
    inference(subsumption_resolution,[],[f465,f76])).

fof(f465,plain,
    ( ~ v10_lattices(sK11)
    | spl17_1 ),
    inference(subsumption_resolution,[],[f464,f78])).

fof(f464,plain,
    ( ~ l3_lattices(sK11)
    | ~ v10_lattices(sK11)
    | spl17_1 ),
    inference(subsumption_resolution,[],[f463,f75])).

fof(f463,plain,
    ( v2_struct_0(sK11)
    | ~ l3_lattices(sK11)
    | ~ v10_lattices(sK11)
    | spl17_1 ),
    inference(resolution,[],[f450,f132])).

fof(f132,plain,(
    ! [X3] :
      ( v6_lattices(X3)
      | v2_struct_0(X3)
      | ~ l3_lattices(X3)
      | ~ v10_lattices(X3) ) ),
    inference(resolution,[],[f87,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ sP0(X0)
      | v6_lattices(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f450,plain,
    ( ~ v6_lattices(sK11)
    | spl17_1 ),
    inference(avatar_component_clause,[],[f448])).

fof(f448,plain,
    ( spl17_1
  <=> v6_lattices(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f462,plain,
    ( ~ spl17_1
    | ~ spl17_2
    | ~ spl17_3
    | spl17_4 ),
    inference(avatar_split_clause,[],[f446,f460,f456,f452,f448])).

fof(f446,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(sK11,sK12))
      | ~ m1_subset_1(X0,u1_struct_0(sK11))
      | ~ v9_lattices(sK11)
      | ~ v8_lattices(sK11)
      | ~ v6_lattices(sK11)
      | ~ r3_lattice3(sK11,X0,a_2_2_lattice3(sK11,sK12))
      | k15_lattice3(sK11,sK12) != X0
      | ~ sP3(X0,sK11) ) ),
    inference(subsumption_resolution,[],[f445,f75])).

fof(f445,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(sK11,sK12))
      | ~ m1_subset_1(X0,u1_struct_0(sK11))
      | ~ v9_lattices(sK11)
      | ~ v8_lattices(sK11)
      | ~ v6_lattices(sK11)
      | v2_struct_0(sK11)
      | ~ r3_lattice3(sK11,X0,a_2_2_lattice3(sK11,sK12))
      | k15_lattice3(sK11,sK12) != X0
      | ~ sP3(X0,sK11) ) ),
    inference(subsumption_resolution,[],[f442,f78])).

fof(f442,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,a_2_2_lattice3(sK11,sK12))
      | ~ m1_subset_1(X0,u1_struct_0(sK11))
      | ~ l3_lattices(sK11)
      | ~ v9_lattices(sK11)
      | ~ v8_lattices(sK11)
      | ~ v6_lattices(sK11)
      | v2_struct_0(sK11)
      | ~ r3_lattice3(sK11,X0,a_2_2_lattice3(sK11,sK12))
      | k15_lattice3(sK11,sK12) != X0
      | ~ sP3(X0,sK11) ) ),
    inference(resolution,[],[f437,f162])).

fof(f162,plain,(
    ! [X6] :
      ( ~ sP1(X6,sK11,a_2_2_lattice3(sK11,sK12))
      | ~ r3_lattice3(sK11,X6,a_2_2_lattice3(sK11,sK12))
      | k15_lattice3(sK11,sK12) != X6
      | ~ sP3(X6,sK11) ) ),
    inference(resolution,[],[f92,f151])).

fof(f151,plain,(
    ! [X0] :
      ( ~ sP2(a_2_2_lattice3(sK11,sK12),sK11,X0)
      | k15_lattice3(sK11,sK12) != X0
      | ~ sP3(X0,sK11) ) ),
    inference(superposition,[],[f79,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k16_lattice3(X1,X2) = X0
      | ~ sP2(X2,X1,X0)
      | ~ sP3(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k16_lattice3(X1,X2) = X0
            | ~ sP2(X2,X1,X0) )
          & ( sP2(X2,X1,X0)
            | k16_lattice3(X1,X2) != X0 ) )
      | ~ sP3(X0,X1) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ! [X2] :
          ( ( k16_lattice3(X0,X2) = X1
            | ~ sP2(X2,X0,X1) )
          & ( sP2(X2,X0,X1)
            | k16_lattice3(X0,X2) != X1 ) )
      | ~ sP3(X1,X0) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f79,plain,(
    k15_lattice3(sK11,sK12) != k16_lattice3(sK11,a_2_2_lattice3(sK11,sK12)) ),
    inference(cnf_transformation,[],[f44])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( sP2(X0,X1,X2)
      | ~ sP1(X2,X1,X0)
      | ~ r3_lattice3(X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ~ sP1(X2,X1,X0)
        | ~ r3_lattice3(X1,X2,X0) )
      & ( ( sP1(X2,X1,X0)
          & r3_lattice3(X1,X2,X0) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ~ sP1(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP1(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ( sP2(X2,X0,X1)
        | ~ sP1(X1,X0,X2)
        | ~ r3_lattice3(X0,X1,X2) )
      & ( ( sP1(X1,X0,X2)
          & r3_lattice3(X0,X1,X2) )
        | ~ sP2(X2,X0,X1) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f437,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v9_lattices(X2)
      | ~ v8_lattices(X2)
      | ~ v6_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(duplicate_literal_removal,[],[f432])).

fof(f432,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | sP1(X0,X2,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v9_lattices(X2)
      | ~ v8_lattices(X2)
      | ~ v6_lattices(X2)
      | v2_struct_0(X2)
      | sP1(X0,X2,X1) ) ),
    inference(resolution,[],[f308,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X1,sK13(X0,X1,X2),X0)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ r3_lattices(X1,sK13(X0,X1,X2),X0)
          & r3_lattice3(X1,sK13(X0,X1,X2),X2)
          & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r3_lattices(X1,X4,X0)
            | ~ r3_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f52,f53])).

fof(f53,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r3_lattices(X1,X3,X0)
          & r3_lattice3(X1,X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r3_lattices(X1,sK13(X0,X1,X2),X0)
        & r3_lattice3(X1,sK13(X0,X1,X2),X2)
        & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ r3_lattices(X1,X3,X0)
            & r3_lattice3(X1,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r3_lattices(X1,X4,X0)
            | ~ r3_lattice3(X1,X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f51])).

fof(f51,plain,(
    ! [X1,X0,X2] :
      ( ( sP1(X1,X0,X2)
        | ? [X3] :
            ( ~ r3_lattices(X0,X3,X1)
            & r3_lattice3(X0,X3,X2)
            & m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ! [X3] :
            ( r3_lattices(X0,X3,X1)
            | ~ r3_lattice3(X0,X3,X2)
            | ~ m1_subset_1(X3,u1_struct_0(X0)) )
        | ~ sP1(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f308,plain,(
    ! [X10,X8,X11,X9] :
      ( r3_lattices(X9,sK13(X11,X9,X10),X8)
      | ~ r2_hidden(X8,X10)
      | sP1(X11,X9,X10)
      | ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ l3_lattices(X9)
      | ~ v9_lattices(X9)
      | ~ v8_lattices(X9)
      | ~ v6_lattices(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f307,f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f307,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ r2_hidden(X8,X10)
      | sP1(X11,X9,X10)
      | r3_lattices(X9,sK13(X11,X9,X10),X8)
      | ~ m1_subset_1(sK13(X11,X9,X10),u1_struct_0(X9))
      | ~ l3_lattices(X9)
      | ~ v9_lattices(X9)
      | ~ v8_lattices(X9)
      | ~ v6_lattices(X9)
      | v2_struct_0(X9) ) ),
    inference(subsumption_resolution,[],[f304,f114])).

fof(f304,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ r2_hidden(X8,X10)
      | ~ sP8(X9,sK13(X11,X9,X10))
      | sP1(X11,X9,X10)
      | r3_lattices(X9,sK13(X11,X9,X10),X8)
      | ~ m1_subset_1(sK13(X11,X9,X10),u1_struct_0(X9))
      | ~ l3_lattices(X9)
      | ~ v9_lattices(X9)
      | ~ v8_lattices(X9)
      | ~ v6_lattices(X9)
      | v2_struct_0(X9) ) ),
    inference(duplicate_literal_removal,[],[f303])).

fof(f303,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ r2_hidden(X8,X10)
      | ~ sP8(X9,sK13(X11,X9,X10))
      | sP1(X11,X9,X10)
      | r3_lattices(X9,sK13(X11,X9,X10),X8)
      | ~ m1_subset_1(X8,u1_struct_0(X9))
      | ~ m1_subset_1(sK13(X11,X9,X10),u1_struct_0(X9))
      | ~ l3_lattices(X9)
      | ~ v9_lattices(X9)
      | ~ v8_lattices(X9)
      | ~ v6_lattices(X9)
      | v2_struct_0(X9) ) ),
    inference(resolution,[],[f213,f117])).

fof(f117,plain,(
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
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
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

fof(f213,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_lattices(X1,sK13(X2,X1,X3),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ r2_hidden(X0,X3)
      | ~ sP8(X1,sK13(X2,X1,X3))
      | sP1(X2,X1,X3) ) ),
    inference(resolution,[],[f187,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( r3_lattice3(X1,sK13(X0,X1,X2),X2)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f187,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r3_lattice3(X2,X3,X1)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | r1_lattices(X2,X3,X0)
      | ~ r2_hidden(X0,X1)
      | ~ sP8(X2,X3) ) ),
    inference(resolution,[],[f110,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( sP7(X1,X0,X2)
      | ~ r3_lattice3(X0,X1,X2)
      | ~ sP8(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f110,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r1_lattices(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:00:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (25862)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.46  % (25855)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.47  % (25843)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.47  % (25843)Refutation not found, incomplete strategy% (25843)------------------------------
% 0.21/0.47  % (25843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (25843)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (25843)Memory used [KB]: 10618
% 0.21/0.47  % (25843)Time elapsed: 0.063 s
% 0.21/0.47  % (25843)------------------------------
% 0.21/0.47  % (25843)------------------------------
% 0.21/0.48  % (25856)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (25865)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (25846)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.51  % (25851)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.51  % (25850)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (25850)Refutation not found, incomplete strategy% (25850)------------------------------
% 0.21/0.51  % (25850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (25850)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (25850)Memory used [KB]: 1663
% 0.21/0.51  % (25850)Time elapsed: 0.105 s
% 0.21/0.51  % (25850)------------------------------
% 0.21/0.51  % (25850)------------------------------
% 0.21/0.51  % (25848)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (25847)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.52  % (25845)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (25863)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.52  % (25859)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (25849)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  % (25853)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (25864)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (25857)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (25854)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.53  % (25868)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.53  % (25852)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (25861)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.44/0.54  % (25844)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.44/0.54  % (25844)Refutation not found, incomplete strategy% (25844)------------------------------
% 1.44/0.54  % (25844)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.54  % (25844)Termination reason: Refutation not found, incomplete strategy
% 1.44/0.54  
% 1.44/0.54  % (25844)Memory used [KB]: 10618
% 1.44/0.54  % (25844)Time elapsed: 0.126 s
% 1.44/0.54  % (25844)------------------------------
% 1.44/0.54  % (25844)------------------------------
% 1.44/0.54  % (25858)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.44/0.54  % (25847)Refutation found. Thanks to Tanya!
% 1.44/0.54  % SZS status Theorem for theBenchmark
% 1.44/0.54  % SZS output start Proof for theBenchmark
% 1.44/0.54  fof(f606,plain,(
% 1.44/0.54    $false),
% 1.44/0.54    inference(avatar_sat_refutation,[],[f462,f467,f472,f477,f513,f531,f543,f557,f571,f587,f601])).
% 1.44/0.54  fof(f601,plain,(
% 1.44/0.54    spl17_7),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f600])).
% 1.44/0.54  fof(f600,plain,(
% 1.44/0.54    $false | spl17_7),
% 1.44/0.54    inference(subsumption_resolution,[],[f599,f75])).
% 1.44/0.54  fof(f75,plain,(
% 1.44/0.54    ~v2_struct_0(sK11)),
% 1.44/0.54    inference(cnf_transformation,[],[f44])).
% 1.44/0.54  fof(f44,plain,(
% 1.44/0.54    k15_lattice3(sK11,sK12) != k16_lattice3(sK11,a_2_2_lattice3(sK11,sK12)) & l3_lattices(sK11) & v4_lattice3(sK11) & v10_lattices(sK11) & ~v2_struct_0(sK11)),
% 1.44/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK11,sK12])],[f11,f43,f42])).
% 1.44/0.54  fof(f42,plain,(
% 1.44/0.54    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : k15_lattice3(sK11,X1) != k16_lattice3(sK11,a_2_2_lattice3(sK11,X1)) & l3_lattices(sK11) & v4_lattice3(sK11) & v10_lattices(sK11) & ~v2_struct_0(sK11))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f43,plain,(
% 1.44/0.54    ? [X1] : k15_lattice3(sK11,X1) != k16_lattice3(sK11,a_2_2_lattice3(sK11,X1)) => k15_lattice3(sK11,sK12) != k16_lattice3(sK11,a_2_2_lattice3(sK11,sK12))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f11,plain,(
% 1.44/0.54    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f10])).
% 1.44/0.54  fof(f10,plain,(
% 1.44/0.54    ? [X0] : (? [X1] : k15_lattice3(X0,X1) != k16_lattice3(X0,a_2_2_lattice3(X0,X1)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f9])).
% 1.44/0.54  fof(f9,negated_conjecture,(
% 1.44/0.54    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 1.44/0.54    inference(negated_conjecture,[],[f8])).
% 1.44/0.54  fof(f8,conjecture,(
% 1.44/0.54    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : k15_lattice3(X0,X1) = k16_lattice3(X0,a_2_2_lattice3(X0,X1)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_lattice3)).
% 1.44/0.54  fof(f599,plain,(
% 1.44/0.54    v2_struct_0(sK11) | spl17_7),
% 1.44/0.54    inference(subsumption_resolution,[],[f598,f76])).
% 1.44/0.54  fof(f76,plain,(
% 1.44/0.54    v10_lattices(sK11)),
% 1.44/0.54    inference(cnf_transformation,[],[f44])).
% 1.44/0.54  fof(f598,plain,(
% 1.44/0.54    ~v10_lattices(sK11) | v2_struct_0(sK11) | spl17_7),
% 1.44/0.54    inference(subsumption_resolution,[],[f597,f77])).
% 1.44/0.54  fof(f77,plain,(
% 1.44/0.54    v4_lattice3(sK11)),
% 1.44/0.54    inference(cnf_transformation,[],[f44])).
% 1.44/0.54  fof(f597,plain,(
% 1.44/0.54    ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | spl17_7),
% 1.44/0.54    inference(subsumption_resolution,[],[f594,f78])).
% 1.44/0.54  fof(f78,plain,(
% 1.44/0.54    l3_lattices(sK11)),
% 1.44/0.54    inference(cnf_transformation,[],[f44])).
% 1.44/0.54  fof(f594,plain,(
% 1.44/0.54    ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | spl17_7),
% 1.44/0.54    inference(resolution,[],[f512,f182])).
% 1.44/0.54  fof(f182,plain,(
% 1.44/0.54    ( ! [X0,X1] : (sP3(k15_lattice3(X0,X1),X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(duplicate_literal_removal,[],[f177])).
% 1.44/0.54  fof(f177,plain,(
% 1.44/0.54    ( ! [X0,X1] : (sP3(k15_lattice3(X0,X1),X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(resolution,[],[f97,f115])).
% 1.44/0.54  fof(f115,plain,(
% 1.44/0.54    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f21])).
% 1.44/0.54  fof(f21,plain,(
% 1.44/0.54    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f20])).
% 1.44/0.54  fof(f20,plain,(
% 1.44/0.54    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f5])).
% 1.44/0.54  fof(f5,axiom,(
% 1.44/0.54    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 1.44/0.54  fof(f97,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP3(X1,X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f31])).
% 1.44/0.54  fof(f31,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (sP3(X1,X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.44/0.54    inference(definition_folding,[],[f15,f30,f29,f28])).
% 1.44/0.54  fof(f28,plain,(
% 1.44/0.54    ! [X1,X0,X2] : (sP1(X1,X0,X2) <=> ! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.44/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.44/0.54  fof(f29,plain,(
% 1.44/0.54    ! [X2,X0,X1] : (sP2(X2,X0,X1) <=> (sP1(X1,X0,X2) & r3_lattice3(X0,X1,X2)))),
% 1.44/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.44/0.54  fof(f30,plain,(
% 1.44/0.54    ! [X1,X0] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> sP2(X2,X0,X1)) | ~sP3(X1,X0))),
% 1.44/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.44/0.54  fof(f15,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f14])).
% 1.44/0.54  fof(f14,plain,(
% 1.44/0.54    ! [X0] : (! [X1] : (! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : ((r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r3_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f7])).
% 1.44/0.54  fof(f7,axiom,(
% 1.44/0.54    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (k16_lattice3(X0,X2) = X1 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r3_lattice3(X0,X3,X2) => r3_lattices(X0,X3,X1))) & r3_lattice3(X0,X1,X2)))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_lattice3)).
% 1.44/0.54  fof(f512,plain,(
% 1.44/0.54    ~sP3(k15_lattice3(sK11,sK12),sK11) | spl17_7),
% 1.44/0.54    inference(avatar_component_clause,[],[f510])).
% 1.44/0.54  fof(f510,plain,(
% 1.44/0.54    spl17_7 <=> sP3(k15_lattice3(sK11,sK12),sK11)),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl17_7])])).
% 1.44/0.54  fof(f587,plain,(
% 1.44/0.54    spl17_11),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f586])).
% 1.44/0.54  fof(f586,plain,(
% 1.44/0.54    $false | spl17_11),
% 1.44/0.54    inference(subsumption_resolution,[],[f585,f77])).
% 1.44/0.54  fof(f585,plain,(
% 1.44/0.54    ~v4_lattice3(sK11) | spl17_11),
% 1.44/0.54    inference(subsumption_resolution,[],[f584,f78])).
% 1.44/0.54  fof(f584,plain,(
% 1.44/0.54    ~l3_lattices(sK11) | ~v4_lattice3(sK11) | spl17_11),
% 1.44/0.54    inference(subsumption_resolution,[],[f583,f75])).
% 1.44/0.54  fof(f583,plain,(
% 1.44/0.54    v2_struct_0(sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | spl17_11),
% 1.44/0.54    inference(subsumption_resolution,[],[f580,f76])).
% 1.44/0.54  fof(f580,plain,(
% 1.44/0.54    ~v10_lattices(sK11) | v2_struct_0(sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | spl17_11),
% 1.44/0.54    inference(resolution,[],[f556,f194])).
% 1.44/0.54  fof(f194,plain,(
% 1.44/0.54    ( ! [X2,X3] : (r4_lattice3(X2,k15_lattice3(X2,X3),X3) | ~v10_lattices(X2) | v2_struct_0(X2) | ~l3_lattices(X2) | ~v4_lattice3(X2)) )),
% 1.44/0.54    inference(resolution,[],[f192,f100])).
% 1.44/0.54  fof(f100,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | r4_lattice3(X1,X2,X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f59])).
% 1.44/0.54  fof(f59,plain,(
% 1.44/0.54    ! [X0,X1,X2] : ((sP5(X0,X1,X2) | ~sP4(X2,X1,X0) | ~r4_lattice3(X1,X2,X0)) & ((sP4(X2,X1,X0) & r4_lattice3(X1,X2,X0)) | ~sP5(X0,X1,X2)))),
% 1.44/0.54    inference(rectify,[],[f58])).
% 1.44/0.54  fof(f58,plain,(
% 1.44/0.54    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | ~sP4(X2,X0,X1) | ~r4_lattice3(X0,X2,X1)) & ((sP4(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP5(X1,X0,X2)))),
% 1.44/0.54    inference(flattening,[],[f57])).
% 1.44/0.54  fof(f57,plain,(
% 1.44/0.54    ! [X1,X0,X2] : ((sP5(X1,X0,X2) | (~sP4(X2,X0,X1) | ~r4_lattice3(X0,X2,X1))) & ((sP4(X2,X0,X1) & r4_lattice3(X0,X2,X1)) | ~sP5(X1,X0,X2)))),
% 1.44/0.54    inference(nnf_transformation,[],[f33])).
% 1.44/0.54  fof(f33,plain,(
% 1.44/0.54    ! [X1,X0,X2] : (sP5(X1,X0,X2) <=> (sP4(X2,X0,X1) & r4_lattice3(X0,X2,X1)))),
% 1.44/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 1.44/0.54  fof(f192,plain,(
% 1.44/0.54    ( ! [X0,X1] : (sP5(X1,X0,k15_lattice3(X0,X1)) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f189,f115])).
% 1.44/0.54  fof(f189,plain,(
% 1.44/0.54    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP5(X1,X0,k15_lattice3(X0,X1))) )),
% 1.44/0.54    inference(resolution,[],[f128,f126])).
% 1.44/0.54  fof(f126,plain,(
% 1.44/0.54    ( ! [X2,X1] : (~sP6(k15_lattice3(X1,X2),X1,X2) | sP5(X2,X1,k15_lattice3(X1,X2))) )),
% 1.44/0.54    inference(equality_resolution,[],[f98])).
% 1.44/0.54  fof(f98,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (sP5(X2,X1,X0) | k15_lattice3(X1,X2) != X0 | ~sP6(X0,X1,X2)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f56])).
% 1.44/0.54  fof(f56,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (((k15_lattice3(X1,X2) = X0 | ~sP5(X2,X1,X0)) & (sP5(X2,X1,X0) | k15_lattice3(X1,X2) != X0)) | ~sP6(X0,X1,X2))),
% 1.44/0.54    inference(rectify,[],[f55])).
% 1.44/0.54  fof(f55,plain,(
% 1.44/0.54    ! [X2,X0,X1] : (((k15_lattice3(X0,X1) = X2 | ~sP5(X1,X0,X2)) & (sP5(X1,X0,X2) | k15_lattice3(X0,X1) != X2)) | ~sP6(X2,X0,X1))),
% 1.44/0.54    inference(nnf_transformation,[],[f34])).
% 1.44/0.54  fof(f34,plain,(
% 1.44/0.54    ! [X2,X0,X1] : ((k15_lattice3(X0,X1) = X2 <=> sP5(X1,X0,X2)) | ~sP6(X2,X0,X1))),
% 1.44/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 1.44/0.54  fof(f128,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (sP6(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(duplicate_literal_removal,[],[f107])).
% 1.44/0.54  fof(f107,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (sP6(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f35])).
% 1.44/0.54  fof(f35,plain,(
% 1.44/0.54    ! [X0] : (! [X1,X2] : (sP6(X2,X0,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.44/0.54    inference(definition_folding,[],[f17,f34,f33,f32])).
% 1.44/0.54  fof(f32,plain,(
% 1.44/0.54    ! [X2,X0,X1] : (sP4(X2,X0,X1) <=> ! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.44/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 1.44/0.54  fof(f17,plain,(
% 1.44/0.54    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.44/0.54    inference(flattening,[],[f16])).
% 1.44/0.54  fof(f16,plain,(
% 1.44/0.54    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.44/0.54    inference(ennf_transformation,[],[f4])).
% 1.44/0.54  fof(f4,axiom,(
% 1.44/0.54    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d21_lattice3)).
% 1.44/0.54  fof(f556,plain,(
% 1.44/0.54    ~r4_lattice3(sK11,k15_lattice3(sK11,sK12),sK12) | spl17_11),
% 1.44/0.54    inference(avatar_component_clause,[],[f554])).
% 1.44/0.54  fof(f554,plain,(
% 1.44/0.54    spl17_11 <=> r4_lattice3(sK11,k15_lattice3(sK11,sK12),sK12)),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl17_11])])).
% 1.44/0.54  fof(f571,plain,(
% 1.44/0.54    spl17_5),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f570])).
% 1.44/0.54  fof(f570,plain,(
% 1.44/0.54    $false | spl17_5),
% 1.44/0.54    inference(subsumption_resolution,[],[f569,f75])).
% 1.44/0.54  fof(f569,plain,(
% 1.44/0.54    v2_struct_0(sK11) | spl17_5),
% 1.44/0.54    inference(subsumption_resolution,[],[f565,f78])).
% 1.44/0.54  fof(f565,plain,(
% 1.44/0.54    ~l3_lattices(sK11) | v2_struct_0(sK11) | spl17_5),
% 1.44/0.54    inference(resolution,[],[f504,f115])).
% 1.44/0.54  fof(f504,plain,(
% 1.44/0.54    ~m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) | spl17_5),
% 1.44/0.54    inference(avatar_component_clause,[],[f502])).
% 1.44/0.54  fof(f502,plain,(
% 1.44/0.54    spl17_5 <=> m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11))),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl17_5])])).
% 1.44/0.54  fof(f557,plain,(
% 1.44/0.54    ~spl17_5 | ~spl17_11 | spl17_10),
% 1.44/0.54    inference(avatar_split_clause,[],[f550,f528,f554,f502])).
% 1.44/0.54  fof(f528,plain,(
% 1.44/0.54    spl17_10 <=> sP9(sK12,sK11,k15_lattice3(sK11,sK12))),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl17_10])])).
% 1.44/0.54  fof(f550,plain,(
% 1.44/0.54    ~r4_lattice3(sK11,k15_lattice3(sK11,sK12),sK12) | ~m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) | spl17_10),
% 1.44/0.54    inference(resolution,[],[f530,f127])).
% 1.44/0.54  fof(f127,plain,(
% 1.44/0.54    ( ! [X0,X3,X1] : (sP9(X0,X1,X3) | ~r4_lattice3(X1,X3,X0) | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 1.44/0.54    inference(equality_resolution,[],[f123])).
% 1.44/0.54  fof(f123,plain,(
% 1.44/0.54    ( ! [X2,X0,X3,X1] : (sP9(X0,X1,X2) | ~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1))) )),
% 1.44/0.54    inference(cnf_transformation,[],[f74])).
% 1.44/0.54  fof(f74,plain,(
% 1.44/0.54    ! [X0,X1,X2] : ((sP9(X0,X1,X2) | ! [X3] : (~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & ((r4_lattice3(X1,sK16(X0,X1,X2),X0) & sK16(X0,X1,X2) = X2 & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))) | ~sP9(X0,X1,X2)))),
% 1.44/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK16])],[f72,f73])).
% 1.44/0.54  fof(f73,plain,(
% 1.44/0.54    ! [X2,X1,X0] : (? [X4] : (r4_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) => (r4_lattice3(X1,sK16(X0,X1,X2),X0) & sK16(X0,X1,X2) = X2 & m1_subset_1(sK16(X0,X1,X2),u1_struct_0(X1))))),
% 1.44/0.54    introduced(choice_axiom,[])).
% 1.44/0.54  fof(f72,plain,(
% 1.44/0.54    ! [X0,X1,X2] : ((sP9(X0,X1,X2) | ! [X3] : (~r4_lattice3(X1,X3,X0) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X4] : (r4_lattice3(X1,X4,X0) & X2 = X4 & m1_subset_1(X4,u1_struct_0(X1))) | ~sP9(X0,X1,X2)))),
% 1.44/0.54    inference(rectify,[],[f71])).
% 1.44/0.54  fof(f71,plain,(
% 1.44/0.54    ! [X2,X1,X0] : ((sP9(X2,X1,X0) | ! [X3] : (~r4_lattice3(X1,X3,X2) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP9(X2,X1,X0)))),
% 1.44/0.54    inference(nnf_transformation,[],[f39])).
% 1.44/0.54  fof(f39,plain,(
% 1.44/0.54    ! [X2,X1,X0] : (sP9(X2,X1,X0) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 1.44/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP9])])).
% 1.44/0.54  fof(f530,plain,(
% 1.44/0.54    ~sP9(sK12,sK11,k15_lattice3(sK11,sK12)) | spl17_10),
% 1.44/0.54    inference(avatar_component_clause,[],[f528])).
% 1.44/0.54  fof(f543,plain,(
% 1.44/0.54    spl17_9),
% 1.44/0.54    inference(avatar_contradiction_clause,[],[f542])).
% 1.44/0.54  fof(f542,plain,(
% 1.44/0.54    $false | spl17_9),
% 1.44/0.54    inference(subsumption_resolution,[],[f541,f75])).
% 1.44/0.54  fof(f541,plain,(
% 1.44/0.54    v2_struct_0(sK11) | spl17_9),
% 1.44/0.54    inference(subsumption_resolution,[],[f540,f76])).
% 1.44/0.54  fof(f540,plain,(
% 1.44/0.54    ~v10_lattices(sK11) | v2_struct_0(sK11) | spl17_9),
% 1.44/0.54    inference(subsumption_resolution,[],[f539,f77])).
% 1.44/0.54  fof(f539,plain,(
% 1.44/0.54    ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | spl17_9),
% 1.44/0.54    inference(subsumption_resolution,[],[f536,f78])).
% 1.44/0.54  fof(f536,plain,(
% 1.44/0.54    ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~v10_lattices(sK11) | v2_struct_0(sK11) | spl17_9),
% 1.44/0.54    inference(resolution,[],[f526,f124])).
% 1.44/0.54  fof(f124,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (sP10(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f41])).
% 1.44/0.54  fof(f41,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (sP10(X0,X1,X2) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.44/0.54    inference(definition_folding,[],[f25,f40,f39])).
% 1.44/0.54  fof(f40,plain,(
% 1.44/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> sP9(X2,X1,X0)) | ~sP10(X0,X1,X2))),
% 1.44/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP10])])).
% 1.44/0.54  fof(f25,plain,(
% 1.44/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1))),
% 1.44/0.54    inference(flattening,[],[f24])).
% 1.44/0.54  fof(f24,plain,(
% 1.44/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)))),
% 1.44/0.54    inference(ennf_transformation,[],[f6])).
% 1.44/0.54  fof(f6,axiom,(
% 1.44/0.54    ! [X0,X1,X2] : ((l3_lattices(X1) & v4_lattice3(X1) & v10_lattices(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_2_lattice3(X1,X2)) <=> ? [X3] : (r4_lattice3(X1,X3,X2) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.44/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_2_lattice3)).
% 1.44/0.54  fof(f526,plain,(
% 1.44/0.54    ~sP10(k15_lattice3(sK11,sK12),sK11,sK12) | spl17_9),
% 1.44/0.54    inference(avatar_component_clause,[],[f524])).
% 1.44/0.54  fof(f524,plain,(
% 1.44/0.54    spl17_9 <=> sP10(k15_lattice3(sK11,sK12),sK11,sK12)),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl17_9])])).
% 1.44/0.54  fof(f531,plain,(
% 1.44/0.54    ~spl17_9 | ~spl17_10 | spl17_6),
% 1.44/0.54    inference(avatar_split_clause,[],[f520,f506,f528,f524])).
% 1.44/0.54  fof(f506,plain,(
% 1.44/0.54    spl17_6 <=> r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12))),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl17_6])])).
% 1.44/0.54  fof(f520,plain,(
% 1.44/0.54    ~sP9(sK12,sK11,k15_lattice3(sK11,sK12)) | ~sP10(k15_lattice3(sK11,sK12),sK11,sK12) | spl17_6),
% 1.44/0.54    inference(resolution,[],[f508,f119])).
% 1.44/0.54  fof(f119,plain,(
% 1.44/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~sP9(X2,X1,X0) | ~sP10(X0,X1,X2)) )),
% 1.44/0.54    inference(cnf_transformation,[],[f70])).
% 1.44/0.54  fof(f70,plain,(
% 1.44/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_2_lattice3(X1,X2)) | ~sP9(X2,X1,X0)) & (sP9(X2,X1,X0) | ~r2_hidden(X0,a_2_2_lattice3(X1,X2)))) | ~sP10(X0,X1,X2))),
% 1.44/0.54    inference(nnf_transformation,[],[f40])).
% 1.44/0.54  fof(f508,plain,(
% 1.44/0.54    ~r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12)) | spl17_6),
% 1.44/0.54    inference(avatar_component_clause,[],[f506])).
% 1.44/0.54  fof(f513,plain,(
% 1.44/0.54    ~spl17_5 | ~spl17_6 | ~spl17_7 | ~spl17_4),
% 1.44/0.54    inference(avatar_split_clause,[],[f500,f460,f510,f506,f502])).
% 1.44/0.54  fof(f460,plain,(
% 1.44/0.54    spl17_4 <=> ! [X0] : (~r2_hidden(X0,a_2_2_lattice3(sK11,sK12)) | ~sP3(X0,sK11) | k15_lattice3(sK11,sK12) != X0 | ~r3_lattice3(sK11,X0,a_2_2_lattice3(sK11,sK12)) | ~m1_subset_1(X0,u1_struct_0(sK11)))),
% 1.44/0.54    introduced(avatar_definition,[new_symbols(naming,[spl17_4])])).
% 1.44/0.54  fof(f500,plain,(
% 1.44/0.54    ~sP3(k15_lattice3(sK11,sK12),sK11) | ~r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12)) | ~m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) | ~spl17_4),
% 1.44/0.54    inference(subsumption_resolution,[],[f499,f77])).
% 1.44/0.54  fof(f499,plain,(
% 1.44/0.54    ~sP3(k15_lattice3(sK11,sK12),sK11) | ~r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12)) | ~m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) | ~v4_lattice3(sK11) | ~spl17_4),
% 1.44/0.54    inference(subsumption_resolution,[],[f498,f78])).
% 1.44/0.54  fof(f498,plain,(
% 1.44/0.54    ~sP3(k15_lattice3(sK11,sK12),sK11) | ~r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12)) | ~m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~spl17_4),
% 1.44/0.54    inference(subsumption_resolution,[],[f497,f76])).
% 1.44/0.54  fof(f497,plain,(
% 1.44/0.54    ~sP3(k15_lattice3(sK11,sK12),sK11) | ~r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12)) | ~m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) | ~v10_lattices(sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~spl17_4),
% 1.44/0.54    inference(subsumption_resolution,[],[f491,f75])).
% 1.44/0.54  fof(f491,plain,(
% 1.44/0.54    ~sP3(k15_lattice3(sK11,sK12),sK11) | ~r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12)) | ~m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) | v2_struct_0(sK11) | ~v10_lattices(sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~spl17_4),
% 1.44/0.54    inference(trivial_inequality_removal,[],[f487])).
% 1.44/0.54  fof(f487,plain,(
% 1.44/0.54    ~sP3(k15_lattice3(sK11,sK12),sK11) | k15_lattice3(sK11,sK12) != k15_lattice3(sK11,sK12) | ~r2_hidden(k15_lattice3(sK11,sK12),a_2_2_lattice3(sK11,sK12)) | ~m1_subset_1(k15_lattice3(sK11,sK12),u1_struct_0(sK11)) | v2_struct_0(sK11) | ~v10_lattices(sK11) | ~l3_lattices(sK11) | ~v4_lattice3(sK11) | ~spl17_4),
% 1.44/0.54    inference(resolution,[],[f461,f294])).
% 1.44/0.54  fof(f294,plain,(
% 1.44/0.54    ( ! [X4,X3] : (r3_lattice3(X3,k15_lattice3(X3,X4),a_2_2_lattice3(X3,X4)) | v2_struct_0(X3) | ~v10_lattices(X3) | ~l3_lattices(X3) | ~v4_lattice3(X3)) )),
% 1.44/0.54    inference(subsumption_resolution,[],[f292,f142])).
% 1.44/0.54  fof(f142,plain,(
% 1.44/0.54    ( ! [X0,X1] : (sP8(X0,k15_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(duplicate_literal_removal,[],[f138])).
% 1.44/0.54  fof(f138,plain,(
% 1.44/0.54    ( ! [X0,X1] : (sP8(X0,k15_lattice3(X0,X1)) | ~l3_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.44/0.54    inference(resolution,[],[f114,f115])).
% 1.44/0.54  % (25867)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.44/0.55  % (25866)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.44/0.55  % (25860)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.59/0.56  fof(f114,plain,(
% 1.59/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP8(X0,X1) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f38])).
% 1.59/0.56  fof(f38,plain,(
% 1.59/0.56    ! [X0] : (! [X1] : (sP8(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.56    inference(definition_folding,[],[f19,f37,f36])).
% 1.59/0.56  fof(f36,plain,(
% 1.59/0.56    ! [X1,X0,X2] : (sP7(X1,X0,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))))),
% 1.59/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 1.59/0.56  fof(f37,plain,(
% 1.59/0.56    ! [X0,X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> sP7(X1,X0,X2)) | ~sP8(X0,X1))),
% 1.59/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP8])])).
% 1.59/0.56  fof(f19,plain,(
% 1.59/0.56    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.56    inference(flattening,[],[f18])).
% 1.59/0.56  fof(f18,plain,(
% 1.59/0.56    ! [X0] : (! [X1] : (! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.56    inference(ennf_transformation,[],[f3])).
% 1.59/0.56  fof(f3,axiom,(
% 1.59/0.56    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r3_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X1,X3))))))),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattice3)).
% 1.59/0.56  fof(f292,plain,(
% 1.59/0.56    ( ! [X4,X3] : (~v4_lattice3(X3) | v2_struct_0(X3) | ~v10_lattices(X3) | ~l3_lattices(X3) | r3_lattice3(X3,k15_lattice3(X3,X4),a_2_2_lattice3(X3,X4)) | ~sP8(X3,k15_lattice3(X3,X4))) )),
% 1.59/0.56    inference(resolution,[],[f290,f109])).
% 1.59/0.56  fof(f109,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (~sP7(X1,X0,X2) | r3_lattice3(X0,X1,X2) | ~sP8(X0,X1)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f64])).
% 1.59/0.56  fof(f64,plain,(
% 1.59/0.56    ! [X0,X1] : (! [X2] : ((r3_lattice3(X0,X1,X2) | ~sP7(X1,X0,X2)) & (sP7(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) | ~sP8(X0,X1))),
% 1.59/0.56    inference(nnf_transformation,[],[f37])).
% 1.59/0.56  fof(f290,plain,(
% 1.59/0.56    ( ! [X0,X1] : (sP7(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1)) | ~v4_lattice3(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | ~l3_lattices(X0)) )),
% 1.59/0.56    inference(duplicate_literal_removal,[],[f288])).
% 1.59/0.56  fof(f288,plain,(
% 1.59/0.56    ( ! [X0,X1] : (~l3_lattices(X0) | ~v4_lattice3(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | sP7(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | sP7(k15_lattice3(X0,X1),X0,a_2_2_lattice3(X0,X1))) )),
% 1.59/0.56    inference(resolution,[],[f243,f270])).
% 1.59/0.56  fof(f270,plain,(
% 1.59/0.56    ( ! [X10,X8,X11,X9] : (r4_lattice3(X10,sK15(X8,X9,a_2_2_lattice3(X10,X11)),X11) | ~l3_lattices(X10) | ~v4_lattice3(X10) | ~v10_lattices(X10) | v2_struct_0(X10) | sP7(X8,X9,a_2_2_lattice3(X10,X11))) )),
% 1.59/0.56    inference(resolution,[],[f225,f147])).
% 1.59/0.56  fof(f147,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (~sP9(X0,X1,X2) | r4_lattice3(X1,X2,X0)) )),
% 1.59/0.56    inference(duplicate_literal_removal,[],[f146])).
% 1.59/0.56  fof(f146,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (r4_lattice3(X1,X2,X0) | ~sP9(X0,X1,X2) | ~sP9(X0,X1,X2)) )),
% 1.59/0.56    inference(superposition,[],[f122,f121])).
% 1.59/0.56  fof(f121,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (sK16(X0,X1,X2) = X2 | ~sP9(X0,X1,X2)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f74])).
% 1.59/0.56  fof(f122,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (r4_lattice3(X1,sK16(X0,X1,X2),X0) | ~sP9(X0,X1,X2)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f74])).
% 1.59/0.56  fof(f225,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (sP9(X0,X1,sK15(X2,X3,a_2_2_lattice3(X1,X0))) | sP7(X2,X3,a_2_2_lattice3(X1,X0)) | ~l3_lattices(X1) | ~v4_lattice3(X1) | ~v10_lattices(X1) | v2_struct_0(X1)) )),
% 1.59/0.56    inference(resolution,[],[f174,f124])).
% 1.59/0.56  fof(f174,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (~sP10(sK15(X2,X3,a_2_2_lattice3(X1,X0)),X1,X0) | sP9(X0,X1,sK15(X2,X3,a_2_2_lattice3(X1,X0))) | sP7(X2,X3,a_2_2_lattice3(X1,X0))) )),
% 1.59/0.56    inference(resolution,[],[f118,f112])).
% 1.59/0.56  fof(f112,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (r2_hidden(sK15(X0,X1,X2),X2) | sP7(X0,X1,X2)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f68])).
% 1.59/0.56  fof(f68,plain,(
% 1.59/0.56    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | (~r1_lattices(X1,X0,sK15(X0,X1,X2)) & r2_hidden(sK15(X0,X1,X2),X2) & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 1.59/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK15])],[f66,f67])).
% 1.59/0.56  fof(f67,plain,(
% 1.59/0.56    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK15(X0,X1,X2)) & r2_hidden(sK15(X0,X1,X2),X2) & m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1))))),
% 1.59/0.56    introduced(choice_axiom,[])).
% 1.59/0.56  fof(f66,plain,(
% 1.59/0.56    ! [X0,X1,X2] : ((sP7(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP7(X0,X1,X2)))),
% 1.59/0.56    inference(rectify,[],[f65])).
% 1.59/0.56  fof(f65,plain,(
% 1.59/0.56    ! [X1,X0,X2] : ((sP7(X1,X0,X2) | ? [X3] : (~r1_lattices(X0,X1,X3) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X1,X3) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP7(X1,X0,X2)))),
% 1.59/0.56    inference(nnf_transformation,[],[f36])).
% 1.59/0.56  fof(f118,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_2_lattice3(X1,X2)) | sP9(X2,X1,X0) | ~sP10(X0,X1,X2)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f70])).
% 1.59/0.56  fof(f243,plain,(
% 1.59/0.56    ( ! [X4,X5,X3] : (~r4_lattice3(X3,sK15(k15_lattice3(X3,X4),X3,X5),X4) | ~l3_lattices(X3) | ~v4_lattice3(X3) | v2_struct_0(X3) | ~v10_lattices(X3) | sP7(k15_lattice3(X3,X4),X3,X5)) )),
% 1.59/0.56    inference(subsumption_resolution,[],[f238,f111])).
% 1.59/0.56  fof(f111,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK15(X0,X1,X2),u1_struct_0(X1)) | sP7(X0,X1,X2)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f68])).
% 1.59/0.56  fof(f238,plain,(
% 1.59/0.56    ( ! [X4,X5,X3] : (v2_struct_0(X3) | ~l3_lattices(X3) | ~v4_lattice3(X3) | ~r4_lattice3(X3,sK15(k15_lattice3(X3,X4),X3,X5),X4) | ~m1_subset_1(sK15(k15_lattice3(X3,X4),X3,X5),u1_struct_0(X3)) | ~v10_lattices(X3) | sP7(k15_lattice3(X3,X4),X3,X5)) )),
% 1.59/0.56    inference(resolution,[],[f196,f113])).
% 1.59/0.56  fof(f113,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (~r1_lattices(X1,X0,sK15(X0,X1,X2)) | sP7(X0,X1,X2)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f68])).
% 1.59/0.56  fof(f196,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X2),X1) | v2_struct_0(X0) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~r4_lattice3(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v10_lattices(X0)) )),
% 1.59/0.56    inference(resolution,[],[f193,f103])).
% 1.59/0.56  fof(f103,plain,(
% 1.59/0.56    ( ! [X4,X2,X0,X1] : (~sP4(X0,X1,X2) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f63])).
% 1.59/0.56  fof(f63,plain,(
% 1.59/0.56    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | (~r1_lattices(X1,X0,sK14(X0,X1,X2)) & r4_lattice3(X1,sK14(X0,X1,X2),X2) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 1.59/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f61,f62])).
% 1.59/0.56  fof(f62,plain,(
% 1.59/0.56    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r1_lattices(X1,X0,sK14(X0,X1,X2)) & r4_lattice3(X1,sK14(X0,X1,X2),X2) & m1_subset_1(sK14(X0,X1,X2),u1_struct_0(X1))))),
% 1.59/0.56    introduced(choice_axiom,[])).
% 1.59/0.56  fof(f61,plain,(
% 1.59/0.56    ! [X0,X1,X2] : ((sP4(X0,X1,X2) | ? [X3] : (~r1_lattices(X1,X0,X3) & r4_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r1_lattices(X1,X0,X4) | ~r4_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP4(X0,X1,X2)))),
% 1.59/0.56    inference(rectify,[],[f60])).
% 1.59/0.56  fof(f60,plain,(
% 1.59/0.56    ! [X2,X0,X1] : ((sP4(X2,X0,X1) | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP4(X2,X0,X1)))),
% 1.59/0.56    inference(nnf_transformation,[],[f32])).
% 1.59/0.56  fof(f193,plain,(
% 1.59/0.56    ( ! [X0,X1] : (sP4(k15_lattice3(X0,X1),X0,X1) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | ~v4_lattice3(X0)) )),
% 1.59/0.56    inference(resolution,[],[f192,f101])).
% 1.59/0.56  fof(f101,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (~sP5(X0,X1,X2) | sP4(X2,X1,X0)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f59])).
% 1.59/0.56  fof(f461,plain,(
% 1.59/0.56    ( ! [X0] : (~r3_lattice3(sK11,X0,a_2_2_lattice3(sK11,sK12)) | ~sP3(X0,sK11) | k15_lattice3(sK11,sK12) != X0 | ~r2_hidden(X0,a_2_2_lattice3(sK11,sK12)) | ~m1_subset_1(X0,u1_struct_0(sK11))) ) | ~spl17_4),
% 1.59/0.56    inference(avatar_component_clause,[],[f460])).
% 1.59/0.56  fof(f477,plain,(
% 1.59/0.56    spl17_3),
% 1.59/0.56    inference(avatar_contradiction_clause,[],[f476])).
% 1.59/0.56  fof(f476,plain,(
% 1.59/0.56    $false | spl17_3),
% 1.59/0.56    inference(subsumption_resolution,[],[f475,f76])).
% 1.59/0.56  fof(f475,plain,(
% 1.59/0.56    ~v10_lattices(sK11) | spl17_3),
% 1.59/0.56    inference(subsumption_resolution,[],[f474,f78])).
% 1.59/0.56  fof(f474,plain,(
% 1.59/0.56    ~l3_lattices(sK11) | ~v10_lattices(sK11) | spl17_3),
% 1.59/0.56    inference(subsumption_resolution,[],[f473,f75])).
% 1.59/0.56  fof(f473,plain,(
% 1.59/0.56    v2_struct_0(sK11) | ~l3_lattices(sK11) | ~v10_lattices(sK11) | spl17_3),
% 1.59/0.56    inference(resolution,[],[f458,f135])).
% 1.59/0.56  fof(f135,plain,(
% 1.59/0.56    ( ! [X6] : (v9_lattices(X6) | v2_struct_0(X6) | ~l3_lattices(X6) | ~v10_lattices(X6)) )),
% 1.59/0.56    inference(resolution,[],[f87,f86])).
% 1.59/0.56  fof(f86,plain,(
% 1.59/0.56    ( ! [X0] : (~sP0(X0) | v9_lattices(X0)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f45])).
% 1.59/0.56  fof(f45,plain,(
% 1.59/0.56    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 1.59/0.56    inference(nnf_transformation,[],[f26])).
% 1.59/0.56  fof(f26,plain,(
% 1.59/0.56    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~sP0(X0))),
% 1.59/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.59/0.56  fof(f87,plain,(
% 1.59/0.56    ( ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f27])).
% 1.59/0.56  fof(f27,plain,(
% 1.59/0.56    ! [X0] : (sP0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.59/0.56    inference(definition_folding,[],[f13,f26])).
% 1.59/0.56  fof(f13,plain,(
% 1.59/0.56    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 1.59/0.56    inference(flattening,[],[f12])).
% 1.59/0.56  fof(f12,plain,(
% 1.59/0.56    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 1.59/0.56    inference(ennf_transformation,[],[f1])).
% 1.59/0.56  fof(f1,axiom,(
% 1.59/0.56    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 1.59/0.56  fof(f458,plain,(
% 1.59/0.56    ~v9_lattices(sK11) | spl17_3),
% 1.59/0.56    inference(avatar_component_clause,[],[f456])).
% 1.59/0.56  fof(f456,plain,(
% 1.59/0.56    spl17_3 <=> v9_lattices(sK11)),
% 1.59/0.56    introduced(avatar_definition,[new_symbols(naming,[spl17_3])])).
% 1.59/0.56  fof(f472,plain,(
% 1.59/0.56    spl17_2),
% 1.59/0.56    inference(avatar_contradiction_clause,[],[f471])).
% 1.59/0.56  fof(f471,plain,(
% 1.59/0.56    $false | spl17_2),
% 1.59/0.56    inference(subsumption_resolution,[],[f470,f76])).
% 1.59/0.56  fof(f470,plain,(
% 1.59/0.56    ~v10_lattices(sK11) | spl17_2),
% 1.59/0.56    inference(subsumption_resolution,[],[f469,f78])).
% 1.59/0.56  fof(f469,plain,(
% 1.59/0.56    ~l3_lattices(sK11) | ~v10_lattices(sK11) | spl17_2),
% 1.59/0.56    inference(subsumption_resolution,[],[f468,f75])).
% 1.59/0.56  fof(f468,plain,(
% 1.59/0.56    v2_struct_0(sK11) | ~l3_lattices(sK11) | ~v10_lattices(sK11) | spl17_2),
% 1.59/0.56    inference(resolution,[],[f454,f134])).
% 1.59/0.56  fof(f134,plain,(
% 1.59/0.56    ( ! [X5] : (v8_lattices(X5) | v2_struct_0(X5) | ~l3_lattices(X5) | ~v10_lattices(X5)) )),
% 1.59/0.56    inference(resolution,[],[f87,f85])).
% 1.59/0.56  fof(f85,plain,(
% 1.59/0.56    ( ! [X0] : (~sP0(X0) | v8_lattices(X0)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f45])).
% 1.59/0.56  fof(f454,plain,(
% 1.59/0.56    ~v8_lattices(sK11) | spl17_2),
% 1.59/0.56    inference(avatar_component_clause,[],[f452])).
% 1.59/0.56  fof(f452,plain,(
% 1.59/0.56    spl17_2 <=> v8_lattices(sK11)),
% 1.59/0.56    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).
% 1.59/0.56  fof(f467,plain,(
% 1.59/0.56    spl17_1),
% 1.59/0.56    inference(avatar_contradiction_clause,[],[f466])).
% 1.59/0.56  fof(f466,plain,(
% 1.59/0.56    $false | spl17_1),
% 1.59/0.56    inference(subsumption_resolution,[],[f465,f76])).
% 1.59/0.56  fof(f465,plain,(
% 1.59/0.56    ~v10_lattices(sK11) | spl17_1),
% 1.59/0.56    inference(subsumption_resolution,[],[f464,f78])).
% 1.59/0.56  fof(f464,plain,(
% 1.59/0.56    ~l3_lattices(sK11) | ~v10_lattices(sK11) | spl17_1),
% 1.59/0.56    inference(subsumption_resolution,[],[f463,f75])).
% 1.59/0.56  fof(f463,plain,(
% 1.59/0.56    v2_struct_0(sK11) | ~l3_lattices(sK11) | ~v10_lattices(sK11) | spl17_1),
% 1.59/0.56    inference(resolution,[],[f450,f132])).
% 1.59/0.56  fof(f132,plain,(
% 1.59/0.56    ( ! [X3] : (v6_lattices(X3) | v2_struct_0(X3) | ~l3_lattices(X3) | ~v10_lattices(X3)) )),
% 1.59/0.56    inference(resolution,[],[f87,f83])).
% 1.59/0.56  fof(f83,plain,(
% 1.59/0.56    ( ! [X0] : (~sP0(X0) | v6_lattices(X0)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f45])).
% 1.59/0.56  fof(f450,plain,(
% 1.59/0.56    ~v6_lattices(sK11) | spl17_1),
% 1.59/0.56    inference(avatar_component_clause,[],[f448])).
% 1.59/0.56  fof(f448,plain,(
% 1.59/0.56    spl17_1 <=> v6_lattices(sK11)),
% 1.59/0.56    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).
% 1.59/0.56  fof(f462,plain,(
% 1.59/0.56    ~spl17_1 | ~spl17_2 | ~spl17_3 | spl17_4),
% 1.59/0.56    inference(avatar_split_clause,[],[f446,f460,f456,f452,f448])).
% 1.59/0.56  fof(f446,plain,(
% 1.59/0.56    ( ! [X0] : (~r2_hidden(X0,a_2_2_lattice3(sK11,sK12)) | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~v9_lattices(sK11) | ~v8_lattices(sK11) | ~v6_lattices(sK11) | ~r3_lattice3(sK11,X0,a_2_2_lattice3(sK11,sK12)) | k15_lattice3(sK11,sK12) != X0 | ~sP3(X0,sK11)) )),
% 1.59/0.56    inference(subsumption_resolution,[],[f445,f75])).
% 1.59/0.56  fof(f445,plain,(
% 1.59/0.56    ( ! [X0] : (~r2_hidden(X0,a_2_2_lattice3(sK11,sK12)) | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~v9_lattices(sK11) | ~v8_lattices(sK11) | ~v6_lattices(sK11) | v2_struct_0(sK11) | ~r3_lattice3(sK11,X0,a_2_2_lattice3(sK11,sK12)) | k15_lattice3(sK11,sK12) != X0 | ~sP3(X0,sK11)) )),
% 1.59/0.56    inference(subsumption_resolution,[],[f442,f78])).
% 1.59/0.56  fof(f442,plain,(
% 1.59/0.56    ( ! [X0] : (~r2_hidden(X0,a_2_2_lattice3(sK11,sK12)) | ~m1_subset_1(X0,u1_struct_0(sK11)) | ~l3_lattices(sK11) | ~v9_lattices(sK11) | ~v8_lattices(sK11) | ~v6_lattices(sK11) | v2_struct_0(sK11) | ~r3_lattice3(sK11,X0,a_2_2_lattice3(sK11,sK12)) | k15_lattice3(sK11,sK12) != X0 | ~sP3(X0,sK11)) )),
% 1.59/0.56    inference(resolution,[],[f437,f162])).
% 1.59/0.56  fof(f162,plain,(
% 1.59/0.56    ( ! [X6] : (~sP1(X6,sK11,a_2_2_lattice3(sK11,sK12)) | ~r3_lattice3(sK11,X6,a_2_2_lattice3(sK11,sK12)) | k15_lattice3(sK11,sK12) != X6 | ~sP3(X6,sK11)) )),
% 1.59/0.56    inference(resolution,[],[f92,f151])).
% 1.59/0.56  fof(f151,plain,(
% 1.59/0.56    ( ! [X0] : (~sP2(a_2_2_lattice3(sK11,sK12),sK11,X0) | k15_lattice3(sK11,sK12) != X0 | ~sP3(X0,sK11)) )),
% 1.59/0.56    inference(superposition,[],[f79,f89])).
% 1.59/0.56  fof(f89,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (k16_lattice3(X1,X2) = X0 | ~sP2(X2,X1,X0) | ~sP3(X0,X1)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f47])).
% 1.59/0.56  fof(f47,plain,(
% 1.59/0.56    ! [X0,X1] : (! [X2] : ((k16_lattice3(X1,X2) = X0 | ~sP2(X2,X1,X0)) & (sP2(X2,X1,X0) | k16_lattice3(X1,X2) != X0)) | ~sP3(X0,X1))),
% 1.59/0.56    inference(rectify,[],[f46])).
% 1.59/0.56  fof(f46,plain,(
% 1.59/0.56    ! [X1,X0] : (! [X2] : ((k16_lattice3(X0,X2) = X1 | ~sP2(X2,X0,X1)) & (sP2(X2,X0,X1) | k16_lattice3(X0,X2) != X1)) | ~sP3(X1,X0))),
% 1.59/0.56    inference(nnf_transformation,[],[f30])).
% 1.59/0.56  fof(f79,plain,(
% 1.59/0.56    k15_lattice3(sK11,sK12) != k16_lattice3(sK11,a_2_2_lattice3(sK11,sK12))),
% 1.59/0.56    inference(cnf_transformation,[],[f44])).
% 1.59/0.56  fof(f92,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (sP2(X0,X1,X2) | ~sP1(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f50])).
% 1.59/0.56  fof(f50,plain,(
% 1.59/0.56    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ~sP1(X2,X1,X0) | ~r3_lattice3(X1,X2,X0)) & ((sP1(X2,X1,X0) & r3_lattice3(X1,X2,X0)) | ~sP2(X0,X1,X2)))),
% 1.59/0.56    inference(rectify,[],[f49])).
% 1.59/0.56  fof(f49,plain,(
% 1.59/0.56    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | ~sP1(X1,X0,X2) | ~r3_lattice3(X0,X1,X2)) & ((sP1(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP2(X2,X0,X1)))),
% 1.59/0.56    inference(flattening,[],[f48])).
% 1.59/0.56  fof(f48,plain,(
% 1.59/0.56    ! [X2,X0,X1] : ((sP2(X2,X0,X1) | (~sP1(X1,X0,X2) | ~r3_lattice3(X0,X1,X2))) & ((sP1(X1,X0,X2) & r3_lattice3(X0,X1,X2)) | ~sP2(X2,X0,X1)))),
% 1.59/0.56    inference(nnf_transformation,[],[f29])).
% 1.59/0.56  fof(f437,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~r2_hidden(X0,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v9_lattices(X2) | ~v8_lattices(X2) | ~v6_lattices(X2) | v2_struct_0(X2)) )),
% 1.59/0.56    inference(duplicate_literal_removal,[],[f432])).
% 1.59/0.56  fof(f432,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | sP1(X0,X2,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | ~l3_lattices(X2) | ~v9_lattices(X2) | ~v8_lattices(X2) | ~v6_lattices(X2) | v2_struct_0(X2) | sP1(X0,X2,X1)) )),
% 1.59/0.56    inference(resolution,[],[f308,f96])).
% 1.59/0.56  fof(f96,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (~r3_lattices(X1,sK13(X0,X1,X2),X0) | sP1(X0,X1,X2)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f54])).
% 1.59/0.56  fof(f54,plain,(
% 1.59/0.56    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | (~r3_lattices(X1,sK13(X0,X1,X2),X0) & r3_lattice3(X1,sK13(X0,X1,X2),X2) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 1.59/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13])],[f52,f53])).
% 1.59/0.56  fof(f53,plain,(
% 1.59/0.56    ! [X2,X1,X0] : (? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1))) => (~r3_lattices(X1,sK13(X0,X1,X2),X0) & r3_lattice3(X1,sK13(X0,X1,X2),X2) & m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1))))),
% 1.59/0.56    introduced(choice_axiom,[])).
% 1.59/0.56  fof(f52,plain,(
% 1.59/0.56    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ? [X3] : (~r3_lattices(X1,X3,X0) & r3_lattice3(X1,X3,X2) & m1_subset_1(X3,u1_struct_0(X1)))) & (! [X4] : (r3_lattices(X1,X4,X0) | ~r3_lattice3(X1,X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) | ~sP1(X0,X1,X2)))),
% 1.59/0.56    inference(rectify,[],[f51])).
% 1.59/0.56  fof(f51,plain,(
% 1.59/0.56    ! [X1,X0,X2] : ((sP1(X1,X0,X2) | ? [X3] : (~r3_lattices(X0,X3,X1) & r3_lattice3(X0,X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r3_lattices(X0,X3,X1) | ~r3_lattice3(X0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~sP1(X1,X0,X2)))),
% 1.59/0.56    inference(nnf_transformation,[],[f28])).
% 1.59/0.56  fof(f308,plain,(
% 1.59/0.56    ( ! [X10,X8,X11,X9] : (r3_lattices(X9,sK13(X11,X9,X10),X8) | ~r2_hidden(X8,X10) | sP1(X11,X9,X10) | ~m1_subset_1(X8,u1_struct_0(X9)) | ~l3_lattices(X9) | ~v9_lattices(X9) | ~v8_lattices(X9) | ~v6_lattices(X9) | v2_struct_0(X9)) )),
% 1.59/0.56    inference(subsumption_resolution,[],[f307,f94])).
% 1.59/0.56  fof(f94,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (m1_subset_1(sK13(X0,X1,X2),u1_struct_0(X1)) | sP1(X0,X1,X2)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f54])).
% 1.59/0.56  fof(f307,plain,(
% 1.59/0.56    ( ! [X10,X8,X11,X9] : (~m1_subset_1(X8,u1_struct_0(X9)) | ~r2_hidden(X8,X10) | sP1(X11,X9,X10) | r3_lattices(X9,sK13(X11,X9,X10),X8) | ~m1_subset_1(sK13(X11,X9,X10),u1_struct_0(X9)) | ~l3_lattices(X9) | ~v9_lattices(X9) | ~v8_lattices(X9) | ~v6_lattices(X9) | v2_struct_0(X9)) )),
% 1.59/0.56    inference(subsumption_resolution,[],[f304,f114])).
% 1.59/0.56  fof(f304,plain,(
% 1.59/0.56    ( ! [X10,X8,X11,X9] : (~m1_subset_1(X8,u1_struct_0(X9)) | ~r2_hidden(X8,X10) | ~sP8(X9,sK13(X11,X9,X10)) | sP1(X11,X9,X10) | r3_lattices(X9,sK13(X11,X9,X10),X8) | ~m1_subset_1(sK13(X11,X9,X10),u1_struct_0(X9)) | ~l3_lattices(X9) | ~v9_lattices(X9) | ~v8_lattices(X9) | ~v6_lattices(X9) | v2_struct_0(X9)) )),
% 1.59/0.56    inference(duplicate_literal_removal,[],[f303])).
% 1.59/0.56  fof(f303,plain,(
% 1.59/0.56    ( ! [X10,X8,X11,X9] : (~m1_subset_1(X8,u1_struct_0(X9)) | ~r2_hidden(X8,X10) | ~sP8(X9,sK13(X11,X9,X10)) | sP1(X11,X9,X10) | r3_lattices(X9,sK13(X11,X9,X10),X8) | ~m1_subset_1(X8,u1_struct_0(X9)) | ~m1_subset_1(sK13(X11,X9,X10),u1_struct_0(X9)) | ~l3_lattices(X9) | ~v9_lattices(X9) | ~v8_lattices(X9) | ~v6_lattices(X9) | v2_struct_0(X9)) )),
% 1.59/0.56    inference(resolution,[],[f213,f117])).
% 1.59/0.56  fof(f117,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f69])).
% 1.59/0.56  fof(f69,plain,(
% 1.59/0.56    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.56    inference(nnf_transformation,[],[f23])).
% 1.59/0.56  fof(f23,plain,(
% 1.59/0.56    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 1.59/0.56    inference(flattening,[],[f22])).
% 1.59/0.56  fof(f22,plain,(
% 1.59/0.56    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 1.59/0.56    inference(ennf_transformation,[],[f2])).
% 1.59/0.56  fof(f2,axiom,(
% 1.59/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 1.59/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 1.59/0.56  fof(f213,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (r1_lattices(X1,sK13(X2,X1,X3),X0) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~r2_hidden(X0,X3) | ~sP8(X1,sK13(X2,X1,X3)) | sP1(X2,X1,X3)) )),
% 1.59/0.56    inference(resolution,[],[f187,f95])).
% 1.59/0.56  fof(f95,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (r3_lattice3(X1,sK13(X0,X1,X2),X2) | sP1(X0,X1,X2)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f54])).
% 1.59/0.56  fof(f187,plain,(
% 1.59/0.56    ( ! [X2,X0,X3,X1] : (~r3_lattice3(X2,X3,X1) | ~m1_subset_1(X0,u1_struct_0(X2)) | r1_lattices(X2,X3,X0) | ~r2_hidden(X0,X1) | ~sP8(X2,X3)) )),
% 1.59/0.56    inference(resolution,[],[f110,f108])).
% 1.59/0.56  fof(f108,plain,(
% 1.59/0.56    ( ! [X2,X0,X1] : (sP7(X1,X0,X2) | ~r3_lattice3(X0,X1,X2) | ~sP8(X0,X1)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f64])).
% 1.59/0.56  fof(f110,plain,(
% 1.59/0.56    ( ! [X4,X2,X0,X1] : (~sP7(X0,X1,X2) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1)) | r1_lattices(X1,X0,X4)) )),
% 1.59/0.56    inference(cnf_transformation,[],[f68])).
% 1.59/0.56  % SZS output end Proof for theBenchmark
% 1.59/0.56  % (25847)------------------------------
% 1.59/0.56  % (25847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.56  % (25847)Termination reason: Refutation
% 1.59/0.56  
% 1.59/0.56  % (25847)Memory used [KB]: 6396
% 1.59/0.56  % (25847)Time elapsed: 0.143 s
% 1.59/0.56  % (25847)------------------------------
% 1.59/0.56  % (25847)------------------------------
% 1.59/0.56  % (25842)Success in time 0.204 s
%------------------------------------------------------------------------------
