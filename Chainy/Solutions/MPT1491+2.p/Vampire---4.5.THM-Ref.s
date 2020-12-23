%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1491+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:21 EST 2020

% Result     : Theorem 15.37s
% Output     : Refutation 15.44s
% Verified   : 
% Statistics : Number of formulae       :  261 ( 792 expanded)
%              Number of leaves         :   35 ( 307 expanded)
%              Depth                    :   17
%              Number of atoms          : 1399 (3736 expanded)
%              Number of equality atoms :   61 ( 169 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19307,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3126,f3131,f3136,f3141,f3166,f3285,f3297,f3312,f3438,f3460,f3797,f3974,f5321,f5338,f6093,f6734,f8584,f10357,f12758,f13004,f13543,f15227,f18234,f18242,f18633,f18715,f18853,f19259])).

fof(f19259,plain,
    ( spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_158
    | ~ spl16_210
    | spl16_337
    | ~ spl16_395
    | ~ spl16_402 ),
    inference(avatar_contradiction_clause,[],[f19258])).

fof(f19258,plain,
    ( $false
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_158
    | ~ spl16_210
    | spl16_337
    | ~ spl16_395
    | ~ spl16_402 ),
    inference(subsumption_resolution,[],[f19198,f15886])).

fof(f15886,plain,
    ( ~ r1_lattices(sK1,sK2,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)))
    | spl16_337 ),
    inference(avatar_component_clause,[],[f15885])).

fof(f15885,plain,
    ( spl16_337
  <=> r1_lattices(sK1,sK2,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_337])])).

fof(f19198,plain,
    ( r1_lattices(sK1,sK2,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_158
    | ~ spl16_210
    | ~ spl16_395
    | ~ spl16_402 ),
    inference(backward_demodulation,[],[f19059,f19125])).

fof(f19125,plain,
    ( sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_158
    | ~ spl16_210
    | ~ spl16_402 ),
    inference(forward_demodulation,[],[f19124,f13542])).

fof(f13542,plain,
    ( sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))))
    | ~ spl16_210 ),
    inference(avatar_component_clause,[],[f13540])).

fof(f13540,plain,
    ( spl16_210
  <=> sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_210])])).

fof(f19124,plain,
    ( k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)))) = sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_158
    | ~ spl16_402 ),
    inference(forward_demodulation,[],[f19123,f18694])).

fof(f18694,plain,
    ( k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))) = k7_lattices(sK1,sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_158 ),
    inference(subsumption_resolution,[],[f18693,f3125])).

fof(f3125,plain,
    ( ~ v2_struct_0(sK1)
    | spl16_1 ),
    inference(avatar_component_clause,[],[f3123])).

fof(f3123,plain,
    ( spl16_1
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_1])])).

fof(f18693,plain,
    ( k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))) = k7_lattices(sK1,sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1))
    | v2_struct_0(sK1)
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_158 ),
    inference(subsumption_resolution,[],[f18692,f3130])).

fof(f3130,plain,
    ( v10_lattices(sK1)
    | ~ spl16_2 ),
    inference(avatar_component_clause,[],[f3128])).

fof(f3128,plain,
    ( spl16_2
  <=> v10_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_2])])).

fof(f18692,plain,
    ( k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))) = k7_lattices(sK1,sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1))
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_158 ),
    inference(subsumption_resolution,[],[f18691,f3135])).

fof(f3135,plain,
    ( v17_lattices(sK1)
    | ~ spl16_3 ),
    inference(avatar_component_clause,[],[f3133])).

fof(f3133,plain,
    ( spl16_3
  <=> v17_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_3])])).

fof(f18691,plain,
    ( k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))) = k7_lattices(sK1,sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1))
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_158 ),
    inference(subsumption_resolution,[],[f18684,f3140])).

fof(f3140,plain,
    ( l3_lattices(sK1)
    | ~ spl16_4 ),
    inference(avatar_component_clause,[],[f3138])).

fof(f3138,plain,
    ( spl16_4
  <=> l3_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_4])])).

fof(f18684,plain,
    ( k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))) = k7_lattices(sK1,sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_158 ),
    inference(resolution,[],[f10356,f3026])).

fof(f3026,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | k7_lattices(X2,sK4(X0,X1,X2)) = X0
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f2976])).

fof(f2976,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | k7_lattices(X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & k7_lattices(X2,sK4(X0,X1,X2)) = X0
            & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f2974,f2975])).

fof(f2975,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & k7_lattices(X2,X4) = X0
          & m1_subset_1(X4,u1_struct_0(X2)) )
     => ( r2_hidden(sK4(X0,X1,X2),X1)
        & k7_lattices(X2,sK4(X0,X1,X2)) = X0
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2974,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | k7_lattices(X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & k7_lattices(X2,X4) = X0
              & m1_subset_1(X4,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(rectify,[],[f2973])).

fof(f2973,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | k7_lattices(X2,X3) != X0
              | ~ m1_subset_1(X3,u1_struct_0(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & k7_lattices(X2,X3) = X0
              & m1_subset_1(X3,u1_struct_0(X2)) )
          | ~ r2_hidden(X0,a_2_0_lattice3(X1,X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(nnf_transformation,[],[f2899])).

fof(f2899,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & k7_lattices(X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(flattening,[],[f2898])).

fof(f2898,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & k7_lattices(X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X2)) ) )
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(ennf_transformation,[],[f2849])).

fof(f2849,axiom,(
    ! [X0,X1,X2] :
      ( ( l3_lattices(X2)
        & v17_lattices(X2)
        & v10_lattices(X2)
        & ~ v2_struct_0(X2) )
     => ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & k7_lattices(X2,X3) = X0
            & m1_subset_1(X3,u1_struct_0(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_lattice3)).

fof(f10356,plain,
    ( r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),a_2_0_lattice3(sK0,sK1))
    | ~ spl16_158 ),
    inference(avatar_component_clause,[],[f10354])).

fof(f10354,plain,
    ( spl16_158
  <=> r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),a_2_0_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_158])])).

fof(f19123,plain,
    ( sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1) = k7_lattices(sK1,k7_lattices(sK1,sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1)))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_402 ),
    inference(subsumption_resolution,[],[f19122,f3125])).

fof(f19122,plain,
    ( sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1) = k7_lattices(sK1,k7_lattices(sK1,sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1)))
    | v2_struct_0(sK1)
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_402 ),
    inference(subsumption_resolution,[],[f19121,f3130])).

fof(f19121,plain,
    ( sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1) = k7_lattices(sK1,k7_lattices(sK1,sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1)))
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_402 ),
    inference(subsumption_resolution,[],[f19120,f3135])).

fof(f19120,plain,
    ( sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1) = k7_lattices(sK1,k7_lattices(sK1,sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1)))
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_402 ),
    inference(subsumption_resolution,[],[f18963,f3140])).

fof(f18963,plain,
    ( sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1) = k7_lattices(sK1,k7_lattices(sK1,sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1)))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_402 ),
    inference(resolution,[],[f18852,f3044])).

fof(f3044,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k7_lattices(X0,k7_lattices(X0,X1)) = X1
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2922])).

fof(f2922,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2921])).

fof(f2921,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_lattices(X0,k7_lattices(X0,X1)) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v17_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2080])).

fof(f2080,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v17_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k7_lattices(X0,k7_lattices(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_lattices)).

fof(f18852,plain,
    ( m1_subset_1(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),u1_struct_0(sK1))
    | ~ spl16_402 ),
    inference(avatar_component_clause,[],[f18850])).

fof(f18850,plain,
    ( spl16_402
  <=> m1_subset_1(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_402])])).

fof(f19059,plain,
    ( r1_lattices(sK1,sK2,sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1))
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_395
    | ~ spl16_402 ),
    inference(subsumption_resolution,[],[f18948,f18714])).

fof(f18714,plain,
    ( r2_hidden(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),sK0)
    | ~ spl16_395 ),
    inference(avatar_component_clause,[],[f18712])).

fof(f18712,plain,
    ( spl16_395
  <=> r2_hidden(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_395])])).

fof(f18948,plain,
    ( ~ r2_hidden(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),sK0)
    | r1_lattices(sK1,sK2,sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1))
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_6
    | ~ spl16_402 ),
    inference(resolution,[],[f18852,f18638])).

fof(f18638,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,sK0)
        | r1_lattices(sK1,sK2,X0) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f18637,f3125])).

fof(f18637,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_lattices(sK1,sK2,X0)
        | v2_struct_0(sK1) )
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f18636,f3140])).

fof(f18636,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_lattices(sK1,sK2,X0)
        | ~ l3_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_5
    | ~ spl16_6 ),
    inference(subsumption_resolution,[],[f10059,f3165])).

fof(f3165,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl16_5 ),
    inference(avatar_component_clause,[],[f3163])).

fof(f3163,plain,
    ( spl16_5
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_5])])).

fof(f10059,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_lattices(sK1,sK2,X0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ l3_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_6 ),
    inference(resolution,[],[f3280,f3047])).

fof(f3047,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r3_lattice3(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattices(X0,X1,X4)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2982])).

fof(f2982,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,X1,sK5(X0,X1,X2))
                  & r2_hidden(sK5(X0,X1,X2),X2)
                  & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X1,X4)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r3_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f2980,f2981])).

fof(f2981,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X1,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X1,sK5(X0,X1,X2))
        & r2_hidden(sK5(X0,X1,X2),X2)
        & m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f2980,plain,(
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
    inference(rectify,[],[f2979])).

fof(f2979,plain,(
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
    inference(nnf_transformation,[],[f2926])).

fof(f2926,plain,(
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
    inference(flattening,[],[f2925])).

fof(f2925,plain,(
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
    inference(ennf_transformation,[],[f2815])).

fof(f2815,axiom,(
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

fof(f3280,plain,
    ( r3_lattice3(sK1,sK2,sK0)
    | ~ spl16_6 ),
    inference(avatar_component_clause,[],[f3278])).

fof(f3278,plain,
    ( spl16_6
  <=> r3_lattice3(sK1,sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_6])])).

fof(f18853,plain,
    ( spl16_402
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_158 ),
    inference(avatar_split_clause,[],[f18690,f10354,f3138,f3133,f3128,f3123,f18850])).

fof(f18690,plain,
    ( m1_subset_1(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),u1_struct_0(sK1))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_158 ),
    inference(subsumption_resolution,[],[f18689,f3125])).

fof(f18689,plain,
    ( m1_subset_1(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_158 ),
    inference(subsumption_resolution,[],[f18688,f3130])).

fof(f18688,plain,
    ( m1_subset_1(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),u1_struct_0(sK1))
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_158 ),
    inference(subsumption_resolution,[],[f18687,f3135])).

fof(f18687,plain,
    ( m1_subset_1(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),u1_struct_0(sK1))
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_158 ),
    inference(subsumption_resolution,[],[f18683,f3140])).

fof(f18683,plain,
    ( m1_subset_1(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_158 ),
    inference(resolution,[],[f10356,f3025])).

fof(f3025,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f2976])).

fof(f18715,plain,
    ( spl16_395
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_158 ),
    inference(avatar_split_clause,[],[f18698,f10354,f3138,f3133,f3128,f3123,f18712])).

fof(f18698,plain,
    ( r2_hidden(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),sK0)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_158 ),
    inference(subsumption_resolution,[],[f18697,f3125])).

fof(f18697,plain,
    ( r2_hidden(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),sK0)
    | v2_struct_0(sK1)
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_158 ),
    inference(subsumption_resolution,[],[f18696,f3130])).

fof(f18696,plain,
    ( r2_hidden(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),sK0)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_158 ),
    inference(subsumption_resolution,[],[f18695,f3135])).

fof(f18695,plain,
    ( r2_hidden(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),sK0)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_158 ),
    inference(subsumption_resolution,[],[f18685,f3140])).

fof(f18685,plain,
    ( r2_hidden(sK4(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),sK0,sK1),sK0)
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_158 ),
    inference(resolution,[],[f10356,f3027])).

fof(f3027,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f2976])).

fof(f18633,plain,
    ( spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_13
    | ~ spl16_337 ),
    inference(avatar_contradiction_clause,[],[f18632])).

fof(f18632,plain,
    ( $false
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_13
    | ~ spl16_337 ),
    inference(subsumption_resolution,[],[f3458,f18248])).

fof(f18248,plain,
    ( r3_lattice3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_337 ),
    inference(subsumption_resolution,[],[f18247,f3125])).

fof(f18247,plain,
    ( r3_lattice3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_337 ),
    inference(subsumption_resolution,[],[f18246,f3140])).

fof(f18246,plain,
    ( r3_lattice3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_5
    | ~ spl16_337 ),
    inference(subsumption_resolution,[],[f15892,f3165])).

fof(f15892,plain,
    ( r3_lattice3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_337 ),
    inference(resolution,[],[f15887,f3050])).

fof(f3050,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,sK5(X0,X1,X2))
      | r3_lattice3(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2982])).

fof(f15887,plain,
    ( r1_lattices(sK1,sK2,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)))
    | ~ spl16_337 ),
    inference(avatar_component_clause,[],[f15885])).

fof(f3458,plain,
    ( ~ r3_lattice3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | spl16_13 ),
    inference(avatar_component_clause,[],[f3457])).

fof(f3457,plain,
    ( spl16_13
  <=> r3_lattice3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_13])])).

fof(f18242,plain,
    ( spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_185 ),
    inference(avatar_contradiction_clause,[],[f18241])).

fof(f18241,plain,
    ( $false
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_185 ),
    inference(subsumption_resolution,[],[f18240,f3125])).

fof(f18240,plain,
    ( v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6
    | ~ spl16_185 ),
    inference(subsumption_resolution,[],[f18239,f3140])).

fof(f18239,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_5
    | spl16_6
    | ~ spl16_185 ),
    inference(subsumption_resolution,[],[f18238,f3165])).

fof(f18238,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | spl16_6
    | ~ spl16_185 ),
    inference(subsumption_resolution,[],[f18237,f3279])).

fof(f3279,plain,
    ( ~ r3_lattice3(sK1,sK2,sK0)
    | spl16_6 ),
    inference(avatar_component_clause,[],[f3278])).

fof(f18237,plain,
    ( r3_lattice3(sK1,sK2,sK0)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_185 ),
    inference(resolution,[],[f12999,f3050])).

fof(f12999,plain,
    ( r1_lattices(sK1,sK2,sK5(sK1,sK2,sK0))
    | ~ spl16_185 ),
    inference(avatar_component_clause,[],[f12997])).

fof(f12997,plain,
    ( spl16_185
  <=> r1_lattices(sK1,sK2,sK5(sK1,sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_185])])).

fof(f18234,plain,
    ( spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_111
    | ~ spl16_128
    | spl16_186
    | ~ spl16_314 ),
    inference(avatar_contradiction_clause,[],[f18233])).

fof(f18233,plain,
    ( $false
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_111
    | ~ spl16_128
    | spl16_186
    | ~ spl16_314 ),
    inference(subsumption_resolution,[],[f18232,f13003])).

fof(f13003,plain,
    ( ~ r2_hidden(sK5(sK1,sK2,sK0),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | spl16_186 ),
    inference(avatar_component_clause,[],[f13001])).

fof(f13001,plain,
    ( spl16_186
  <=> r2_hidden(sK5(sK1,sK2,sK0),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_186])])).

fof(f18232,plain,
    ( r2_hidden(sK5(sK1,sK2,sK0),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_111
    | ~ spl16_128
    | ~ spl16_314 ),
    inference(resolution,[],[f6873,f15226])).

fof(f15226,plain,
    ( r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,sK0)),a_2_0_lattice3(sK0,sK1))
    | ~ spl16_314 ),
    inference(avatar_component_clause,[],[f15224])).

fof(f15224,plain,
    ( spl16_314
  <=> r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,sK0)),a_2_0_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_314])])).

fof(f6873,plain,
    ( ! [X27] :
        ( ~ r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,sK0)),X27)
        | r2_hidden(sK5(sK1,sK2,sK0),a_2_0_lattice3(X27,sK1)) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_111
    | ~ spl16_128 ),
    inference(backward_demodulation,[],[f5890,f6733])).

fof(f6733,plain,
    ( sK5(sK1,sK2,sK0) = k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,sK0)))
    | ~ spl16_128 ),
    inference(avatar_component_clause,[],[f6731])).

fof(f6731,plain,
    ( spl16_128
  <=> sK5(sK1,sK2,sK0) = k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_128])])).

fof(f5890,plain,
    ( ! [X27] :
        ( ~ r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,sK0)),X27)
        | r2_hidden(k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,sK0))),a_2_0_lattice3(X27,sK1)) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_111 ),
    inference(subsumption_resolution,[],[f5889,f3125])).

fof(f5889,plain,
    ( ! [X27] :
        ( ~ r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,sK0)),X27)
        | r2_hidden(k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,sK0))),a_2_0_lattice3(X27,sK1))
        | v2_struct_0(sK1) )
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_111 ),
    inference(subsumption_resolution,[],[f5888,f3130])).

fof(f5888,plain,
    ( ! [X27] :
        ( ~ r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,sK0)),X27)
        | r2_hidden(k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,sK0))),a_2_0_lattice3(X27,sK1))
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_111 ),
    inference(subsumption_resolution,[],[f5887,f3135])).

fof(f5887,plain,
    ( ! [X27] :
        ( ~ r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,sK0)),X27)
        | r2_hidden(k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,sK0))),a_2_0_lattice3(X27,sK1))
        | ~ v17_lattices(sK1)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_4
    | ~ spl16_111 ),
    inference(subsumption_resolution,[],[f5758,f3140])).

fof(f5758,plain,
    ( ! [X27] :
        ( ~ r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,sK0)),X27)
        | r2_hidden(k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,sK0))),a_2_0_lattice3(X27,sK1))
        | ~ l3_lattices(sK1)
        | ~ v17_lattices(sK1)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_111 ),
    inference(resolution,[],[f5320,f3117])).

fof(f3117,plain,(
    ! [X2,X3,X1] :
      ( ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ r2_hidden(X3,X1)
      | r2_hidden(k7_lattices(X2,X3),a_2_0_lattice3(X1,X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(equality_resolution,[],[f3028])).

fof(f3028,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_lattice3(X1,X2))
      | ~ r2_hidden(X3,X1)
      | k7_lattices(X2,X3) != X0
      | ~ m1_subset_1(X3,u1_struct_0(X2))
      | ~ l3_lattices(X2)
      | ~ v17_lattices(X2)
      | ~ v10_lattices(X2)
      | v2_struct_0(X2) ) ),
    inference(cnf_transformation,[],[f2976])).

fof(f5320,plain,
    ( m1_subset_1(k7_lattices(sK1,sK5(sK1,sK2,sK0)),u1_struct_0(sK1))
    | ~ spl16_111 ),
    inference(avatar_component_clause,[],[f5318])).

fof(f5318,plain,
    ( spl16_111
  <=> m1_subset_1(k7_lattices(sK1,sK5(sK1,sK2,sK0)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_111])])).

fof(f15227,plain,
    ( spl16_314
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_27
    | ~ spl16_48 ),
    inference(avatar_split_clause,[],[f12887,f3971,f3794,f3138,f3133,f3128,f3123,f15224])).

fof(f3794,plain,
    ( spl16_27
  <=> r2_hidden(sK5(sK1,sK2,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_27])])).

fof(f3971,plain,
    ( spl16_48
  <=> m1_subset_1(sK5(sK1,sK2,sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_48])])).

fof(f12887,plain,
    ( r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,sK0)),a_2_0_lattice3(sK0,sK1))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_27
    | ~ spl16_48 ),
    inference(resolution,[],[f8632,f3796])).

fof(f3796,plain,
    ( r2_hidden(sK5(sK1,sK2,sK0),sK0)
    | ~ spl16_27 ),
    inference(avatar_component_clause,[],[f3794])).

fof(f8632,plain,
    ( ! [X27] :
        ( ~ r2_hidden(sK5(sK1,sK2,sK0),X27)
        | r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,sK0)),a_2_0_lattice3(X27,sK1)) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f8631,f3125])).

fof(f8631,plain,
    ( ! [X27] :
        ( ~ r2_hidden(sK5(sK1,sK2,sK0),X27)
        | r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,sK0)),a_2_0_lattice3(X27,sK1))
        | v2_struct_0(sK1) )
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f8630,f3130])).

fof(f8630,plain,
    ( ! [X27] :
        ( ~ r2_hidden(sK5(sK1,sK2,sK0),X27)
        | r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,sK0)),a_2_0_lattice3(X27,sK1))
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f8629,f3135])).

fof(f8629,plain,
    ( ! [X27] :
        ( ~ r2_hidden(sK5(sK1,sK2,sK0),X27)
        | r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,sK0)),a_2_0_lattice3(X27,sK1))
        | ~ v17_lattices(sK1)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_4
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f7764,f3140])).

fof(f7764,plain,
    ( ! [X27] :
        ( ~ r2_hidden(sK5(sK1,sK2,sK0),X27)
        | r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,sK0)),a_2_0_lattice3(X27,sK1))
        | ~ l3_lattices(sK1)
        | ~ v17_lattices(sK1)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_48 ),
    inference(resolution,[],[f3973,f3117])).

fof(f3973,plain,
    ( m1_subset_1(sK5(sK1,sK2,sK0),u1_struct_0(sK1))
    | ~ spl16_48 ),
    inference(avatar_component_clause,[],[f3971])).

fof(f13543,plain,
    ( spl16_210
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_112 ),
    inference(avatar_split_clause,[],[f8243,f5335,f3138,f3133,f3128,f3123,f13540])).

fof(f5335,plain,
    ( spl16_112
  <=> m1_subset_1(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_112])])).

fof(f8243,plain,
    ( sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_112 ),
    inference(subsumption_resolution,[],[f8242,f3125])).

fof(f8242,plain,
    ( sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))))
    | v2_struct_0(sK1)
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_112 ),
    inference(subsumption_resolution,[],[f8241,f3130])).

fof(f8241,plain,
    ( sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))))
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_112 ),
    inference(subsumption_resolution,[],[f8240,f3135])).

fof(f8240,plain,
    ( sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))))
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_112 ),
    inference(subsumption_resolution,[],[f6806,f3140])).

fof(f6806,plain,
    ( sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_112 ),
    inference(resolution,[],[f5337,f3044])).

fof(f5337,plain,
    ( m1_subset_1(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),u1_struct_0(sK1))
    | ~ spl16_112 ),
    inference(avatar_component_clause,[],[f5335])).

fof(f13004,plain,
    ( spl16_185
    | ~ spl16_186
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_13
    | ~ spl16_48 ),
    inference(avatar_split_clause,[],[f5306,f3971,f3457,f3163,f3138,f3123,f13001,f12997])).

fof(f5306,plain,
    ( ~ r2_hidden(sK5(sK1,sK2,sK0),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | r1_lattices(sK1,sK2,sK5(sK1,sK2,sK0))
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_13
    | ~ spl16_48 ),
    inference(resolution,[],[f5122,f3973])).

fof(f5122,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK1))
        | ~ r2_hidden(X0,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
        | r1_lattices(sK1,sK2,X0) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_13 ),
    inference(subsumption_resolution,[],[f5121,f3125])).

fof(f5121,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_lattices(sK1,sK2,X0)
        | v2_struct_0(sK1) )
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_13 ),
    inference(subsumption_resolution,[],[f5120,f3140])).

fof(f5120,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_lattices(sK1,sK2,X0)
        | ~ l3_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_5
    | ~ spl16_13 ),
    inference(subsumption_resolution,[],[f4731,f3165])).

fof(f4731,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK1))
        | r1_lattices(sK1,sK2,X0)
        | ~ m1_subset_1(sK2,u1_struct_0(sK1))
        | ~ l3_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_13 ),
    inference(resolution,[],[f3459,f3047])).

fof(f3459,plain,
    ( r3_lattice3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | ~ spl16_13 ),
    inference(avatar_component_clause,[],[f3457])).

fof(f12758,plain,
    ( spl16_7
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_10
    | ~ spl16_11
    | ~ spl16_13 ),
    inference(avatar_split_clause,[],[f3946,f3457,f3435,f3309,f3138,f3133,f3128,f3123,f3282])).

fof(f3282,plain,
    ( spl16_7
  <=> r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_7])])).

fof(f3309,plain,
    ( spl16_10
  <=> m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_10])])).

fof(f3435,plain,
    ( spl16_11
  <=> sK2 = k7_lattices(sK1,k7_lattices(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_11])])).

fof(f3946,plain,
    ( r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_10
    | ~ spl16_11
    | ~ spl16_13 ),
    inference(resolution,[],[f3450,f3459])).

fof(f3450,plain,
    ( ! [X1] :
        ( ~ r3_lattice3(sK1,sK2,a_2_0_lattice3(X1,sK1))
        | r4_lattice3(sK1,k7_lattices(sK1,sK2),X1) )
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_10
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f3449,f3125])).

fof(f3449,plain,
    ( ! [X1] :
        ( ~ r3_lattice3(sK1,sK2,a_2_0_lattice3(X1,sK1))
        | r4_lattice3(sK1,k7_lattices(sK1,sK2),X1)
        | v2_struct_0(sK1) )
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_10
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f3448,f3130])).

fof(f3448,plain,
    ( ! [X1] :
        ( ~ r3_lattice3(sK1,sK2,a_2_0_lattice3(X1,sK1))
        | r4_lattice3(sK1,k7_lattices(sK1,sK2),X1)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_10
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f3447,f3135])).

fof(f3447,plain,
    ( ! [X1] :
        ( ~ r3_lattice3(sK1,sK2,a_2_0_lattice3(X1,sK1))
        | r4_lattice3(sK1,k7_lattices(sK1,sK2),X1)
        | ~ v17_lattices(sK1)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_4
    | ~ spl16_10
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f3446,f3140])).

fof(f3446,plain,
    ( ! [X1] :
        ( ~ r3_lattice3(sK1,sK2,a_2_0_lattice3(X1,sK1))
        | r4_lattice3(sK1,k7_lattices(sK1,sK2),X1)
        | ~ l3_lattices(sK1)
        | ~ v17_lattices(sK1)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_10
    | ~ spl16_11 ),
    inference(subsumption_resolution,[],[f3440,f3311])).

fof(f3311,plain,
    ( m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1))
    | ~ spl16_10 ),
    inference(avatar_component_clause,[],[f3309])).

fof(f3440,plain,
    ( ! [X1] :
        ( ~ r3_lattice3(sK1,sK2,a_2_0_lattice3(X1,sK1))
        | r4_lattice3(sK1,k7_lattices(sK1,sK2),X1)
        | ~ m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1))
        | ~ l3_lattices(sK1)
        | ~ v17_lattices(sK1)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_11 ),
    inference(superposition,[],[f3018,f3437])).

fof(f3437,plain,
    ( sK2 = k7_lattices(sK1,k7_lattices(sK1,sK2))
    | ~ spl16_11 ),
    inference(avatar_component_clause,[],[f3435])).

fof(f3018,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
      | r4_lattice3(X1,X2,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f2967])).

fof(f2967,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( ( r4_lattice3(X1,X2,X0)
              | ~ r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
            & ( r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
              | ~ r4_lattice3(X1,X2,X0) ) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f2893])).

fof(f2893,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f2892])).

fof(f2892,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r4_lattice3(X1,X2,X0)
          <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          | ~ m1_subset_1(X2,u1_struct_0(X1)) )
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2875])).

fof(f2875,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v17_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r4_lattice3(X1,X2,X0)
          <=> r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_lattice3)).

fof(f10357,plain,
    ( spl16_158
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_115
    | ~ spl16_150 ),
    inference(avatar_split_clause,[],[f10252,f8581,f6090,f3138,f3133,f3128,f3123,f10354])).

fof(f6090,plain,
    ( spl16_115
  <=> r2_hidden(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_115])])).

fof(f8581,plain,
    ( spl16_150
  <=> m1_subset_1(sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl16_150])])).

fof(f10252,plain,
    ( r2_hidden(k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))),a_2_0_lattice3(sK0,sK1))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_115
    | ~ spl16_150 ),
    inference(backward_demodulation,[],[f10051,f10250])).

fof(f10250,plain,
    ( k7_lattices(sK1,sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))) = sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_115
    | ~ spl16_150 ),
    inference(forward_demodulation,[],[f10249,f10055])).

fof(f10055,plain,
    ( sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_115 ),
    inference(subsumption_resolution,[],[f10054,f3125])).

fof(f10054,plain,
    ( sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1))
    | v2_struct_0(sK1)
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_115 ),
    inference(subsumption_resolution,[],[f10053,f3130])).

fof(f10053,plain,
    ( sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1))
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_115 ),
    inference(subsumption_resolution,[],[f10052,f3135])).

fof(f10052,plain,
    ( sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1))
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_115 ),
    inference(subsumption_resolution,[],[f8347,f3140])).

fof(f8347,plain,
    ( sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)) = k7_lattices(sK1,sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_115 ),
    inference(resolution,[],[f6092,f3026])).

fof(f6092,plain,
    ( r2_hidden(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | ~ spl16_115 ),
    inference(avatar_component_clause,[],[f6090])).

fof(f10249,plain,
    ( sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1) = k7_lattices(sK1,k7_lattices(sK1,sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1)))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_150 ),
    inference(subsumption_resolution,[],[f10248,f3125])).

fof(f10248,plain,
    ( sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1) = k7_lattices(sK1,k7_lattices(sK1,sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1)))
    | v2_struct_0(sK1)
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_150 ),
    inference(subsumption_resolution,[],[f10247,f3130])).

fof(f10247,plain,
    ( sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1) = k7_lattices(sK1,k7_lattices(sK1,sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1)))
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_150 ),
    inference(subsumption_resolution,[],[f10246,f3135])).

fof(f10246,plain,
    ( sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1) = k7_lattices(sK1,k7_lattices(sK1,sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1)))
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_150 ),
    inference(subsumption_resolution,[],[f10138,f3140])).

fof(f10138,plain,
    ( sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1) = k7_lattices(sK1,k7_lattices(sK1,sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1)))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_150 ),
    inference(resolution,[],[f8583,f3044])).

fof(f8583,plain,
    ( m1_subset_1(sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),u1_struct_0(sK1))
    | ~ spl16_150 ),
    inference(avatar_component_clause,[],[f8581])).

fof(f10051,plain,
    ( r2_hidden(sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),a_2_0_lattice3(sK0,sK1))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_115 ),
    inference(subsumption_resolution,[],[f10050,f3125])).

fof(f10050,plain,
    ( r2_hidden(sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),a_2_0_lattice3(sK0,sK1))
    | v2_struct_0(sK1)
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_115 ),
    inference(subsumption_resolution,[],[f10049,f3130])).

fof(f10049,plain,
    ( r2_hidden(sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),a_2_0_lattice3(sK0,sK1))
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_115 ),
    inference(subsumption_resolution,[],[f10048,f3135])).

fof(f10048,plain,
    ( r2_hidden(sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),a_2_0_lattice3(sK0,sK1))
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_115 ),
    inference(subsumption_resolution,[],[f8348,f3140])).

fof(f8348,plain,
    ( r2_hidden(sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),a_2_0_lattice3(sK0,sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_115 ),
    inference(resolution,[],[f6092,f3027])).

fof(f8584,plain,
    ( spl16_150
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_115 ),
    inference(avatar_split_clause,[],[f6839,f6090,f3138,f3133,f3128,f3123,f8581])).

fof(f6839,plain,
    ( m1_subset_1(sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),u1_struct_0(sK1))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_115 ),
    inference(subsumption_resolution,[],[f6838,f3125])).

fof(f6838,plain,
    ( m1_subset_1(sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_115 ),
    inference(subsumption_resolution,[],[f6837,f3130])).

fof(f6837,plain,
    ( m1_subset_1(sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),u1_struct_0(sK1))
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_115 ),
    inference(subsumption_resolution,[],[f6836,f3135])).

fof(f6836,plain,
    ( m1_subset_1(sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),u1_struct_0(sK1))
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_115 ),
    inference(subsumption_resolution,[],[f6832,f3140])).

fof(f6832,plain,
    ( m1_subset_1(sK4(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(sK0,sK1),sK1),u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_115 ),
    inference(resolution,[],[f6092,f3025])).

fof(f6734,plain,
    ( spl16_128
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_48 ),
    inference(avatar_split_clause,[],[f6143,f3971,f3138,f3133,f3128,f3123,f6731])).

fof(f6143,plain,
    ( sK5(sK1,sK2,sK0) = k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,sK0)))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f6142,f3125])).

fof(f6142,plain,
    ( sK5(sK1,sK2,sK0) = k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,sK0)))
    | v2_struct_0(sK1)
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f6141,f3130])).

fof(f6141,plain,
    ( sK5(sK1,sK2,sK0) = k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,sK0)))
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f6140,f3135])).

fof(f6140,plain,
    ( sK5(sK1,sK2,sK0) = k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,sK0)))
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f5659,f3140])).

fof(f5659,plain,
    ( sK5(sK1,sK2,sK0) = k7_lattices(sK1,k7_lattices(sK1,sK5(sK1,sK2,sK0)))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_48 ),
    inference(resolution,[],[f3973,f3044])).

fof(f6093,plain,
    ( spl16_115
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_13 ),
    inference(avatar_split_clause,[],[f5329,f3457,f3163,f3138,f3123,f6090])).

fof(f5329,plain,
    ( r2_hidden(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_13 ),
    inference(resolution,[],[f3458,f3248])).

fof(f3248,plain,
    ( ! [X12] :
        ( r3_lattice3(sK1,sK2,X12)
        | r2_hidden(sK5(sK1,sK2,X12),X12) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f3247,f3125])).

fof(f3247,plain,
    ( ! [X12] :
        ( r2_hidden(sK5(sK1,sK2,X12),X12)
        | r3_lattice3(sK1,sK2,X12)
        | v2_struct_0(sK1) )
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f3183,f3140])).

fof(f3183,plain,
    ( ! [X12] :
        ( r2_hidden(sK5(sK1,sK2,X12),X12)
        | r3_lattice3(sK1,sK2,X12)
        | ~ l3_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_5 ),
    inference(resolution,[],[f3165,f3049])).

fof(f3049,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK5(X0,X1,X2),X2)
      | r3_lattice3(X0,X1,X2)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2982])).

fof(f5338,plain,
    ( spl16_112
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_13 ),
    inference(avatar_split_clause,[],[f5328,f3457,f3163,f3138,f3123,f5335])).

fof(f5328,plain,
    ( m1_subset_1(sK5(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1)),u1_struct_0(sK1))
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_13 ),
    inference(resolution,[],[f3458,f3246])).

fof(f3246,plain,
    ( ! [X11] :
        ( r3_lattice3(sK1,sK2,X11)
        | m1_subset_1(sK5(sK1,sK2,X11),u1_struct_0(sK1)) )
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f3245,f3125])).

fof(f3245,plain,
    ( ! [X11] :
        ( m1_subset_1(sK5(sK1,sK2,X11),u1_struct_0(sK1))
        | r3_lattice3(sK1,sK2,X11)
        | v2_struct_0(sK1) )
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f3182,f3140])).

fof(f3182,plain,
    ( ! [X11] :
        ( m1_subset_1(sK5(sK1,sK2,X11),u1_struct_0(sK1))
        | r3_lattice3(sK1,sK2,X11)
        | ~ l3_lattices(sK1)
        | v2_struct_0(sK1) )
    | ~ spl16_5 ),
    inference(resolution,[],[f3165,f3048])).

fof(f3048,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(sK5(X0,X1,X2),u1_struct_0(X0))
      | r3_lattice3(X0,X1,X2)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2982])).

fof(f5321,plain,
    ( spl16_111
    | spl16_1
    | ~ spl16_4
    | ~ spl16_48 ),
    inference(avatar_split_clause,[],[f4815,f3971,f3138,f3123,f5318])).

fof(f4815,plain,
    ( m1_subset_1(k7_lattices(sK1,sK5(sK1,sK2,sK0)),u1_struct_0(sK1))
    | spl16_1
    | ~ spl16_4
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f4814,f3125])).

fof(f4814,plain,
    ( m1_subset_1(k7_lattices(sK1,sK5(sK1,sK2,sK0)),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_48 ),
    inference(subsumption_resolution,[],[f4772,f3140])).

fof(f4772,plain,
    ( m1_subset_1(k7_lattices(sK1,sK5(sK1,sK2,sK0)),u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_48 ),
    inference(resolution,[],[f3973,f3029])).

fof(f3029,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f2901])).

fof(f2901,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2900])).

fof(f2900,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2043])).

fof(f2043,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k7_lattices(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_lattices)).

fof(f3974,plain,
    ( spl16_48
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6 ),
    inference(avatar_split_clause,[],[f3560,f3278,f3163,f3138,f3123,f3971])).

fof(f3560,plain,
    ( m1_subset_1(sK5(sK1,sK2,sK0),u1_struct_0(sK1))
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6 ),
    inference(resolution,[],[f3246,f3279])).

fof(f3797,plain,
    ( spl16_27
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6 ),
    inference(avatar_split_clause,[],[f3507,f3278,f3163,f3138,f3123,f3794])).

fof(f3507,plain,
    ( r2_hidden(sK5(sK1,sK2,sK0),sK0)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | spl16_6 ),
    inference(resolution,[],[f3248,f3279])).

fof(f3460,plain,
    ( spl16_13
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(avatar_split_clause,[],[f3296,f3282,f3163,f3138,f3133,f3128,f3123,f3457])).

fof(f3296,plain,
    ( r3_lattice3(sK1,sK2,a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(forward_demodulation,[],[f3295,f3244])).

fof(f3244,plain,
    ( sK2 = k7_lattices(sK1,k7_lattices(sK1,sK2))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f3243,f3125])).

fof(f3243,plain,
    ( sK2 = k7_lattices(sK1,k7_lattices(sK1,sK2))
    | v2_struct_0(sK1)
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f3242,f3130])).

fof(f3242,plain,
    ( sK2 = k7_lattices(sK1,k7_lattices(sK1,sK2))
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f3241,f3135])).

fof(f3241,plain,
    ( sK2 = k7_lattices(sK1,k7_lattices(sK1,sK2))
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f3181,f3140])).

fof(f3181,plain,
    ( sK2 = k7_lattices(sK1,k7_lattices(sK1,sK2))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_5 ),
    inference(resolution,[],[f3165,f3044])).

fof(f3295,plain,
    ( r3_lattice3(sK1,k7_lattices(sK1,k7_lattices(sK1,sK2)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(subsumption_resolution,[],[f3294,f3125])).

fof(f3294,plain,
    ( r3_lattice3(sK1,k7_lattices(sK1,k7_lattices(sK1,sK2)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | v2_struct_0(sK1)
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(subsumption_resolution,[],[f3293,f3130])).

fof(f3293,plain,
    ( r3_lattice3(sK1,k7_lattices(sK1,k7_lattices(sK1,sK2)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | spl16_1
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(subsumption_resolution,[],[f3292,f3135])).

fof(f3292,plain,
    ( r3_lattice3(sK1,k7_lattices(sK1,k7_lattices(sK1,sK2)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(subsumption_resolution,[],[f3291,f3140])).

fof(f3291,plain,
    ( r3_lattice3(sK1,k7_lattices(sK1,k7_lattices(sK1,sK2)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5
    | ~ spl16_7 ),
    inference(subsumption_resolution,[],[f3287,f3196])).

fof(f3196,plain,
    ( m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1))
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f3195,f3125])).

fof(f3195,plain,
    ( m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(subsumption_resolution,[],[f3169,f3140])).

fof(f3169,plain,
    ( m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_5 ),
    inference(resolution,[],[f3165,f3029])).

fof(f3287,plain,
    ( r3_lattice3(sK1,k7_lattices(sK1,k7_lattices(sK1,sK2)),a_2_0_lattice3(a_2_0_lattice3(sK0,sK1),sK1))
    | ~ m1_subset_1(k7_lattices(sK1,sK2),u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | ~ v17_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl16_7 ),
    inference(resolution,[],[f3284,f3017])).

fof(f3017,plain,(
    ! [X2,X0,X1] :
      ( ~ r4_lattice3(X1,X2,X0)
      | r3_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v17_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f2967])).

fof(f3284,plain,
    ( r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
    | ~ spl16_7 ),
    inference(avatar_component_clause,[],[f3282])).

fof(f3438,plain,
    ( spl16_11
    | spl16_1
    | ~ spl16_2
    | ~ spl16_3
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(avatar_split_clause,[],[f3244,f3163,f3138,f3133,f3128,f3123,f3435])).

fof(f3312,plain,
    ( spl16_10
    | spl16_1
    | ~ spl16_4
    | ~ spl16_5 ),
    inference(avatar_split_clause,[],[f3196,f3163,f3138,f3123,f3309])).

fof(f3297,plain,
    ( ~ spl16_6
    | ~ spl16_7 ),
    inference(avatar_split_clause,[],[f3016,f3282,f3278])).

fof(f3016,plain,
    ( ~ r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
    | ~ r3_lattice3(sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f2966])).

fof(f2966,plain,
    ( ( ~ r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
      | ~ r3_lattice3(sK1,sK2,sK0) )
    & ( r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
      | r3_lattice3(sK1,sK2,sK0) )
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l3_lattices(sK1)
    & v17_lattices(sK1)
    & v10_lattices(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2963,f2965,f2964])).

fof(f2964,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
              | ~ r3_lattice3(X1,X2,X0) )
            & ( r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
              | r3_lattice3(X1,X2,X0) )
            & m1_subset_1(X2,u1_struct_0(X1)) )
        & l3_lattices(X1)
        & v17_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( ~ r4_lattice3(sK1,k7_lattices(sK1,X2),a_2_0_lattice3(sK0,sK1))
            | ~ r3_lattice3(sK1,X2,sK0) )
          & ( r4_lattice3(sK1,k7_lattices(sK1,X2),a_2_0_lattice3(sK0,sK1))
            | r3_lattice3(sK1,X2,sK0) )
          & m1_subset_1(X2,u1_struct_0(sK1)) )
      & l3_lattices(sK1)
      & v17_lattices(sK1)
      & v10_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f2965,plain,
    ( ? [X2] :
        ( ( ~ r4_lattice3(sK1,k7_lattices(sK1,X2),a_2_0_lattice3(sK0,sK1))
          | ~ r3_lattice3(sK1,X2,sK0) )
        & ( r4_lattice3(sK1,k7_lattices(sK1,X2),a_2_0_lattice3(sK0,sK1))
          | r3_lattice3(sK1,X2,sK0) )
        & m1_subset_1(X2,u1_struct_0(sK1)) )
   => ( ( ~ r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
        | ~ r3_lattice3(sK1,sK2,sK0) )
      & ( r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
        | r3_lattice3(sK1,sK2,sK0) )
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f2963,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | ~ r3_lattice3(X1,X2,X0) )
          & ( r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | r3_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f2962])).

fof(f2962,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | ~ r3_lattice3(X1,X2,X0) )
          & ( r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1))
            | r3_lattice3(X1,X2,X0) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f2891])).

fof(f2891,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r3_lattice3(X1,X2,X0)
          <~> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(flattening,[],[f2890])).

fof(f2890,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r3_lattice3(X1,X2,X0)
          <~> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) )
          & m1_subset_1(X2,u1_struct_0(X1)) )
      & l3_lattices(X1)
      & v17_lattices(X1)
      & v10_lattices(X1)
      & ~ v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f2877])).

fof(f2877,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( l3_lattices(X1)
          & v17_lattices(X1)
          & v10_lattices(X1)
          & ~ v2_struct_0(X1) )
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(X1))
           => ( r3_lattice3(X1,X2,X0)
            <=> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) ) ) ) ),
    inference(negated_conjecture,[],[f2876])).

fof(f2876,conjecture,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & v17_lattices(X1)
        & v10_lattices(X1)
        & ~ v2_struct_0(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(X1))
         => ( r3_lattice3(X1,X2,X0)
          <=> r4_lattice3(X1,k7_lattices(X1,X2),a_2_0_lattice3(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_lattice3)).

fof(f3285,plain,
    ( spl16_6
    | spl16_7 ),
    inference(avatar_split_clause,[],[f3015,f3282,f3278])).

fof(f3015,plain,
    ( r4_lattice3(sK1,k7_lattices(sK1,sK2),a_2_0_lattice3(sK0,sK1))
    | r3_lattice3(sK1,sK2,sK0) ),
    inference(cnf_transformation,[],[f2966])).

fof(f3166,plain,(
    spl16_5 ),
    inference(avatar_split_clause,[],[f3014,f3163])).

fof(f3014,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f2966])).

fof(f3141,plain,(
    spl16_4 ),
    inference(avatar_split_clause,[],[f3013,f3138])).

fof(f3013,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f2966])).

fof(f3136,plain,(
    spl16_3 ),
    inference(avatar_split_clause,[],[f3012,f3133])).

fof(f3012,plain,(
    v17_lattices(sK1) ),
    inference(cnf_transformation,[],[f2966])).

fof(f3131,plain,(
    spl16_2 ),
    inference(avatar_split_clause,[],[f3011,f3128])).

fof(f3011,plain,(
    v10_lattices(sK1) ),
    inference(cnf_transformation,[],[f2966])).

fof(f3126,plain,(
    ~ spl16_1 ),
    inference(avatar_split_clause,[],[f3010,f3123])).

fof(f3010,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f2966])).
%------------------------------------------------------------------------------
