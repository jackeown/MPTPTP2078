%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1469+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:21 EST 2020

% Result     : Theorem 6.89s
% Output     : Refutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 166 expanded)
%              Number of leaves         :   23 (  69 expanded)
%              Depth                    :    8
%              Number of atoms          :  259 ( 533 expanded)
%              Number of equality atoms :   37 (  58 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f11670,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3894,f3904,f3928,f3934,f4360,f7691,f8233,f8622,f9663,f9759,f10501,f11207,f11669])).

fof(f11669,plain,
    ( ~ spl96_2
    | ~ spl96_4
    | spl96_8
    | ~ spl96_96 ),
    inference(avatar_contradiction_clause,[],[f11668])).

fof(f11668,plain,
    ( $false
    | ~ spl96_2
    | ~ spl96_4
    | spl96_8
    | ~ spl96_96 ),
    inference(subsumption_resolution,[],[f11667,f11197])).

fof(f11197,plain,(
    ! [X0] : l2_lattices(k1_lattice3(X0)) ),
    inference(unit_resulting_resolution,[],[f3358,f3681])).

fof(f3681,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f3009])).

fof(f3009,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f2046])).

fof(f2046,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f3358,plain,(
    ! [X0] : l3_lattices(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f2806])).

fof(f2806,axiom,(
    ! [X0] :
      ( l3_lattices(k1_lattice3(X0))
      & v3_lattices(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_lattice3)).

fof(f11667,plain,
    ( ~ l2_lattices(k1_lattice3(sK1))
    | ~ spl96_2
    | ~ spl96_4
    | spl96_8
    | ~ spl96_96 ),
    inference(unit_resulting_resolution,[],[f3359,f3922,f3893,f3903,f8232,f3353])).

fof(f3353,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | k1_lattices(X0,X1,X2) != X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3126])).

fof(f3126,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k1_lattices(X0,X1,X2) != X2 )
                & ( k1_lattices(X0,X1,X2) = X2
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f2851])).

fof(f2851,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f2850])).

fof(f2850,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2030])).

fof(f2030,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_lattices)).

fof(f8232,plain,
    ( sK3 = k1_lattices(k1_lattice3(sK1),sK2,sK3)
    | ~ spl96_96 ),
    inference(avatar_component_clause,[],[f8230])).

fof(f8230,plain,
    ( spl96_96
  <=> sK3 = k1_lattices(k1_lattice3(sK1),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_96])])).

fof(f3903,plain,
    ( m1_subset_1(sK3,u1_struct_0(k1_lattice3(sK1)))
    | ~ spl96_4 ),
    inference(avatar_component_clause,[],[f3901])).

fof(f3901,plain,
    ( spl96_4
  <=> m1_subset_1(sK3,u1_struct_0(k1_lattice3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_4])])).

fof(f3893,plain,
    ( m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK1)))
    | ~ spl96_2 ),
    inference(avatar_component_clause,[],[f3891])).

fof(f3891,plain,
    ( spl96_2
  <=> m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_2])])).

fof(f3922,plain,
    ( ~ r1_lattices(k1_lattice3(sK1),sK2,sK3)
    | spl96_8 ),
    inference(avatar_component_clause,[],[f3921])).

fof(f3921,plain,
    ( spl96_8
  <=> r1_lattices(k1_lattice3(sK1),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_8])])).

fof(f3359,plain,(
    ! [X0] : ~ v2_struct_0(k1_lattice3(X0)) ),
    inference(cnf_transformation,[],[f2807])).

fof(f2807,axiom,(
    ! [X0] :
      ( v3_lattices(k1_lattice3(X0))
      & ~ v2_struct_0(k1_lattice3(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_lattice3)).

fof(f11207,plain,(
    spl96_119 ),
    inference(avatar_contradiction_clause,[],[f11206])).

fof(f11206,plain,
    ( $false
    | spl96_119 ),
    inference(subsumption_resolution,[],[f11196,f3358])).

fof(f11196,plain,
    ( ~ l3_lattices(k1_lattice3(sK1))
    | spl96_119 ),
    inference(unit_resulting_resolution,[],[f10500,f3681])).

fof(f10500,plain,
    ( ~ l2_lattices(k1_lattice3(sK1))
    | spl96_119 ),
    inference(avatar_component_clause,[],[f10498])).

fof(f10498,plain,
    ( spl96_119
  <=> l2_lattices(k1_lattice3(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_119])])).

fof(f10501,plain,
    ( ~ spl96_119
    | ~ spl96_2
    | ~ spl96_4
    | ~ spl96_8
    | spl96_96 ),
    inference(avatar_split_clause,[],[f8337,f8230,f3921,f3901,f3891,f10498])).

fof(f8337,plain,
    ( ~ l2_lattices(k1_lattice3(sK1))
    | ~ spl96_2
    | ~ spl96_4
    | ~ spl96_8
    | spl96_96 ),
    inference(unit_resulting_resolution,[],[f3359,f3893,f3903,f3923,f8231,f3352])).

fof(f3352,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k1_lattices(X0,X1,X2) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f3126])).

fof(f8231,plain,
    ( sK3 != k1_lattices(k1_lattice3(sK1),sK2,sK3)
    | spl96_96 ),
    inference(avatar_component_clause,[],[f8230])).

fof(f3923,plain,
    ( r1_lattices(k1_lattice3(sK1),sK2,sK3)
    | ~ spl96_8 ),
    inference(avatar_component_clause,[],[f3921])).

fof(f9759,plain,
    ( spl96_79
    | ~ spl96_102 ),
    inference(avatar_contradiction_clause,[],[f9758])).

fof(f9758,plain,
    ( $false
    | spl96_79
    | ~ spl96_102 ),
    inference(subsumption_resolution,[],[f9743,f5741])).

fof(f5741,plain,
    ( ~ r1_tarski(sK2,sK3)
    | spl96_79 ),
    inference(unit_resulting_resolution,[],[f5250,f3573])).

fof(f3573,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f2956])).

fof(f2956,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f5250,plain,
    ( sK2 != k3_xboole_0(sK2,sK3)
    | spl96_79 ),
    inference(avatar_component_clause,[],[f5249])).

fof(f5249,plain,
    ( spl96_79
  <=> sK2 = k3_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_79])])).

fof(f9743,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl96_102 ),
    inference(superposition,[],[f3628,f9604])).

fof(f9604,plain,
    ( sK3 = k2_xboole_0(sK2,sK3)
    | ~ spl96_102 ),
    inference(avatar_component_clause,[],[f9602])).

fof(f9602,plain,
    ( spl96_102
  <=> sK3 = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_102])])).

fof(f3628,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f149])).

fof(f149,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f9663,plain,
    ( spl96_102
    | ~ spl96_58
    | ~ spl96_96 ),
    inference(avatar_split_clause,[],[f9605,f8230,f4357,f9602])).

fof(f4357,plain,
    ( spl96_58
  <=> k2_xboole_0(sK2,sK3) = k1_lattices(k1_lattice3(sK1),sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_58])])).

fof(f9605,plain,
    ( sK3 = k2_xboole_0(sK2,sK3)
    | ~ spl96_58
    | ~ spl96_96 ),
    inference(backward_demodulation,[],[f4359,f8232])).

fof(f4359,plain,
    ( k2_xboole_0(sK2,sK3) = k1_lattices(k1_lattice3(sK1),sK2,sK3)
    | ~ spl96_58 ),
    inference(avatar_component_clause,[],[f4357])).

fof(f8622,plain,
    ( ~ spl96_79
    | spl96_82 ),
    inference(avatar_split_clause,[],[f5732,f5481,f5249])).

fof(f5481,plain,
    ( spl96_82
  <=> sK2 = k3_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_82])])).

fof(f5732,plain,
    ( sK2 != k3_xboole_0(sK2,sK3)
    | spl96_82 ),
    inference(superposition,[],[f5482,f3578])).

fof(f3578,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f5482,plain,
    ( sK2 != k3_xboole_0(sK3,sK2)
    | spl96_82 ),
    inference(avatar_component_clause,[],[f5481])).

fof(f8233,plain,
    ( spl96_96
    | ~ spl96_9
    | ~ spl96_58 ),
    inference(avatar_split_clause,[],[f7792,f4357,f3925,f8230])).

fof(f3925,plain,
    ( spl96_9
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl96_9])])).

fof(f7792,plain,
    ( sK3 = k1_lattices(k1_lattice3(sK1),sK2,sK3)
    | ~ spl96_9
    | ~ spl96_58 ),
    inference(backward_demodulation,[],[f4359,f7788])).

fof(f7788,plain,
    ( sK3 = k2_xboole_0(sK2,sK3)
    | ~ spl96_9 ),
    inference(unit_resulting_resolution,[],[f3927,f3620])).

fof(f3620,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f2980])).

fof(f2980,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f68])).

fof(f68,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f3927,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl96_9 ),
    inference(avatar_component_clause,[],[f3925])).

fof(f7691,plain,
    ( spl96_9
    | ~ spl96_82 ),
    inference(avatar_split_clause,[],[f5532,f5481,f3925])).

fof(f5532,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl96_82 ),
    inference(superposition,[],[f3579,f5483])).

fof(f5483,plain,
    ( sK2 = k3_xboole_0(sK3,sK2)
    | ~ spl96_82 ),
    inference(avatar_component_clause,[],[f5481])).

fof(f3579,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f4360,plain,
    ( spl96_58
    | ~ spl96_2
    | ~ spl96_4 ),
    inference(avatar_split_clause,[],[f4006,f3901,f3891,f4357])).

fof(f4006,plain,
    ( k2_xboole_0(sK2,sK3) = k1_lattices(k1_lattice3(sK1),sK2,sK3)
    | ~ spl96_2
    | ~ spl96_4 ),
    inference(unit_resulting_resolution,[],[f3893,f3903,f3355])).

fof(f3355,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
      | k2_xboole_0(X1,X2) = k1_lattices(k1_lattice3(X0),X1,X2) ) ),
    inference(cnf_transformation,[],[f2852])).

fof(f2852,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( k3_xboole_0(X1,X2) = k2_lattices(k1_lattice3(X0),X1,X2)
            & k2_xboole_0(X1,X2) = k1_lattices(k1_lattice3(X0),X1,X2) )
          | ~ m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      | ~ m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(ennf_transformation,[],[f2808])).

fof(f2808,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
         => ( k3_xboole_0(X1,X2) = k2_lattices(k1_lattice3(X0),X1,X2)
            & k2_xboole_0(X1,X2) = k1_lattices(k1_lattice3(X0),X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_lattice3)).

fof(f3934,plain,
    ( ~ spl96_8
    | ~ spl96_9 ),
    inference(avatar_split_clause,[],[f3308,f3925,f3921])).

fof(f3308,plain,
    ( ~ r1_tarski(sK2,sK3)
    | ~ r1_lattices(k1_lattice3(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f3101])).

fof(f3101,plain,
    ( ( ~ r1_tarski(sK2,sK3)
      | ~ r1_lattices(k1_lattice3(sK1),sK2,sK3) )
    & ( r1_tarski(sK2,sK3)
      | r1_lattices(k1_lattice3(sK1),sK2,sK3) )
    & m1_subset_1(sK3,u1_struct_0(k1_lattice3(sK1)))
    & m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f3098,f3100,f3099])).

fof(f3099,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ( ~ r1_tarski(X1,X2)
              | ~ r1_lattices(k1_lattice3(X0),X1,X2) )
            & ( r1_tarski(X1,X2)
              | r1_lattices(k1_lattice3(X0),X1,X2) )
            & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
        & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) )
   => ( ? [X2] :
          ( ( ~ r1_tarski(sK2,X2)
            | ~ r1_lattices(k1_lattice3(sK1),sK2,X2) )
          & ( r1_tarski(sK2,X2)
            | r1_lattices(k1_lattice3(sK1),sK2,X2) )
          & m1_subset_1(X2,u1_struct_0(k1_lattice3(sK1))) )
      & m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f3100,plain,
    ( ? [X2] :
        ( ( ~ r1_tarski(sK2,X2)
          | ~ r1_lattices(k1_lattice3(sK1),sK2,X2) )
        & ( r1_tarski(sK2,X2)
          | r1_lattices(k1_lattice3(sK1),sK2,X2) )
        & m1_subset_1(X2,u1_struct_0(k1_lattice3(sK1))) )
   => ( ( ~ r1_tarski(sK2,sK3)
        | ~ r1_lattices(k1_lattice3(sK1),sK2,sK3) )
      & ( r1_tarski(sK2,sK3)
        | r1_lattices(k1_lattice3(sK1),sK2,sK3) )
      & m1_subset_1(sK3,u1_struct_0(k1_lattice3(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f3098,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_lattices(k1_lattice3(X0),X1,X2) )
          & ( r1_tarski(X1,X2)
            | r1_lattices(k1_lattice3(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(flattening,[],[f3097])).

fof(f3097,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( ~ r1_tarski(X1,X2)
            | ~ r1_lattices(k1_lattice3(X0),X1,X2) )
          & ( r1_tarski(X1,X2)
            | r1_lattices(k1_lattice3(X0),X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(nnf_transformation,[],[f2815])).

fof(f2815,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ( r1_lattices(k1_lattice3(X0),X1,X2)
          <~> r1_tarski(X1,X2) )
          & m1_subset_1(X2,u1_struct_0(k1_lattice3(X0))) )
      & m1_subset_1(X1,u1_struct_0(k1_lattice3(X0))) ) ),
    inference(ennf_transformation,[],[f2810])).

fof(f2810,negated_conjecture,(
    ~ ! [X0,X1] :
        ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
       => ! [X2] :
            ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
           => ( r1_lattices(k1_lattice3(X0),X1,X2)
            <=> r1_tarski(X1,X2) ) ) ) ),
    inference(negated_conjecture,[],[f2809])).

fof(f2809,conjecture,(
    ! [X0,X1] :
      ( m1_subset_1(X1,u1_struct_0(k1_lattice3(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,u1_struct_0(k1_lattice3(X0)))
         => ( r1_lattices(k1_lattice3(X0),X1,X2)
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_lattice3)).

fof(f3928,plain,
    ( spl96_8
    | spl96_9 ),
    inference(avatar_split_clause,[],[f3307,f3925,f3921])).

fof(f3307,plain,
    ( r1_tarski(sK2,sK3)
    | r1_lattices(k1_lattice3(sK1),sK2,sK3) ),
    inference(cnf_transformation,[],[f3101])).

fof(f3904,plain,(
    spl96_4 ),
    inference(avatar_split_clause,[],[f3306,f3901])).

fof(f3306,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_lattice3(sK1))) ),
    inference(cnf_transformation,[],[f3101])).

fof(f3894,plain,(
    spl96_2 ),
    inference(avatar_split_clause,[],[f3305,f3891])).

fof(f3305,plain,(
    m1_subset_1(sK2,u1_struct_0(k1_lattice3(sK1))) ),
    inference(cnf_transformation,[],[f3101])).
%------------------------------------------------------------------------------
