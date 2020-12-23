%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:48 EST 2020

% Result     : Theorem 5.46s
% Output     : Refutation 6.04s
% Verified   : 
% Statistics : Number of formulae       :  250 (1082 expanded)
%              Number of leaves         :   41 ( 291 expanded)
%              Depth                    :   27
%              Number of atoms          : 1237 (7617 expanded)
%              Number of equality atoms :  193 ( 983 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8799,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f223,f225,f227,f276,f294,f314,f316,f321,f344,f367,f570,f2237,f2390,f3082,f4741,f4893,f8796])).

fof(f8796,plain,
    ( ~ spl14_7
    | ~ spl14_11
    | ~ spl14_17
    | ~ spl14_53 ),
    inference(avatar_contradiction_clause,[],[f8795])).

fof(f8795,plain,
    ( $false
    | ~ spl14_7
    | ~ spl14_11
    | ~ spl14_17
    | ~ spl14_53 ),
    inference(trivial_inequality_removal,[],[f8794])).

fof(f8794,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ spl14_7
    | ~ spl14_11
    | ~ spl14_17
    | ~ spl14_53 ),
    inference(superposition,[],[f2236,f4734])).

fof(f4734,plain,
    ( ! [X3] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X3)))
    | ~ spl14_7
    | ~ spl14_11
    | ~ spl14_17 ),
    inference(superposition,[],[f4523,f429])).

fof(f429,plain,
    ( ! [X6] : sK2(sK0,k15_lattice3(sK0,X6)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X6))))
    | ~ spl14_7 ),
    inference(subsumption_resolution,[],[f428,f119])).

fof(f119,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f72])).

fof(f72,plain,
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
   => ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
        | ~ l3_lattices(sK0)
        | ~ v13_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
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
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).

fof(f428,plain,
    ( ! [X6] :
        ( sK2(sK0,k15_lattice3(sK0,X6)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X6))))
        | v2_struct_0(sK0) )
    | ~ spl14_7 ),
    inference(subsumption_resolution,[],[f427,f120])).

fof(f120,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f427,plain,
    ( ! [X6] :
        ( sK2(sK0,k15_lattice3(sK0,X6)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X6))))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl14_7 ),
    inference(subsumption_resolution,[],[f426,f121])).

fof(f121,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f426,plain,
    ( ! [X6] :
        ( sK2(sK0,k15_lattice3(sK0,X6)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X6))))
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl14_7 ),
    inference(subsumption_resolution,[],[f414,f122])).

fof(f122,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f73])).

fof(f414,plain,
    ( ! [X6] :
        ( sK2(sK0,k15_lattice3(sK0,X6)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X6))))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl14_7 ),
    inference(resolution,[],[f266,f151])).

fof(f151,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).

fof(f266,plain,
    ( ! [X6] : m1_subset_1(sK2(sK0,k15_lattice3(sK0,X6)),u1_struct_0(sK0))
    | ~ spl14_7 ),
    inference(avatar_component_clause,[],[f265])).

fof(f265,plain,
    ( spl14_7
  <=> ! [X6] : m1_subset_1(sK2(sK0,k15_lattice3(sK0,X6)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).

fof(f4523,plain,
    ( ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | ~ spl14_11
    | ~ spl14_17 ),
    inference(superposition,[],[f596,f951])).

fof(f951,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | ~ spl14_17 ),
    inference(subsumption_resolution,[],[f950,f119])).

fof(f950,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl14_17 ),
    inference(subsumption_resolution,[],[f949,f561])).

fof(f561,plain,
    ( l2_lattices(sK0)
    | ~ spl14_17 ),
    inference(avatar_component_clause,[],[f560])).

fof(f560,plain,
    ( spl14_17
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).

fof(f949,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,X0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f948,f229])).

fof(f229,plain,(
    ! [X0] : m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f228,f122])).

fof(f228,plain,(
    ! [X0] :
      ( ~ l3_lattices(sK0)
      | m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f119,f169])).

fof(f169,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f948,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,X0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
      | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f942,f229])).

fof(f942,plain,(
    ! [X0] :
      ( k15_lattice3(sK0,X0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
      | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
      | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f847,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | k1_lattices(X0,X1,X2) = X2
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k1_lattices(X0,X1,X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).

fof(f847,plain,(
    ! [X0] : r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) ),
    inference(subsumption_resolution,[],[f840,f229])).

fof(f840,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) ) ),
    inference(resolution,[],[f836,f257])).

fof(f257,plain,(
    ! [X2,X1] :
      ( ~ r4_lattice3(sK0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X2),X1) ) ),
    inference(subsumption_resolution,[],[f256,f119])).

fof(f256,plain,(
    ! [X2,X1] :
      ( ~ r4_lattice3(sK0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X2),X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f255,f120])).

fof(f255,plain,(
    ! [X2,X1] :
      ( ~ r4_lattice3(sK0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X2),X1)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f254,f121])).

fof(f254,plain,(
    ! [X2,X1] :
      ( ~ r4_lattice3(sK0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X2),X1)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f239,f122])).

fof(f239,plain,(
    ! [X2,X1] :
      ( ~ r4_lattice3(sK0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,k15_lattice3(sK0,X2),X1)
      | ~ l3_lattices(sK0)
      | ~ v4_lattice3(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f229,f201])).

fof(f201,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ r4_lattice3(X0,X4,X1)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | r1_lattices(X0,k15_lattice3(X0,X1),X4)
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f192])).

fof(f192,plain,(
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
    inference(equality_resolution,[],[f156])).

fof(f156,plain,(
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
    inference(cnf_transformation,[],[f93])).

fof(f93,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k15_lattice3(X0,X1) = X2
              | ( ~ r1_lattices(X0,X2,sK6(X0,X1,X2))
                & r4_lattice3(X0,sK6(X0,X1,X2),X1)
                & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) )
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f91,f92])).

fof(f92,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X2,X3)
          & r4_lattice3(X0,X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,X2,sK6(X0,X1,X2))
        & r4_lattice3(X0,sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
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
    inference(rectify,[],[f90])).

fof(f90,plain,(
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
    inference(flattening,[],[f89])).

fof(f89,plain,(
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
    inference(nnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(flattening,[],[f55])).

fof(f55,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f836,plain,(
    ! [X0] : r4_lattice3(sK0,k15_lattice3(sK0,X0),k1_xboole_0) ),
    inference(resolution,[],[f571,f124])).

fof(f124,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f571,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK9(sK0,k15_lattice3(sK0,X0),X1))
      | r4_lattice3(sK0,k15_lattice3(sK0,X0),X1) ) ),
    inference(resolution,[],[f298,f178])).

fof(f178,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f298,plain,(
    ! [X15,X16] :
      ( r2_hidden(sK9(sK0,k15_lattice3(sK0,X15),X16),X16)
      | r4_lattice3(sK0,k15_lattice3(sK0,X15),X16) ) ),
    inference(subsumption_resolution,[],[f297,f119])).

fof(f297,plain,(
    ! [X15,X16] :
      ( r2_hidden(sK9(sK0,k15_lattice3(sK0,X15),X16),X16)
      | r4_lattice3(sK0,k15_lattice3(sK0,X15),X16)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f249,f122])).

fof(f249,plain,(
    ! [X15,X16] :
      ( r2_hidden(sK9(sK0,k15_lattice3(sK0,X15),X16),X16)
      | r4_lattice3(sK0,k15_lattice3(sK0,X15),X16)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f229,f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r2_hidden(sK9(X0,X1,X2),X2)
      | r4_lattice3(X0,X1,X2)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f102,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r4_lattice3(X0,X1,X2)
                | ( ~ r1_lattices(X0,sK9(X0,X1,X2),X1)
                  & r2_hidden(sK9(X0,X1,X2),X2)
                  & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) )
              & ( ! [X4] :
                    ( r1_lattices(X0,X4,X1)
                    | ~ r2_hidden(X4,X2)
                    | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                | ~ r4_lattice3(X0,X1,X2) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f100,f101])).

fof(f101,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r1_lattices(X0,X3,X1)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ~ r1_lattices(X0,sK9(X0,X1,X2),X1)
        & r2_hidden(sK9(X0,X1,X2),X2)
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f100,plain,(
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
    inference(rectify,[],[f99])).

fof(f99,plain,(
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
    inference(nnf_transformation,[],[f60])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f596,plain,
    ( ! [X4,X3] : k15_lattice3(sK0,X3) = k2_lattices(sK0,k15_lattice3(sK0,X3),k1_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X4)))
    | ~ spl14_11 ),
    inference(resolution,[],[f293,f229])).

fof(f293,plain,
    ( ! [X12,X11] :
        ( ~ m1_subset_1(X11,u1_struct_0(sK0))
        | k2_lattices(sK0,X11,k1_lattices(sK0,X11,k15_lattice3(sK0,X12))) = X11 )
    | ~ spl14_11 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl14_11
  <=> ! [X11,X12] :
        ( k2_lattices(sK0,X11,k1_lattices(sK0,X11,k15_lattice3(sK0,X12))) = X11
        | ~ m1_subset_1(X11,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).

fof(f2236,plain,
    ( ! [X0] : k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
    | ~ spl14_53 ),
    inference(avatar_component_clause,[],[f2235])).

fof(f2235,plain,
    ( spl14_53
  <=> ! [X0] : k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_53])])).

fof(f4893,plain,(
    ~ spl14_1 ),
    inference(avatar_contradiction_clause,[],[f4892])).

fof(f4892,plain,
    ( $false
    | ~ spl14_1 ),
    inference(subsumption_resolution,[],[f206,f119])).

fof(f206,plain,
    ( v2_struct_0(sK0)
    | ~ spl14_1 ),
    inference(avatar_component_clause,[],[f204])).

fof(f204,plain,
    ( spl14_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).

fof(f4741,plain,
    ( spl14_5
    | ~ spl14_6
    | ~ spl14_11
    | ~ spl14_12
    | ~ spl14_17
    | ~ spl14_69 ),
    inference(avatar_contradiction_clause,[],[f4740])).

fof(f4740,plain,
    ( $false
    | spl14_5
    | ~ spl14_6
    | ~ spl14_11
    | ~ spl14_12
    | ~ spl14_17
    | ~ spl14_69 ),
    inference(subsumption_resolution,[],[f4739,f222])).

fof(f222,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl14_5 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl14_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).

fof(f4739,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ spl14_6
    | ~ spl14_11
    | ~ spl14_12
    | ~ spl14_17
    | ~ spl14_69 ),
    inference(forward_demodulation,[],[f4731,f3513])).

fof(f3513,plain,
    ( ! [X5] : k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X5),k5_lattices(sK0))
    | ~ spl14_12
    | ~ spl14_69 ),
    inference(forward_demodulation,[],[f320,f2385])).

fof(f2385,plain,
    ( k5_lattices(sK0) = sK3(sK0)
    | ~ spl14_69 ),
    inference(avatar_component_clause,[],[f2383])).

fof(f2383,plain,
    ( spl14_69
  <=> k5_lattices(sK0) = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_69])])).

fof(f320,plain,
    ( ! [X5] : sK3(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X5),sK3(sK0))
    | ~ spl14_12 ),
    inference(avatar_component_clause,[],[f319])).

fof(f319,plain,
    ( spl14_12
  <=> ! [X5] : sK3(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X5),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).

fof(f4731,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl14_6
    | ~ spl14_11
    | ~ spl14_17 ),
    inference(superposition,[],[f4523,f396])).

fof(f396,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f395,f119])).

fof(f395,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | v2_struct_0(sK0)
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f394,f120])).

fof(f394,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f393,f121])).

fof(f393,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f382,f122])).

fof(f382,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0)))
    | ~ l3_lattices(sK0)
    | ~ v4_lattice3(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_6 ),
    inference(resolution,[],[f339,f151])).

fof(f339,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f334,f119])).

fof(f334,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl14_6 ),
    inference(resolution,[],[f262,f135])).

fof(f135,plain,(
    ! [X0] :
      ( ~ l1_lattices(X0)
      | m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f262,plain,
    ( l1_lattices(sK0)
    | ~ spl14_6 ),
    inference(avatar_component_clause,[],[f261])).

fof(f261,plain,
    ( spl14_6
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).

fof(f3082,plain,
    ( ~ spl14_3
    | ~ spl14_6
    | spl14_69
    | ~ spl14_70 ),
    inference(avatar_contradiction_clause,[],[f3081])).

fof(f3081,plain,
    ( $false
    | ~ spl14_3
    | ~ spl14_6
    | spl14_69
    | ~ spl14_70 ),
    inference(subsumption_resolution,[],[f3080,f119])).

fof(f3080,plain,
    ( v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_6
    | spl14_69
    | ~ spl14_70 ),
    inference(subsumption_resolution,[],[f3079,f262])).

fof(f3079,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_6
    | spl14_69
    | ~ spl14_70 ),
    inference(subsumption_resolution,[],[f3078,f213])).

fof(f213,plain,
    ( v13_lattices(sK0)
    | ~ spl14_3 ),
    inference(avatar_component_clause,[],[f212])).

fof(f212,plain,
    ( spl14_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).

fof(f3078,plain,
    ( ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_6
    | spl14_69
    | ~ spl14_70 ),
    inference(subsumption_resolution,[],[f3077,f2359])).

fof(f2359,plain,
    ( m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl14_3
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f2358,f119])).

fof(f2358,plain,
    ( m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f2357,f262])).

fof(f2357,plain,
    ( m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_3 ),
    inference(resolution,[],[f213,f140])).

fof(f140,plain,(
    ! [X0] :
      ( ~ v13_lattices(X0)
      | m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
                  & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f80,f82,f81])).

fof(f81,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k2_lattices(X0,X4,X3) = X3
                & k2_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( sK3(X0) = k2_lattices(X0,X4,sK3(X0))
              & sK3(X0) = k2_lattices(X0,sK3(X0),X4) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( ( k2_lattices(X0,X4,X3) = X3
                    & k2_lattices(X0,X3,X4) = X3 )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f79])).

fof(f79,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).

fof(f3077,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_6
    | spl14_69
    | ~ spl14_70 ),
    inference(subsumption_resolution,[],[f3076,f2614])).

fof(f2614,plain,
    ( sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0)))
    | ~ spl14_3
    | ~ spl14_6
    | ~ spl14_70 ),
    inference(subsumption_resolution,[],[f2613,f119])).

fof(f2613,plain,
    ( sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0)))
    | v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_6
    | ~ spl14_70 ),
    inference(subsumption_resolution,[],[f2612,f262])).

fof(f2612,plain,
    ( sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0)))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_70 ),
    inference(subsumption_resolution,[],[f2591,f213])).

fof(f2591,plain,
    ( sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0)))
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_70 ),
    inference(resolution,[],[f2389,f141])).

fof(f141,plain,(
    ! [X4,X0] :
      ( ~ m1_subset_1(X4,u1_struct_0(X0))
      | sK3(X0) = k2_lattices(X0,sK3(X0),X4)
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f2389,plain,
    ( m1_subset_1(sK1(sK0,sK3(sK0)),u1_struct_0(sK0))
    | ~ spl14_70 ),
    inference(avatar_component_clause,[],[f2387])).

fof(f2387,plain,
    ( spl14_70
  <=> m1_subset_1(sK1(sK0,sK3(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_70])])).

fof(f3076,plain,
    ( sK3(sK0) != k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0)))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_6
    | spl14_69
    | ~ spl14_70 ),
    inference(subsumption_resolution,[],[f3075,f2384])).

fof(f2384,plain,
    ( k5_lattices(sK0) != sK3(sK0)
    | spl14_69 ),
    inference(avatar_component_clause,[],[f2383])).

fof(f3075,plain,
    ( k5_lattices(sK0) = sK3(sK0)
    | sK3(sK0) != k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0)))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_6
    | ~ spl14_70 ),
    inference(trivial_inequality_removal,[],[f3074])).

fof(f3074,plain,
    ( sK3(sK0) != sK3(sK0)
    | k5_lattices(sK0) = sK3(sK0)
    | sK3(sK0) != k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0)))
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_6
    | ~ spl14_70 ),
    inference(superposition,[],[f139,f2617])).

fof(f2617,plain,
    ( sK3(sK0) = k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0))
    | ~ spl14_3
    | ~ spl14_6
    | ~ spl14_70 ),
    inference(subsumption_resolution,[],[f2616,f119])).

fof(f2616,plain,
    ( sK3(sK0) = k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0))
    | v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_6
    | ~ spl14_70 ),
    inference(subsumption_resolution,[],[f2615,f262])).

fof(f2615,plain,
    ( sK3(sK0) = k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_70 ),
    inference(subsumption_resolution,[],[f2592,f213])).

fof(f2592,plain,
    ( sK3(sK0) = k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0))
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_70 ),
    inference(resolution,[],[f2389,f142])).

fof(f142,plain,(
    ! [X4,X0] :
      ( ~ m1_subset_1(X4,u1_struct_0(X0))
      | sK3(X0) = k2_lattices(X0,X4,sK3(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f139,plain,(
    ! [X0,X1] :
      ( k2_lattices(X0,sK1(X0,X1),X1) != X1
      | k5_lattices(X0) = X1
      | k2_lattices(X0,X1,sK1(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f78,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f76,f77])).

fof(f77,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f76,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f75])).

fof(f75,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

fof(f2390,plain,
    ( spl14_69
    | spl14_70
    | ~ spl14_3
    | ~ spl14_6 ),
    inference(avatar_split_clause,[],[f2381,f261,f212,f2387,f2383])).

fof(f2381,plain,
    ( m1_subset_1(sK1(sK0,sK3(sK0)),u1_struct_0(sK0))
    | k5_lattices(sK0) = sK3(sK0)
    | ~ spl14_3
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f2380,f119])).

fof(f2380,plain,
    ( m1_subset_1(sK1(sK0,sK3(sK0)),u1_struct_0(sK0))
    | k5_lattices(sK0) = sK3(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f2379,f262])).

fof(f2379,plain,
    ( m1_subset_1(sK1(sK0,sK3(sK0)),u1_struct_0(sK0))
    | k5_lattices(sK0) = sK3(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_6 ),
    inference(subsumption_resolution,[],[f2367,f213])).

fof(f2367,plain,
    ( m1_subset_1(sK1(sK0,sK3(sK0)),u1_struct_0(sK0))
    | k5_lattices(sK0) = sK3(sK0)
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl14_3
    | ~ spl14_6 ),
    inference(resolution,[],[f2359,f138])).

fof(f138,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | k5_lattices(X0) = X1
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f2237,plain,
    ( spl14_3
    | spl14_53
    | ~ spl14_6
    | ~ spl14_7
    | ~ spl14_9 ),
    inference(avatar_split_clause,[],[f2233,f274,f265,f261,f2235,f212])).

fof(f274,plain,
    ( spl14_9
  <=> ! [X7,X8] :
        ( k2_lattices(sK0,k15_lattice3(sK0,X7),X8) = k2_lattices(sK0,X8,k15_lattice3(sK0,X7))
        | ~ m1_subset_1(X8,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).

fof(f2233,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | v13_lattices(sK0) )
    | ~ spl14_6
    | ~ spl14_7
    | ~ spl14_9 ),
    inference(subsumption_resolution,[],[f2232,f119])).

fof(f2232,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | v13_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl14_6
    | ~ spl14_7
    | ~ spl14_9 ),
    inference(subsumption_resolution,[],[f2231,f262])).

fof(f2231,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl14_7
    | ~ spl14_9 ),
    inference(subsumption_resolution,[],[f1567,f229])).

fof(f1567,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | v13_lattices(sK0)
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl14_7
    | ~ spl14_9 ),
    inference(duplicate_literal_removal,[],[f1566])).

fof(f1566,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | v13_lattices(sK0)
        | k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))
        | ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl14_7
    | ~ spl14_9 ),
    inference(superposition,[],[f144,f777])).

fof(f777,plain,
    ( ! [X6,X5] : k2_lattices(sK0,k15_lattice3(sK0,X5),sK2(sK0,k15_lattice3(sK0,X6))) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X6)),k15_lattice3(sK0,X5))
    | ~ spl14_7
    | ~ spl14_9 ),
    inference(resolution,[],[f275,f266])).

fof(f275,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK0))
        | k2_lattices(sK0,k15_lattice3(sK0,X7),X8) = k2_lattices(sK0,X8,k15_lattice3(sK0,X7)) )
    | ~ spl14_9 ),
    inference(avatar_component_clause,[],[f274])).

fof(f144,plain,(
    ! [X0,X1] :
      ( k2_lattices(X0,sK2(X0,X1),X1) != X1
      | v13_lattices(X0)
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f570,plain,(
    spl14_17 ),
    inference(avatar_contradiction_clause,[],[f569])).

fof(f569,plain,
    ( $false
    | spl14_17 ),
    inference(subsumption_resolution,[],[f568,f122])).

fof(f568,plain,
    ( ~ l3_lattices(sK0)
    | spl14_17 ),
    inference(resolution,[],[f562,f126])).

fof(f126,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f562,plain,
    ( ~ l2_lattices(sK0)
    | spl14_17 ),
    inference(avatar_component_clause,[],[f560])).

fof(f367,plain,(
    spl14_10 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl14_10 ),
    inference(subsumption_resolution,[],[f365,f122])).

fof(f365,plain,
    ( ~ l3_lattices(sK0)
    | spl14_10 ),
    inference(subsumption_resolution,[],[f364,f119])).

fof(f364,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl14_10 ),
    inference(subsumption_resolution,[],[f359,f120])).

fof(f359,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl14_10 ),
    inference(resolution,[],[f290,f130])).

fof(f130,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
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

fof(f290,plain,
    ( ~ v9_lattices(sK0)
    | spl14_10 ),
    inference(avatar_component_clause,[],[f288])).

fof(f288,plain,
    ( spl14_10
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).

fof(f344,plain,(
    spl14_8 ),
    inference(avatar_contradiction_clause,[],[f343])).

fof(f343,plain,
    ( $false
    | spl14_8 ),
    inference(subsumption_resolution,[],[f342,f122])).

fof(f342,plain,
    ( ~ l3_lattices(sK0)
    | spl14_8 ),
    inference(subsumption_resolution,[],[f341,f119])).

fof(f341,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl14_8 ),
    inference(subsumption_resolution,[],[f340,f120])).

fof(f340,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl14_8 ),
    inference(resolution,[],[f272,f129])).

fof(f129,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f272,plain,
    ( ~ v6_lattices(sK0)
    | spl14_8 ),
    inference(avatar_component_clause,[],[f270])).

fof(f270,plain,
    ( spl14_8
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).

fof(f321,plain,
    ( ~ spl14_6
    | ~ spl14_3
    | spl14_12 ),
    inference(avatar_split_clause,[],[f317,f319,f212,f261])).

fof(f317,plain,(
    ! [X5] :
      ( sK3(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X5),sK3(sK0))
      | ~ v13_lattices(sK0)
      | ~ l1_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f242,f119])).

fof(f242,plain,(
    ! [X5] :
      ( sK3(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X5),sK3(sK0))
      | ~ v13_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f229,f142])).

fof(f316,plain,
    ( ~ spl14_6
    | spl14_3
    | spl14_7 ),
    inference(avatar_split_clause,[],[f315,f265,f212,f261])).

fof(f315,plain,(
    ! [X6] :
      ( m1_subset_1(sK2(sK0,k15_lattice3(sK0,X6)),u1_struct_0(sK0))
      | v13_lattices(sK0)
      | ~ l1_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f243,f119])).

fof(f243,plain,(
    ! [X6] :
      ( m1_subset_1(sK2(sK0,k15_lattice3(sK0,X6)),u1_struct_0(sK0))
      | v13_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f229,f143])).

fof(f143,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f314,plain,(
    spl14_6 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | spl14_6 ),
    inference(subsumption_resolution,[],[f312,f122])).

fof(f312,plain,
    ( ~ l3_lattices(sK0)
    | spl14_6 ),
    inference(resolution,[],[f263,f125])).

fof(f125,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f263,plain,
    ( ~ l1_lattices(sK0)
    | spl14_6 ),
    inference(avatar_component_clause,[],[f261])).

fof(f294,plain,
    ( ~ spl14_10
    | spl14_11 ),
    inference(avatar_split_clause,[],[f286,f292,f288])).

fof(f286,plain,(
    ! [X12,X11] :
      ( k2_lattices(sK0,X11,k1_lattices(sK0,X11,k15_lattice3(sK0,X12))) = X11
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ v9_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f285,f119])).

fof(f285,plain,(
    ! [X12,X11] :
      ( k2_lattices(sK0,X11,k1_lattices(sK0,X11,k15_lattice3(sK0,X12))) = X11
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f247,f122])).

fof(f247,plain,(
    ! [X12,X11] :
      ( k2_lattices(sK0,X11,k1_lattices(sK0,X11,k15_lattice3(sK0,X12))) = X11
      | ~ m1_subset_1(X11,u1_struct_0(sK0))
      | ~ v9_lattices(sK0)
      | ~ l3_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f229,f160])).

fof(f160,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v9_lattices(X0)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f98])).

fof(f98,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),sK8(X0)))
            & m1_subset_1(sK8(X0),u1_struct_0(X0))
            & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f95,f97,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK7(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f97,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),sK8(X0)))
        & m1_subset_1(sK8(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f95,plain,(
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
    inference(rectify,[],[f94])).

fof(f94,plain,(
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
    inference(nnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f276,plain,
    ( ~ spl14_6
    | ~ spl14_8
    | spl14_9 ),
    inference(avatar_split_clause,[],[f268,f274,f270,f261])).

fof(f268,plain,(
    ! [X8,X7] :
      ( k2_lattices(sK0,k15_lattice3(sK0,X7),X8) = k2_lattices(sK0,X8,k15_lattice3(sK0,X7))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0) ) ),
    inference(subsumption_resolution,[],[f244,f119])).

fof(f244,plain,(
    ! [X8,X7] :
      ( k2_lattices(sK0,k15_lattice3(sK0,X7),X8) = k2_lattices(sK0,X8,k15_lattice3(sK0,X7))
      | ~ m1_subset_1(X8,u1_struct_0(sK0))
      | ~ v6_lattices(sK0)
      | ~ l1_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f229,f145])).

fof(f145,plain,(
    ! [X4,X0,X3] :
      ( ~ m1_subset_1(X4,u1_struct_0(X0))
      | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f88])).

fof(f88,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f85,f87,f86])).

fof(f86,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f87,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).

fof(f227,plain,(
    spl14_2 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl14_2 ),
    inference(subsumption_resolution,[],[f210,f120])).

fof(f210,plain,
    ( ~ v10_lattices(sK0)
    | spl14_2 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl14_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).

fof(f225,plain,(
    spl14_4 ),
    inference(avatar_contradiction_clause,[],[f224])).

fof(f224,plain,
    ( $false
    | spl14_4 ),
    inference(subsumption_resolution,[],[f218,f122])).

fof(f218,plain,
    ( ~ l3_lattices(sK0)
    | spl14_4 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl14_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).

fof(f223,plain,
    ( spl14_1
    | ~ spl14_2
    | ~ spl14_3
    | ~ spl14_4
    | ~ spl14_5 ),
    inference(avatar_split_clause,[],[f123,f220,f216,f212,f208,f204])).

fof(f123,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:35:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (23060)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.52  % (23043)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.52  % (23035)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (23038)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (23032)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (23042)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (23034)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (23049)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (23055)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (23031)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.54  % (23041)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (23033)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (23059)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (23041)Refutation not found, incomplete strategy% (23041)------------------------------
% 0.21/0.55  % (23041)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (23041)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (23041)Memory used [KB]: 10746
% 0.21/0.55  % (23041)Time elapsed: 0.133 s
% 0.21/0.55  % (23041)------------------------------
% 0.21/0.55  % (23041)------------------------------
% 0.21/0.55  % (23047)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.55  % (23047)Refutation not found, incomplete strategy% (23047)------------------------------
% 1.45/0.55  % (23047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (23051)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.55  % (23046)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.55  % (23058)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.45/0.55  % (23045)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.55  % (23040)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.55  % (23040)Refutation not found, incomplete strategy% (23040)------------------------------
% 1.45/0.55  % (23040)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (23040)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (23040)Memory used [KB]: 10746
% 1.45/0.55  % (23040)Time elapsed: 0.148 s
% 1.45/0.55  % (23040)------------------------------
% 1.45/0.55  % (23040)------------------------------
% 1.45/0.56  % (23039)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.56  % (23057)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.56  % (23039)Refutation not found, incomplete strategy% (23039)------------------------------
% 1.45/0.56  % (23039)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (23039)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (23039)Memory used [KB]: 10618
% 1.45/0.56  % (23039)Time elapsed: 0.002 s
% 1.45/0.56  % (23039)------------------------------
% 1.45/0.56  % (23039)------------------------------
% 1.45/0.56  % (23054)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.56  % (23048)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.56  % (23050)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.56  % (23037)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.45/0.56  % (23053)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.45/0.56  % (23044)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.59/0.57  % (23030)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.59/0.57  % (23030)Refutation not found, incomplete strategy% (23030)------------------------------
% 1.59/0.57  % (23030)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (23030)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (23030)Memory used [KB]: 1663
% 1.59/0.57  % (23030)Time elapsed: 0.003 s
% 1.59/0.57  % (23030)------------------------------
% 1.59/0.57  % (23030)------------------------------
% 1.59/0.57  % (23036)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.59/0.57  % (23052)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.59/0.57  % (23047)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (23047)Memory used [KB]: 10618
% 1.59/0.57  % (23047)Time elapsed: 0.138 s
% 1.59/0.57  % (23047)------------------------------
% 1.59/0.57  % (23047)------------------------------
% 1.59/0.57  % (23052)Refutation not found, incomplete strategy% (23052)------------------------------
% 1.59/0.57  % (23052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.59/0.57  % (23052)Termination reason: Refutation not found, incomplete strategy
% 1.59/0.57  
% 1.59/0.57  % (23052)Memory used [KB]: 10874
% 1.59/0.57  % (23052)Time elapsed: 0.090 s
% 1.59/0.57  % (23052)------------------------------
% 1.59/0.57  % (23052)------------------------------
% 2.30/0.69  % (23081)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.30/0.70  % (23082)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.30/0.70  % (23084)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.30/0.71  % (23085)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.30/0.71  % (23083)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.30/0.71  % (23081)Refutation not found, incomplete strategy% (23081)------------------------------
% 2.30/0.71  % (23081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.30/0.71  % (23081)Termination reason: Refutation not found, incomplete strategy
% 2.30/0.71  
% 2.30/0.71  % (23086)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.30/0.71  % (23081)Memory used [KB]: 6268
% 2.30/0.71  % (23081)Time elapsed: 0.128 s
% 2.30/0.71  % (23081)------------------------------
% 2.30/0.71  % (23081)------------------------------
% 3.28/0.84  % (23035)Time limit reached!
% 3.28/0.84  % (23035)------------------------------
% 3.28/0.84  % (23035)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.28/0.84  % (23035)Termination reason: Time limit
% 3.28/0.84  
% 3.28/0.84  % (23035)Memory used [KB]: 9083
% 3.28/0.84  % (23035)Time elapsed: 0.417 s
% 3.28/0.84  % (23035)------------------------------
% 3.28/0.84  % (23035)------------------------------
% 3.28/0.86  % (23082)Refutation not found, incomplete strategy% (23082)------------------------------
% 3.28/0.86  % (23082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.28/0.86  % (23082)Termination reason: Refutation not found, incomplete strategy
% 3.28/0.86  
% 3.28/0.86  % (23082)Memory used [KB]: 6268
% 3.28/0.86  % (23082)Time elapsed: 0.250 s
% 3.28/0.86  % (23082)------------------------------
% 3.28/0.86  % (23082)------------------------------
% 3.59/0.90  % (23087)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 4.09/0.94  % (23042)Time limit reached!
% 4.09/0.94  % (23042)------------------------------
% 4.09/0.94  % (23042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.94  % (23042)Termination reason: Time limit
% 4.09/0.94  
% 4.09/0.94  % (23042)Memory used [KB]: 8699
% 4.09/0.94  % (23042)Time elapsed: 0.529 s
% 4.09/0.94  % (23042)------------------------------
% 4.09/0.94  % (23042)------------------------------
% 4.09/0.95  % (23031)Time limit reached!
% 4.09/0.95  % (23031)------------------------------
% 4.09/0.95  % (23031)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/0.95  % (23031)Termination reason: Time limit
% 4.09/0.95  
% 4.09/0.95  % (23031)Memory used [KB]: 8955
% 4.09/0.95  % (23031)Time elapsed: 0.534 s
% 4.09/0.95  % (23031)------------------------------
% 4.09/0.95  % (23031)------------------------------
% 4.09/0.97  % (23088)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 4.28/1.00  % (23089)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 4.28/1.01  % (23084)Time limit reached!
% 4.28/1.01  % (23084)------------------------------
% 4.28/1.01  % (23084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/1.01  % (23084)Termination reason: Time limit
% 4.28/1.01  
% 4.28/1.01  % (23084)Memory used [KB]: 7419
% 4.28/1.01  % (23084)Time elapsed: 0.410 s
% 4.28/1.01  % (23084)------------------------------
% 4.28/1.01  % (23084)------------------------------
% 4.28/1.01  % (23085)Time limit reached!
% 4.28/1.01  % (23085)------------------------------
% 4.28/1.01  % (23085)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/1.01  % (23085)Termination reason: Time limit
% 4.28/1.01  % (23085)Termination phase: Saturation
% 4.28/1.01  
% 4.28/1.01  % (23085)Memory used [KB]: 12920
% 4.28/1.01  % (23085)Time elapsed: 0.400 s
% 4.28/1.01  % (23085)------------------------------
% 4.28/1.01  % (23085)------------------------------
% 4.28/1.02  % (23059)Time limit reached!
% 4.28/1.02  % (23059)------------------------------
% 4.28/1.02  % (23059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/1.02  % (23059)Termination reason: Time limit
% 4.28/1.02  
% 4.28/1.02  % (23059)Memory used [KB]: 7419
% 4.28/1.02  % (23059)Time elapsed: 0.611 s
% 4.28/1.02  % (23059)------------------------------
% 4.28/1.02  % (23059)------------------------------
% 4.87/1.03  % (23037)Time limit reached!
% 4.87/1.03  % (23037)------------------------------
% 4.87/1.03  % (23037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.87/1.03  % (23037)Termination reason: Time limit
% 4.87/1.03  % (23037)Termination phase: Saturation
% 4.87/1.03  
% 4.87/1.03  % (23037)Memory used [KB]: 10490
% 4.87/1.03  % (23037)Time elapsed: 0.600 s
% 4.87/1.03  % (23037)------------------------------
% 4.87/1.03  % (23037)------------------------------
% 4.87/1.03  % (23046)Time limit reached!
% 4.87/1.03  % (23046)------------------------------
% 4.87/1.03  % (23046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.87/1.03  % (23046)Termination reason: Time limit
% 4.87/1.03  
% 4.87/1.03  % (23046)Memory used [KB]: 16630
% 4.87/1.03  % (23046)Time elapsed: 0.627 s
% 4.87/1.03  % (23046)------------------------------
% 4.87/1.03  % (23046)------------------------------
% 5.46/1.08  % (23091)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 5.46/1.08  % (23090)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.46/1.11  % (23038)Refutation found. Thanks to Tanya!
% 5.46/1.11  % SZS status Theorem for theBenchmark
% 5.46/1.11  % SZS output start Proof for theBenchmark
% 5.46/1.12  fof(f8799,plain,(
% 5.46/1.12    $false),
% 5.46/1.12    inference(avatar_sat_refutation,[],[f223,f225,f227,f276,f294,f314,f316,f321,f344,f367,f570,f2237,f2390,f3082,f4741,f4893,f8796])).
% 5.46/1.12  fof(f8796,plain,(
% 5.46/1.12    ~spl14_7 | ~spl14_11 | ~spl14_17 | ~spl14_53),
% 5.46/1.12    inference(avatar_contradiction_clause,[],[f8795])).
% 5.46/1.12  fof(f8795,plain,(
% 5.46/1.12    $false | (~spl14_7 | ~spl14_11 | ~spl14_17 | ~spl14_53)),
% 5.46/1.12    inference(trivial_inequality_removal,[],[f8794])).
% 5.46/1.12  fof(f8794,plain,(
% 5.46/1.12    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | (~spl14_7 | ~spl14_11 | ~spl14_17 | ~spl14_53)),
% 5.46/1.12    inference(superposition,[],[f2236,f4734])).
% 5.46/1.12  fof(f4734,plain,(
% 5.46/1.12    ( ! [X3] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X3)))) ) | (~spl14_7 | ~spl14_11 | ~spl14_17)),
% 5.46/1.12    inference(superposition,[],[f4523,f429])).
% 5.46/1.12  fof(f429,plain,(
% 5.46/1.12    ( ! [X6] : (sK2(sK0,k15_lattice3(sK0,X6)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X6))))) ) | ~spl14_7),
% 5.46/1.12    inference(subsumption_resolution,[],[f428,f119])).
% 5.46/1.12  fof(f119,plain,(
% 5.46/1.12    ~v2_struct_0(sK0)),
% 5.46/1.12    inference(cnf_transformation,[],[f73])).
% 5.46/1.12  fof(f73,plain,(
% 5.46/1.12    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 5.46/1.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f72])).
% 5.46/1.12  fof(f72,plain,(
% 5.46/1.12    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 5.46/1.12    introduced(choice_axiom,[])).
% 5.46/1.12  fof(f32,plain,(
% 5.46/1.12    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 5.46/1.12    inference(flattening,[],[f31])).
% 5.46/1.12  fof(f31,plain,(
% 5.46/1.12    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 5.46/1.12    inference(ennf_transformation,[],[f27])).
% 5.46/1.12  fof(f27,negated_conjecture,(
% 5.46/1.12    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 5.46/1.12    inference(negated_conjecture,[],[f26])).
% 5.46/1.12  fof(f26,conjecture,(
% 5.46/1.12    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 5.46/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 5.46/1.12  fof(f428,plain,(
% 5.46/1.12    ( ! [X6] : (sK2(sK0,k15_lattice3(sK0,X6)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X6)))) | v2_struct_0(sK0)) ) | ~spl14_7),
% 5.46/1.12    inference(subsumption_resolution,[],[f427,f120])).
% 5.46/1.12  fof(f120,plain,(
% 5.46/1.12    v10_lattices(sK0)),
% 5.46/1.12    inference(cnf_transformation,[],[f73])).
% 5.46/1.12  fof(f427,plain,(
% 5.46/1.12    ( ! [X6] : (sK2(sK0,k15_lattice3(sK0,X6)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X6)))) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl14_7),
% 5.46/1.12    inference(subsumption_resolution,[],[f426,f121])).
% 5.46/1.12  fof(f121,plain,(
% 5.46/1.12    v4_lattice3(sK0)),
% 5.46/1.12    inference(cnf_transformation,[],[f73])).
% 5.46/1.12  fof(f426,plain,(
% 5.46/1.12    ( ! [X6] : (sK2(sK0,k15_lattice3(sK0,X6)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X6)))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl14_7),
% 5.46/1.12    inference(subsumption_resolution,[],[f414,f122])).
% 5.46/1.12  fof(f122,plain,(
% 5.46/1.12    l3_lattices(sK0)),
% 5.46/1.12    inference(cnf_transformation,[],[f73])).
% 5.46/1.12  fof(f414,plain,(
% 5.46/1.12    ( ! [X6] : (sK2(sK0,k15_lattice3(sK0,X6)) = k15_lattice3(sK0,a_2_3_lattice3(sK0,sK2(sK0,k15_lattice3(sK0,X6)))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl14_7),
% 5.46/1.12    inference(resolution,[],[f266,f151])).
% 5.46/1.12  fof(f151,plain,(
% 5.46/1.12    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f52])).
% 5.46/1.12  fof(f52,plain,(
% 5.46/1.12    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(flattening,[],[f51])).
% 5.46/1.12  fof(f51,plain,(
% 5.46/1.12    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 5.46/1.12    inference(ennf_transformation,[],[f23])).
% 5.46/1.12  fof(f23,axiom,(
% 5.46/1.12    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 5.46/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).
% 5.46/1.12  fof(f266,plain,(
% 5.46/1.12    ( ! [X6] : (m1_subset_1(sK2(sK0,k15_lattice3(sK0,X6)),u1_struct_0(sK0))) ) | ~spl14_7),
% 5.46/1.12    inference(avatar_component_clause,[],[f265])).
% 5.46/1.12  fof(f265,plain,(
% 5.46/1.12    spl14_7 <=> ! [X6] : m1_subset_1(sK2(sK0,k15_lattice3(sK0,X6)),u1_struct_0(sK0))),
% 5.46/1.12    introduced(avatar_definition,[new_symbols(naming,[spl14_7])])).
% 5.46/1.12  fof(f4523,plain,(
% 5.46/1.12    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | (~spl14_11 | ~spl14_17)),
% 5.46/1.12    inference(superposition,[],[f596,f951])).
% 5.46/1.12  fof(f951,plain,(
% 5.46/1.12    ( ! [X0] : (k15_lattice3(sK0,X0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | ~spl14_17),
% 5.46/1.12    inference(subsumption_resolution,[],[f950,f119])).
% 5.46/1.12  fof(f950,plain,(
% 5.46/1.12    ( ! [X0] : (k15_lattice3(sK0,X0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | v2_struct_0(sK0)) ) | ~spl14_17),
% 5.46/1.12    inference(subsumption_resolution,[],[f949,f561])).
% 5.46/1.12  fof(f561,plain,(
% 5.46/1.12    l2_lattices(sK0) | ~spl14_17),
% 5.46/1.12    inference(avatar_component_clause,[],[f560])).
% 5.46/1.12  fof(f560,plain,(
% 5.46/1.12    spl14_17 <=> l2_lattices(sK0)),
% 5.46/1.12    introduced(avatar_definition,[new_symbols(naming,[spl14_17])])).
% 5.46/1.12  fof(f949,plain,(
% 5.46/1.12    ( ! [X0] : (k15_lattice3(sK0,X0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) )),
% 5.46/1.12    inference(subsumption_resolution,[],[f948,f229])).
% 5.46/1.12  fof(f229,plain,(
% 5.46/1.12    ( ! [X0] : (m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 5.46/1.12    inference(subsumption_resolution,[],[f228,f122])).
% 5.46/1.12  fof(f228,plain,(
% 5.46/1.12    ( ! [X0] : (~l3_lattices(sK0) | m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))) )),
% 5.46/1.12    inference(resolution,[],[f119,f169])).
% 5.46/1.12  fof(f169,plain,(
% 5.46/1.12    ( ! [X0,X1] : (v2_struct_0(X0) | ~l3_lattices(X0) | m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))) )),
% 5.46/1.12    inference(cnf_transformation,[],[f63])).
% 5.46/1.12  fof(f63,plain,(
% 5.46/1.12    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(flattening,[],[f62])).
% 5.46/1.12  fof(f62,plain,(
% 5.46/1.12    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 5.46/1.12    inference(ennf_transformation,[],[f20])).
% 5.46/1.12  fof(f20,axiom,(
% 5.46/1.12    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 5.46/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 5.46/1.12  fof(f948,plain,(
% 5.46/1.12    ( ! [X0] : (k15_lattice3(sK0,X0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) )),
% 5.46/1.12    inference(subsumption_resolution,[],[f942,f229])).
% 5.46/1.12  fof(f942,plain,(
% 5.46/1.12    ( ! [X0] : (k15_lattice3(sK0,X0) = k1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0)) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~l2_lattices(sK0) | v2_struct_0(sK0)) )),
% 5.46/1.12    inference(resolution,[],[f847,f133])).
% 5.46/1.12  fof(f133,plain,(
% 5.46/1.12    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) = X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | v2_struct_0(X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f74])).
% 5.46/1.12  fof(f74,plain,(
% 5.46/1.12    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k1_lattices(X0,X1,X2) != X2) & (k1_lattices(X0,X1,X2) = X2 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(nnf_transformation,[],[f40])).
% 5.46/1.12  fof(f40,plain,(
% 5.46/1.12    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l2_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(flattening,[],[f39])).
% 5.46/1.12  fof(f39,plain,(
% 5.46/1.12    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l2_lattices(X0) | v2_struct_0(X0)))),
% 5.46/1.12    inference(ennf_transformation,[],[f11])).
% 5.46/1.12  fof(f11,axiom,(
% 5.46/1.12    ! [X0] : ((l2_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k1_lattices(X0,X1,X2) = X2))))),
% 5.46/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_lattices)).
% 5.46/1.12  fof(f847,plain,(
% 5.46/1.12    ( ! [X0] : (r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) )),
% 5.46/1.12    inference(subsumption_resolution,[],[f840,f229])).
% 5.46/1.12  fof(f840,plain,(
% 5.46/1.12    ( ! [X0] : (~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) )),
% 5.46/1.12    inference(resolution,[],[f836,f257])).
% 5.46/1.12  fof(f257,plain,(
% 5.46/1.12    ( ! [X2,X1] : (~r4_lattice3(sK0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X2),X1)) )),
% 5.46/1.12    inference(subsumption_resolution,[],[f256,f119])).
% 5.46/1.12  fof(f256,plain,(
% 5.46/1.12    ( ! [X2,X1] : (~r4_lattice3(sK0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X2),X1) | v2_struct_0(sK0)) )),
% 5.46/1.12    inference(subsumption_resolution,[],[f255,f120])).
% 5.46/1.12  fof(f255,plain,(
% 5.46/1.12    ( ! [X2,X1] : (~r4_lattice3(sK0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X2),X1) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 5.46/1.12    inference(subsumption_resolution,[],[f254,f121])).
% 5.46/1.12  fof(f254,plain,(
% 5.46/1.12    ( ! [X2,X1] : (~r4_lattice3(sK0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X2),X1) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 5.46/1.12    inference(subsumption_resolution,[],[f239,f122])).
% 5.46/1.12  fof(f239,plain,(
% 5.46/1.12    ( ! [X2,X1] : (~r4_lattice3(sK0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(sK0)) | r1_lattices(sK0,k15_lattice3(sK0,X2),X1) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) )),
% 5.46/1.12    inference(resolution,[],[f229,f201])).
% 5.46/1.12  fof(f201,plain,(
% 5.46/1.12    ( ! [X4,X0,X1] : (~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 5.46/1.12    inference(duplicate_literal_removal,[],[f192])).
% 5.46/1.12  fof(f192,plain,(
% 5.46/1.12    ( ! [X4,X0,X1] : (r1_lattices(X0,k15_lattice3(X0,X1),X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 5.46/1.12    inference(equality_resolution,[],[f156])).
% 5.46/1.12  fof(f156,plain,(
% 5.46/1.12    ( ! [X4,X2,X0,X1] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0)) | k15_lattice3(X0,X1) != X2 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f93])).
% 5.46/1.12  fof(f93,plain,(
% 5.46/1.12    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (~r1_lattices(X0,X2,sK6(X0,X1,X2)) & r4_lattice3(X0,sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f91,f92])).
% 5.46/1.12  fof(f92,plain,(
% 5.46/1.12    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,X2,sK6(X0,X1,X2)) & r4_lattice3(X0,sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 5.46/1.12    introduced(choice_axiom,[])).
% 5.46/1.12  fof(f91,plain,(
% 5.46/1.12    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X4] : (r1_lattices(X0,X2,X4) | ~r4_lattice3(X0,X4,X1) | ~m1_subset_1(X4,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(rectify,[],[f90])).
% 5.46/1.12  fof(f90,plain,(
% 5.46/1.12    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | ? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1)) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(flattening,[],[f89])).
% 5.46/1.12  fof(f89,plain,(
% 5.46/1.12    ! [X0] : (! [X1,X2] : (((k15_lattice3(X0,X1) = X2 | (? [X3] : (~r1_lattices(X0,X2,X3) & r4_lattice3(X0,X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X2,X1))) & ((! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1)) | k15_lattice3(X0,X1) != X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(nnf_transformation,[],[f56])).
% 5.46/1.12  fof(f56,plain,(
% 5.46/1.12    ! [X0] : (! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : (r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(flattening,[],[f55])).
% 5.46/1.12  fof(f55,plain,(
% 5.46/1.12    ! [X0] : ((! [X1,X2] : ((k15_lattice3(X0,X1) = X2 <=> (! [X3] : ((r1_lattices(X0,X2,X3) | ~r4_lattice3(X0,X3,X1)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r4_lattice3(X0,X2,X1))) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 5.46/1.12    inference(ennf_transformation,[],[f18])).
% 5.46/1.12  fof(f18,axiom,(
% 5.46/1.12    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k15_lattice3(X0,X1) = X2 <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r4_lattice3(X0,X3,X1) => r1_lattices(X0,X2,X3))) & r4_lattice3(X0,X2,X1))))))),
% 5.46/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d21_lattice3)).
% 5.46/1.12  fof(f836,plain,(
% 5.46/1.12    ( ! [X0] : (r4_lattice3(sK0,k15_lattice3(sK0,X0),k1_xboole_0)) )),
% 5.46/1.12    inference(resolution,[],[f571,f124])).
% 5.46/1.12  fof(f124,plain,(
% 5.46/1.12    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f4])).
% 5.46/1.12  fof(f4,axiom,(
% 5.46/1.12    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 5.46/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 5.46/1.12  fof(f571,plain,(
% 5.46/1.12    ( ! [X0,X1] : (~r1_tarski(X1,sK9(sK0,k15_lattice3(sK0,X0),X1)) | r4_lattice3(sK0,k15_lattice3(sK0,X0),X1)) )),
% 5.46/1.12    inference(resolution,[],[f298,f178])).
% 5.46/1.12  fof(f178,plain,(
% 5.46/1.12    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f65])).
% 5.46/1.12  fof(f65,plain,(
% 5.46/1.12    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 5.46/1.12    inference(ennf_transformation,[],[f8])).
% 5.46/1.12  fof(f8,axiom,(
% 5.46/1.12    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 5.46/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 5.46/1.12  fof(f298,plain,(
% 5.46/1.12    ( ! [X15,X16] : (r2_hidden(sK9(sK0,k15_lattice3(sK0,X15),X16),X16) | r4_lattice3(sK0,k15_lattice3(sK0,X15),X16)) )),
% 5.46/1.12    inference(subsumption_resolution,[],[f297,f119])).
% 5.46/1.12  fof(f297,plain,(
% 5.46/1.12    ( ! [X15,X16] : (r2_hidden(sK9(sK0,k15_lattice3(sK0,X15),X16),X16) | r4_lattice3(sK0,k15_lattice3(sK0,X15),X16) | v2_struct_0(sK0)) )),
% 5.46/1.12    inference(subsumption_resolution,[],[f249,f122])).
% 5.46/1.12  fof(f249,plain,(
% 5.46/1.12    ( ! [X15,X16] : (r2_hidden(sK9(sK0,k15_lattice3(sK0,X15),X16),X16) | r4_lattice3(sK0,k15_lattice3(sK0,X15),X16) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 5.46/1.12    inference(resolution,[],[f229,f166])).
% 5.46/1.12  fof(f166,plain,(
% 5.46/1.12    ( ! [X2,X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r2_hidden(sK9(X0,X1,X2),X2) | r4_lattice3(X0,X1,X2) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f102])).
% 5.46/1.12  fof(f102,plain,(
% 5.46/1.12    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | (~r1_lattices(X0,sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f100,f101])).
% 5.46/1.12  fof(f101,plain,(
% 5.46/1.12    ! [X2,X1,X0] : (? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (~r1_lattices(X0,sK9(X0,X1,X2),X1) & r2_hidden(sK9(X0,X1,X2),X2) & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))))),
% 5.46/1.12    introduced(choice_axiom,[])).
% 5.46/1.12  fof(f100,plain,(
% 5.46/1.12    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X4] : (r1_lattices(X0,X4,X1) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(rectify,[],[f99])).
% 5.46/1.12  fof(f99,plain,(
% 5.46/1.12    ! [X0] : (! [X1] : (! [X2] : ((r4_lattice3(X0,X1,X2) | ? [X3] : (~r1_lattices(X0,X3,X1) & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0)))) & (! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~r4_lattice3(X0,X1,X2))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(nnf_transformation,[],[f60])).
% 5.46/1.12  fof(f60,plain,(
% 5.46/1.12    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(flattening,[],[f59])).
% 5.46/1.12  fof(f59,plain,(
% 5.46/1.12    ! [X0] : (! [X1] : (! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : ((r1_lattices(X0,X3,X1) | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 5.46/1.12    inference(ennf_transformation,[],[f17])).
% 5.46/1.12  fof(f17,axiom,(
% 5.46/1.12    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (r4_lattice3(X0,X1,X2) <=> ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => r1_lattices(X0,X3,X1))))))),
% 5.46/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_lattice3)).
% 5.46/1.12  fof(f596,plain,(
% 5.46/1.12    ( ! [X4,X3] : (k15_lattice3(sK0,X3) = k2_lattices(sK0,k15_lattice3(sK0,X3),k1_lattices(sK0,k15_lattice3(sK0,X3),k15_lattice3(sK0,X4)))) ) | ~spl14_11),
% 5.46/1.12    inference(resolution,[],[f293,f229])).
% 5.46/1.12  fof(f293,plain,(
% 5.46/1.12    ( ! [X12,X11] : (~m1_subset_1(X11,u1_struct_0(sK0)) | k2_lattices(sK0,X11,k1_lattices(sK0,X11,k15_lattice3(sK0,X12))) = X11) ) | ~spl14_11),
% 5.46/1.12    inference(avatar_component_clause,[],[f292])).
% 5.46/1.12  fof(f292,plain,(
% 5.46/1.12    spl14_11 <=> ! [X11,X12] : (k2_lattices(sK0,X11,k1_lattices(sK0,X11,k15_lattice3(sK0,X12))) = X11 | ~m1_subset_1(X11,u1_struct_0(sK0)))),
% 5.46/1.12    introduced(avatar_definition,[new_symbols(naming,[spl14_11])])).
% 5.46/1.12  fof(f2236,plain,(
% 5.46/1.12    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))) ) | ~spl14_53),
% 5.46/1.12    inference(avatar_component_clause,[],[f2235])).
% 5.46/1.12  fof(f2235,plain,(
% 5.46/1.12    spl14_53 <=> ! [X0] : k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0)))),
% 5.46/1.12    introduced(avatar_definition,[new_symbols(naming,[spl14_53])])).
% 5.46/1.12  fof(f4893,plain,(
% 5.46/1.12    ~spl14_1),
% 5.46/1.12    inference(avatar_contradiction_clause,[],[f4892])).
% 5.46/1.12  fof(f4892,plain,(
% 5.46/1.12    $false | ~spl14_1),
% 5.46/1.12    inference(subsumption_resolution,[],[f206,f119])).
% 5.46/1.12  fof(f206,plain,(
% 5.46/1.12    v2_struct_0(sK0) | ~spl14_1),
% 5.46/1.12    inference(avatar_component_clause,[],[f204])).
% 5.46/1.12  fof(f204,plain,(
% 5.46/1.12    spl14_1 <=> v2_struct_0(sK0)),
% 5.46/1.12    introduced(avatar_definition,[new_symbols(naming,[spl14_1])])).
% 5.46/1.12  fof(f4741,plain,(
% 5.46/1.12    spl14_5 | ~spl14_6 | ~spl14_11 | ~spl14_12 | ~spl14_17 | ~spl14_69),
% 5.46/1.12    inference(avatar_contradiction_clause,[],[f4740])).
% 5.46/1.12  fof(f4740,plain,(
% 5.46/1.12    $false | (spl14_5 | ~spl14_6 | ~spl14_11 | ~spl14_12 | ~spl14_17 | ~spl14_69)),
% 5.46/1.12    inference(subsumption_resolution,[],[f4739,f222])).
% 5.46/1.12  fof(f222,plain,(
% 5.46/1.12    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl14_5),
% 5.46/1.12    inference(avatar_component_clause,[],[f220])).
% 5.46/1.12  fof(f220,plain,(
% 5.46/1.12    spl14_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 5.46/1.12    introduced(avatar_definition,[new_symbols(naming,[spl14_5])])).
% 5.46/1.12  fof(f4739,plain,(
% 5.46/1.12    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | (~spl14_6 | ~spl14_11 | ~spl14_12 | ~spl14_17 | ~spl14_69)),
% 5.46/1.12    inference(forward_demodulation,[],[f4731,f3513])).
% 5.46/1.12  fof(f3513,plain,(
% 5.46/1.12    ( ! [X5] : (k5_lattices(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X5),k5_lattices(sK0))) ) | (~spl14_12 | ~spl14_69)),
% 5.46/1.12    inference(forward_demodulation,[],[f320,f2385])).
% 5.46/1.12  fof(f2385,plain,(
% 5.46/1.12    k5_lattices(sK0) = sK3(sK0) | ~spl14_69),
% 5.46/1.12    inference(avatar_component_clause,[],[f2383])).
% 5.46/1.12  fof(f2383,plain,(
% 5.46/1.12    spl14_69 <=> k5_lattices(sK0) = sK3(sK0)),
% 5.46/1.12    introduced(avatar_definition,[new_symbols(naming,[spl14_69])])).
% 5.46/1.12  fof(f320,plain,(
% 5.46/1.12    ( ! [X5] : (sK3(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X5),sK3(sK0))) ) | ~spl14_12),
% 5.46/1.12    inference(avatar_component_clause,[],[f319])).
% 5.46/1.12  fof(f319,plain,(
% 5.46/1.12    spl14_12 <=> ! [X5] : sK3(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X5),sK3(sK0))),
% 5.46/1.12    introduced(avatar_definition,[new_symbols(naming,[spl14_12])])).
% 5.46/1.12  fof(f4731,plain,(
% 5.46/1.12    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | (~spl14_6 | ~spl14_11 | ~spl14_17)),
% 5.46/1.12    inference(superposition,[],[f4523,f396])).
% 5.46/1.12  fof(f396,plain,(
% 5.46/1.12    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~spl14_6),
% 5.46/1.12    inference(subsumption_resolution,[],[f395,f119])).
% 5.46/1.12  fof(f395,plain,(
% 5.46/1.12    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | v2_struct_0(sK0) | ~spl14_6),
% 5.46/1.12    inference(subsumption_resolution,[],[f394,f120])).
% 5.46/1.12  fof(f394,plain,(
% 5.46/1.12    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl14_6),
% 5.46/1.12    inference(subsumption_resolution,[],[f393,f121])).
% 5.46/1.12  fof(f393,plain,(
% 5.46/1.12    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl14_6),
% 5.46/1.12    inference(subsumption_resolution,[],[f382,f122])).
% 5.46/1.12  fof(f382,plain,(
% 5.46/1.12    k5_lattices(sK0) = k15_lattice3(sK0,a_2_3_lattice3(sK0,k5_lattices(sK0))) | ~l3_lattices(sK0) | ~v4_lattice3(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0) | ~spl14_6),
% 5.46/1.12    inference(resolution,[],[f339,f151])).
% 5.46/1.12  fof(f339,plain,(
% 5.46/1.12    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl14_6),
% 5.46/1.12    inference(subsumption_resolution,[],[f334,f119])).
% 5.46/1.12  fof(f334,plain,(
% 5.46/1.12    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl14_6),
% 5.46/1.12    inference(resolution,[],[f262,f135])).
% 5.46/1.12  fof(f135,plain,(
% 5.46/1.12    ( ! [X0] : (~l1_lattices(X0) | m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f42])).
% 5.46/1.12  fof(f42,plain,(
% 5.46/1.12    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(flattening,[],[f41])).
% 5.46/1.12  fof(f41,plain,(
% 5.46/1.12    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 5.46/1.12    inference(ennf_transformation,[],[f13])).
% 5.46/1.12  fof(f13,axiom,(
% 5.46/1.12    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 5.46/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 5.46/1.12  fof(f262,plain,(
% 5.46/1.12    l1_lattices(sK0) | ~spl14_6),
% 5.46/1.12    inference(avatar_component_clause,[],[f261])).
% 5.46/1.12  fof(f261,plain,(
% 5.46/1.12    spl14_6 <=> l1_lattices(sK0)),
% 5.46/1.12    introduced(avatar_definition,[new_symbols(naming,[spl14_6])])).
% 5.46/1.12  fof(f3082,plain,(
% 5.46/1.12    ~spl14_3 | ~spl14_6 | spl14_69 | ~spl14_70),
% 5.46/1.12    inference(avatar_contradiction_clause,[],[f3081])).
% 5.46/1.12  fof(f3081,plain,(
% 5.46/1.12    $false | (~spl14_3 | ~spl14_6 | spl14_69 | ~spl14_70)),
% 5.46/1.12    inference(subsumption_resolution,[],[f3080,f119])).
% 5.46/1.12  fof(f3080,plain,(
% 5.46/1.12    v2_struct_0(sK0) | (~spl14_3 | ~spl14_6 | spl14_69 | ~spl14_70)),
% 5.46/1.12    inference(subsumption_resolution,[],[f3079,f262])).
% 5.46/1.12  fof(f3079,plain,(
% 5.46/1.12    ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl14_3 | ~spl14_6 | spl14_69 | ~spl14_70)),
% 5.46/1.12    inference(subsumption_resolution,[],[f3078,f213])).
% 5.46/1.12  fof(f213,plain,(
% 5.46/1.12    v13_lattices(sK0) | ~spl14_3),
% 5.46/1.12    inference(avatar_component_clause,[],[f212])).
% 5.46/1.12  fof(f212,plain,(
% 5.46/1.12    spl14_3 <=> v13_lattices(sK0)),
% 5.46/1.12    introduced(avatar_definition,[new_symbols(naming,[spl14_3])])).
% 5.46/1.12  fof(f3078,plain,(
% 5.46/1.12    ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl14_3 | ~spl14_6 | spl14_69 | ~spl14_70)),
% 5.46/1.12    inference(subsumption_resolution,[],[f3077,f2359])).
% 5.46/1.12  fof(f2359,plain,(
% 5.46/1.12    m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | (~spl14_3 | ~spl14_6)),
% 5.46/1.12    inference(subsumption_resolution,[],[f2358,f119])).
% 5.46/1.12  fof(f2358,plain,(
% 5.46/1.12    m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | v2_struct_0(sK0) | (~spl14_3 | ~spl14_6)),
% 5.46/1.12    inference(subsumption_resolution,[],[f2357,f262])).
% 5.46/1.12  fof(f2357,plain,(
% 5.46/1.12    m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl14_3),
% 5.46/1.12    inference(resolution,[],[f213,f140])).
% 5.46/1.12  fof(f140,plain,(
% 5.46/1.12    ( ! [X0] : (~v13_lattices(X0) | m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f83])).
% 5.46/1.12  fof(f83,plain,(
% 5.46/1.12    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f80,f82,f81])).
% 5.46/1.12  fof(f81,plain,(
% 5.46/1.12    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 5.46/1.12    introduced(choice_axiom,[])).
% 5.46/1.12  fof(f82,plain,(
% 5.46/1.12    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 5.46/1.12    introduced(choice_axiom,[])).
% 5.46/1.12  fof(f80,plain,(
% 5.46/1.12    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(rectify,[],[f79])).
% 5.46/1.12  fof(f79,plain,(
% 5.46/1.12    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(nnf_transformation,[],[f46])).
% 5.46/1.12  fof(f46,plain,(
% 5.46/1.12    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(flattening,[],[f45])).
% 5.46/1.12  fof(f45,plain,(
% 5.46/1.12    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 5.46/1.12    inference(ennf_transformation,[],[f16])).
% 5.46/1.12  fof(f16,axiom,(
% 5.46/1.12    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 5.46/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 5.46/1.12  fof(f3077,plain,(
% 5.46/1.12    ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl14_3 | ~spl14_6 | spl14_69 | ~spl14_70)),
% 5.46/1.12    inference(subsumption_resolution,[],[f3076,f2614])).
% 5.46/1.12  fof(f2614,plain,(
% 5.46/1.12    sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0))) | (~spl14_3 | ~spl14_6 | ~spl14_70)),
% 5.46/1.12    inference(subsumption_resolution,[],[f2613,f119])).
% 5.46/1.12  fof(f2613,plain,(
% 5.46/1.12    sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0))) | v2_struct_0(sK0) | (~spl14_3 | ~spl14_6 | ~spl14_70)),
% 5.46/1.12    inference(subsumption_resolution,[],[f2612,f262])).
% 5.46/1.12  fof(f2612,plain,(
% 5.46/1.12    sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0))) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl14_3 | ~spl14_70)),
% 5.46/1.12    inference(subsumption_resolution,[],[f2591,f213])).
% 5.46/1.12  fof(f2591,plain,(
% 5.46/1.12    sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0))) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl14_70),
% 5.46/1.12    inference(resolution,[],[f2389,f141])).
% 5.46/1.12  fof(f141,plain,(
% 5.46/1.12    ( ! [X4,X0] : (~m1_subset_1(X4,u1_struct_0(X0)) | sK3(X0) = k2_lattices(X0,sK3(X0),X4) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f83])).
% 5.46/1.12  fof(f2389,plain,(
% 5.46/1.12    m1_subset_1(sK1(sK0,sK3(sK0)),u1_struct_0(sK0)) | ~spl14_70),
% 5.46/1.12    inference(avatar_component_clause,[],[f2387])).
% 5.46/1.12  fof(f2387,plain,(
% 5.46/1.12    spl14_70 <=> m1_subset_1(sK1(sK0,sK3(sK0)),u1_struct_0(sK0))),
% 5.46/1.12    introduced(avatar_definition,[new_symbols(naming,[spl14_70])])).
% 5.46/1.12  fof(f3076,plain,(
% 5.46/1.12    sK3(sK0) != k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0))) | ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl14_3 | ~spl14_6 | spl14_69 | ~spl14_70)),
% 5.46/1.12    inference(subsumption_resolution,[],[f3075,f2384])).
% 5.46/1.12  fof(f2384,plain,(
% 5.46/1.12    k5_lattices(sK0) != sK3(sK0) | spl14_69),
% 5.46/1.12    inference(avatar_component_clause,[],[f2383])).
% 5.46/1.12  fof(f3075,plain,(
% 5.46/1.12    k5_lattices(sK0) = sK3(sK0) | sK3(sK0) != k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0))) | ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl14_3 | ~spl14_6 | ~spl14_70)),
% 5.46/1.12    inference(trivial_inequality_removal,[],[f3074])).
% 5.46/1.12  fof(f3074,plain,(
% 5.46/1.12    sK3(sK0) != sK3(sK0) | k5_lattices(sK0) = sK3(sK0) | sK3(sK0) != k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0))) | ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl14_3 | ~spl14_6 | ~spl14_70)),
% 5.46/1.12    inference(superposition,[],[f139,f2617])).
% 5.46/1.12  fof(f2617,plain,(
% 5.46/1.12    sK3(sK0) = k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0)) | (~spl14_3 | ~spl14_6 | ~spl14_70)),
% 5.46/1.12    inference(subsumption_resolution,[],[f2616,f119])).
% 5.46/1.12  fof(f2616,plain,(
% 5.46/1.12    sK3(sK0) = k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0)) | v2_struct_0(sK0) | (~spl14_3 | ~spl14_6 | ~spl14_70)),
% 5.46/1.12    inference(subsumption_resolution,[],[f2615,f262])).
% 5.46/1.12  fof(f2615,plain,(
% 5.46/1.12    sK3(sK0) = k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl14_3 | ~spl14_70)),
% 5.46/1.12    inference(subsumption_resolution,[],[f2592,f213])).
% 5.46/1.12  fof(f2592,plain,(
% 5.46/1.12    sK3(sK0) = k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl14_70),
% 5.46/1.12    inference(resolution,[],[f2389,f142])).
% 5.46/1.12  fof(f142,plain,(
% 5.46/1.12    ( ! [X4,X0] : (~m1_subset_1(X4,u1_struct_0(X0)) | sK3(X0) = k2_lattices(X0,X4,sK3(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f83])).
% 5.46/1.12  fof(f139,plain,(
% 5.46/1.12    ( ! [X0,X1] : (k2_lattices(X0,sK1(X0,X1),X1) != X1 | k5_lattices(X0) = X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f78])).
% 5.46/1.12  fof(f78,plain,(
% 5.46/1.12    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f76,f77])).
% 5.46/1.12  fof(f77,plain,(
% 5.46/1.12    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 5.46/1.12    introduced(choice_axiom,[])).
% 5.46/1.12  fof(f76,plain,(
% 5.46/1.12    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(rectify,[],[f75])).
% 5.46/1.12  fof(f75,plain,(
% 5.46/1.12    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(nnf_transformation,[],[f44])).
% 5.46/1.12  fof(f44,plain,(
% 5.46/1.12    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 5.46/1.12    inference(flattening,[],[f43])).
% 5.46/1.12  fof(f43,plain,(
% 5.46/1.12    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 5.46/1.12    inference(ennf_transformation,[],[f10])).
% 5.46/1.12  fof(f10,axiom,(
% 5.46/1.12    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 5.46/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 5.46/1.12  fof(f2390,plain,(
% 5.46/1.12    spl14_69 | spl14_70 | ~spl14_3 | ~spl14_6),
% 5.46/1.12    inference(avatar_split_clause,[],[f2381,f261,f212,f2387,f2383])).
% 5.46/1.12  fof(f2381,plain,(
% 5.46/1.12    m1_subset_1(sK1(sK0,sK3(sK0)),u1_struct_0(sK0)) | k5_lattices(sK0) = sK3(sK0) | (~spl14_3 | ~spl14_6)),
% 5.46/1.12    inference(subsumption_resolution,[],[f2380,f119])).
% 5.46/1.12  fof(f2380,plain,(
% 5.46/1.12    m1_subset_1(sK1(sK0,sK3(sK0)),u1_struct_0(sK0)) | k5_lattices(sK0) = sK3(sK0) | v2_struct_0(sK0) | (~spl14_3 | ~spl14_6)),
% 5.46/1.12    inference(subsumption_resolution,[],[f2379,f262])).
% 5.46/1.12  fof(f2379,plain,(
% 5.46/1.12    m1_subset_1(sK1(sK0,sK3(sK0)),u1_struct_0(sK0)) | k5_lattices(sK0) = sK3(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl14_3 | ~spl14_6)),
% 5.46/1.12    inference(subsumption_resolution,[],[f2367,f213])).
% 5.46/1.12  fof(f2367,plain,(
% 5.46/1.12    m1_subset_1(sK1(sK0,sK3(sK0)),u1_struct_0(sK0)) | k5_lattices(sK0) = sK3(sK0) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl14_3 | ~spl14_6)),
% 5.46/1.12    inference(resolution,[],[f2359,f138])).
% 5.46/1.12  fof(f138,plain,(
% 5.46/1.12    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | k5_lattices(X0) = X1 | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f78])).
% 5.46/1.12  fof(f2237,plain,(
% 5.46/1.12    spl14_3 | spl14_53 | ~spl14_6 | ~spl14_7 | ~spl14_9),
% 5.46/1.12    inference(avatar_split_clause,[],[f2233,f274,f265,f261,f2235,f212])).
% 5.46/1.12  fof(f274,plain,(
% 5.46/1.12    spl14_9 <=> ! [X7,X8] : (k2_lattices(sK0,k15_lattice3(sK0,X7),X8) = k2_lattices(sK0,X8,k15_lattice3(sK0,X7)) | ~m1_subset_1(X8,u1_struct_0(sK0)))),
% 5.46/1.12    introduced(avatar_definition,[new_symbols(naming,[spl14_9])])).
% 5.46/1.12  fof(f2233,plain,(
% 5.46/1.12    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | v13_lattices(sK0)) ) | (~spl14_6 | ~spl14_7 | ~spl14_9)),
% 5.46/1.12    inference(subsumption_resolution,[],[f2232,f119])).
% 5.46/1.12  fof(f2232,plain,(
% 5.46/1.12    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | v13_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl14_6 | ~spl14_7 | ~spl14_9)),
% 5.46/1.12    inference(subsumption_resolution,[],[f2231,f262])).
% 5.46/1.12  fof(f2231,plain,(
% 5.46/1.12    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl14_7 | ~spl14_9)),
% 5.46/1.12    inference(subsumption_resolution,[],[f1567,f229])).
% 5.46/1.12  fof(f1567,plain,(
% 5.46/1.12    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | v13_lattices(sK0) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl14_7 | ~spl14_9)),
% 5.46/1.12    inference(duplicate_literal_removal,[],[f1566])).
% 5.46/1.12  fof(f1566,plain,(
% 5.46/1.12    ( ! [X0] : (k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | v13_lattices(sK0) | k15_lattice3(sK0,X0) != k2_lattices(sK0,k15_lattice3(sK0,X0),sK2(sK0,k15_lattice3(sK0,X0))) | ~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl14_7 | ~spl14_9)),
% 5.46/1.12    inference(superposition,[],[f144,f777])).
% 5.46/1.12  fof(f777,plain,(
% 5.46/1.12    ( ! [X6,X5] : (k2_lattices(sK0,k15_lattice3(sK0,X5),sK2(sK0,k15_lattice3(sK0,X6))) = k2_lattices(sK0,sK2(sK0,k15_lattice3(sK0,X6)),k15_lattice3(sK0,X5))) ) | (~spl14_7 | ~spl14_9)),
% 5.46/1.12    inference(resolution,[],[f275,f266])).
% 5.46/1.12  fof(f275,plain,(
% 5.46/1.12    ( ! [X8,X7] : (~m1_subset_1(X8,u1_struct_0(sK0)) | k2_lattices(sK0,k15_lattice3(sK0,X7),X8) = k2_lattices(sK0,X8,k15_lattice3(sK0,X7))) ) | ~spl14_9),
% 5.46/1.12    inference(avatar_component_clause,[],[f274])).
% 5.46/1.12  fof(f144,plain,(
% 5.46/1.12    ( ! [X0,X1] : (k2_lattices(X0,sK2(X0,X1),X1) != X1 | v13_lattices(X0) | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f83])).
% 5.46/1.12  fof(f570,plain,(
% 5.46/1.12    spl14_17),
% 5.46/1.12    inference(avatar_contradiction_clause,[],[f569])).
% 5.46/1.12  fof(f569,plain,(
% 5.46/1.12    $false | spl14_17),
% 5.46/1.12    inference(subsumption_resolution,[],[f568,f122])).
% 5.46/1.12  fof(f568,plain,(
% 5.46/1.12    ~l3_lattices(sK0) | spl14_17),
% 5.46/1.12    inference(resolution,[],[f562,f126])).
% 5.46/1.12  fof(f126,plain,(
% 5.46/1.12    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f33])).
% 5.46/1.12  fof(f33,plain,(
% 5.46/1.12    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 5.46/1.12    inference(ennf_transformation,[],[f14])).
% 5.46/1.12  fof(f14,axiom,(
% 5.46/1.12    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 5.46/1.12    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 5.46/1.12  fof(f562,plain,(
% 5.46/1.12    ~l2_lattices(sK0) | spl14_17),
% 5.46/1.12    inference(avatar_component_clause,[],[f560])).
% 5.46/1.12  fof(f367,plain,(
% 5.46/1.12    spl14_10),
% 5.46/1.12    inference(avatar_contradiction_clause,[],[f366])).
% 5.46/1.12  fof(f366,plain,(
% 5.46/1.12    $false | spl14_10),
% 5.46/1.12    inference(subsumption_resolution,[],[f365,f122])).
% 5.46/1.12  fof(f365,plain,(
% 5.46/1.12    ~l3_lattices(sK0) | spl14_10),
% 5.46/1.12    inference(subsumption_resolution,[],[f364,f119])).
% 5.46/1.12  fof(f364,plain,(
% 5.46/1.12    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl14_10),
% 5.46/1.12    inference(subsumption_resolution,[],[f359,f120])).
% 5.46/1.12  fof(f359,plain,(
% 5.46/1.12    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl14_10),
% 5.46/1.12    inference(resolution,[],[f290,f130])).
% 5.46/1.12  fof(f130,plain,(
% 5.46/1.12    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 5.46/1.12    inference(cnf_transformation,[],[f35])).
% 5.46/1.12  fof(f35,plain,(
% 5.46/1.12    ! [X0] : ((v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 5.46/1.12    inference(flattening,[],[f34])).
% 5.46/1.12  fof(f34,plain,(
% 5.46/1.12    ! [X0] : (((v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 5.46/1.12    inference(ennf_transformation,[],[f30])).
% 6.04/1.13  fof(f30,plain,(
% 6.04/1.13    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 6.04/1.13    inference(pure_predicate_removal,[],[f29])).
% 6.04/1.13  fof(f29,plain,(
% 6.04/1.13    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 6.04/1.13    inference(pure_predicate_removal,[],[f28])).
% 6.04/1.13  fof(f28,plain,(
% 6.04/1.13    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 6.04/1.13    inference(pure_predicate_removal,[],[f9])).
% 6.04/1.13  fof(f9,axiom,(
% 6.04/1.13    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 6.04/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 6.04/1.13  fof(f290,plain,(
% 6.04/1.13    ~v9_lattices(sK0) | spl14_10),
% 6.04/1.13    inference(avatar_component_clause,[],[f288])).
% 6.04/1.13  fof(f288,plain,(
% 6.04/1.13    spl14_10 <=> v9_lattices(sK0)),
% 6.04/1.13    introduced(avatar_definition,[new_symbols(naming,[spl14_10])])).
% 6.04/1.13  fof(f344,plain,(
% 6.04/1.13    spl14_8),
% 6.04/1.13    inference(avatar_contradiction_clause,[],[f343])).
% 6.04/1.13  fof(f343,plain,(
% 6.04/1.13    $false | spl14_8),
% 6.04/1.13    inference(subsumption_resolution,[],[f342,f122])).
% 6.04/1.13  fof(f342,plain,(
% 6.04/1.13    ~l3_lattices(sK0) | spl14_8),
% 6.04/1.13    inference(subsumption_resolution,[],[f341,f119])).
% 6.04/1.13  fof(f341,plain,(
% 6.04/1.13    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl14_8),
% 6.04/1.13    inference(subsumption_resolution,[],[f340,f120])).
% 6.04/1.13  fof(f340,plain,(
% 6.04/1.13    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl14_8),
% 6.04/1.13    inference(resolution,[],[f272,f129])).
% 6.04/1.13  fof(f129,plain,(
% 6.04/1.13    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 6.04/1.13    inference(cnf_transformation,[],[f35])).
% 6.04/1.13  fof(f272,plain,(
% 6.04/1.13    ~v6_lattices(sK0) | spl14_8),
% 6.04/1.13    inference(avatar_component_clause,[],[f270])).
% 6.04/1.13  fof(f270,plain,(
% 6.04/1.13    spl14_8 <=> v6_lattices(sK0)),
% 6.04/1.13    introduced(avatar_definition,[new_symbols(naming,[spl14_8])])).
% 6.04/1.13  fof(f321,plain,(
% 6.04/1.13    ~spl14_6 | ~spl14_3 | spl14_12),
% 6.04/1.13    inference(avatar_split_clause,[],[f317,f319,f212,f261])).
% 6.04/1.13  fof(f317,plain,(
% 6.04/1.13    ( ! [X5] : (sK3(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X5),sK3(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0)) )),
% 6.04/1.13    inference(subsumption_resolution,[],[f242,f119])).
% 6.04/1.13  fof(f242,plain,(
% 6.04/1.13    ( ! [X5] : (sK3(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X5),sK3(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 6.04/1.13    inference(resolution,[],[f229,f142])).
% 6.04/1.13  fof(f316,plain,(
% 6.04/1.13    ~spl14_6 | spl14_3 | spl14_7),
% 6.04/1.13    inference(avatar_split_clause,[],[f315,f265,f212,f261])).
% 6.04/1.13  fof(f315,plain,(
% 6.04/1.13    ( ! [X6] : (m1_subset_1(sK2(sK0,k15_lattice3(sK0,X6)),u1_struct_0(sK0)) | v13_lattices(sK0) | ~l1_lattices(sK0)) )),
% 6.04/1.13    inference(subsumption_resolution,[],[f243,f119])).
% 6.04/1.13  fof(f243,plain,(
% 6.04/1.13    ( ! [X6] : (m1_subset_1(sK2(sK0,k15_lattice3(sK0,X6)),u1_struct_0(sK0)) | v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 6.04/1.13    inference(resolution,[],[f229,f143])).
% 6.04/1.13  fof(f143,plain,(
% 6.04/1.13    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 6.04/1.13    inference(cnf_transformation,[],[f83])).
% 6.04/1.13  fof(f314,plain,(
% 6.04/1.13    spl14_6),
% 6.04/1.13    inference(avatar_contradiction_clause,[],[f313])).
% 6.04/1.13  fof(f313,plain,(
% 6.04/1.13    $false | spl14_6),
% 6.04/1.13    inference(subsumption_resolution,[],[f312,f122])).
% 6.04/1.13  fof(f312,plain,(
% 6.04/1.13    ~l3_lattices(sK0) | spl14_6),
% 6.04/1.13    inference(resolution,[],[f263,f125])).
% 6.04/1.13  fof(f125,plain,(
% 6.04/1.13    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 6.04/1.13    inference(cnf_transformation,[],[f33])).
% 6.04/1.13  fof(f263,plain,(
% 6.04/1.13    ~l1_lattices(sK0) | spl14_6),
% 6.04/1.13    inference(avatar_component_clause,[],[f261])).
% 6.04/1.13  fof(f294,plain,(
% 6.04/1.13    ~spl14_10 | spl14_11),
% 6.04/1.13    inference(avatar_split_clause,[],[f286,f292,f288])).
% 6.04/1.13  fof(f286,plain,(
% 6.04/1.13    ( ! [X12,X11] : (k2_lattices(sK0,X11,k1_lattices(sK0,X11,k15_lattice3(sK0,X12))) = X11 | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~v9_lattices(sK0)) )),
% 6.04/1.13    inference(subsumption_resolution,[],[f285,f119])).
% 6.04/1.13  fof(f285,plain,(
% 6.04/1.13    ( ! [X12,X11] : (k2_lattices(sK0,X11,k1_lattices(sK0,X11,k15_lattice3(sK0,X12))) = X11 | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~v9_lattices(sK0) | v2_struct_0(sK0)) )),
% 6.04/1.13    inference(subsumption_resolution,[],[f247,f122])).
% 6.04/1.13  fof(f247,plain,(
% 6.04/1.13    ( ! [X12,X11] : (k2_lattices(sK0,X11,k1_lattices(sK0,X11,k15_lattice3(sK0,X12))) = X11 | ~m1_subset_1(X11,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) )),
% 6.04/1.13    inference(resolution,[],[f229,f160])).
% 6.04/1.13  fof(f160,plain,(
% 6.04/1.13    ( ! [X4,X0,X3] : (~m1_subset_1(X4,u1_struct_0(X0)) | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v9_lattices(X0) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 6.04/1.13    inference(cnf_transformation,[],[f98])).
% 6.04/1.13  fof(f98,plain,(
% 6.04/1.13    ! [X0] : (((v9_lattices(X0) | ((sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),sK8(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.04/1.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8])],[f95,f97,f96])).
% 6.04/1.13  fof(f96,plain,(
% 6.04/1.13    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK7(X0),u1_struct_0(X0))))),
% 6.04/1.13    introduced(choice_axiom,[])).
% 6.04/1.13  fof(f97,plain,(
% 6.04/1.13    ! [X0] : (? [X2] : (sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK7(X0) != k2_lattices(X0,sK7(X0),k1_lattices(X0,sK7(X0),sK8(X0))) & m1_subset_1(sK8(X0),u1_struct_0(X0))))),
% 6.04/1.13    introduced(choice_axiom,[])).
% 6.04/1.13  fof(f95,plain,(
% 6.04/1.13    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.04/1.13    inference(rectify,[],[f94])).
% 6.04/1.13  fof(f94,plain,(
% 6.04/1.13    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.04/1.13    inference(nnf_transformation,[],[f58])).
% 6.04/1.13  fof(f58,plain,(
% 6.04/1.13    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 6.04/1.13    inference(flattening,[],[f57])).
% 6.04/1.13  fof(f57,plain,(
% 6.04/1.13    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 6.04/1.13    inference(ennf_transformation,[],[f12])).
% 6.04/1.13  fof(f12,axiom,(
% 6.04/1.13    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 6.04/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).
% 6.04/1.13  fof(f276,plain,(
% 6.04/1.13    ~spl14_6 | ~spl14_8 | spl14_9),
% 6.04/1.13    inference(avatar_split_clause,[],[f268,f274,f270,f261])).
% 6.04/1.13  fof(f268,plain,(
% 6.04/1.13    ( ! [X8,X7] : (k2_lattices(sK0,k15_lattice3(sK0,X7),X8) = k2_lattices(sK0,X8,k15_lattice3(sK0,X7)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~l1_lattices(sK0)) )),
% 6.04/1.13    inference(subsumption_resolution,[],[f244,f119])).
% 6.04/1.13  fof(f244,plain,(
% 6.04/1.13    ( ! [X8,X7] : (k2_lattices(sK0,k15_lattice3(sK0,X7),X8) = k2_lattices(sK0,X8,k15_lattice3(sK0,X7)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) )),
% 6.04/1.13    inference(resolution,[],[f229,f145])).
% 6.04/1.13  fof(f145,plain,(
% 6.04/1.13    ( ! [X4,X0,X3] : (~m1_subset_1(X4,u1_struct_0(X0)) | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 6.04/1.13    inference(cnf_transformation,[],[f88])).
% 6.04/1.13  fof(f88,plain,(
% 6.04/1.13    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.04/1.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f85,f87,f86])).
% 6.04/1.13  fof(f86,plain,(
% 6.04/1.13    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 6.04/1.13    introduced(choice_axiom,[])).
% 6.04/1.13  fof(f87,plain,(
% 6.04/1.13    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 6.04/1.13    introduced(choice_axiom,[])).
% 6.04/1.13  fof(f85,plain,(
% 6.04/1.13    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.04/1.13    inference(rectify,[],[f84])).
% 6.04/1.13  fof(f84,plain,(
% 6.04/1.13    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.04/1.13    inference(nnf_transformation,[],[f48])).
% 6.04/1.13  fof(f48,plain,(
% 6.04/1.13    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 6.04/1.13    inference(flattening,[],[f47])).
% 6.04/1.13  fof(f47,plain,(
% 6.04/1.13    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 6.04/1.13    inference(ennf_transformation,[],[f19])).
% 6.04/1.13  fof(f19,axiom,(
% 6.04/1.13    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 6.04/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 6.04/1.13  fof(f227,plain,(
% 6.04/1.13    spl14_2),
% 6.04/1.13    inference(avatar_contradiction_clause,[],[f226])).
% 6.04/1.13  fof(f226,plain,(
% 6.04/1.13    $false | spl14_2),
% 6.04/1.13    inference(subsumption_resolution,[],[f210,f120])).
% 6.04/1.13  fof(f210,plain,(
% 6.04/1.13    ~v10_lattices(sK0) | spl14_2),
% 6.04/1.13    inference(avatar_component_clause,[],[f208])).
% 6.04/1.13  fof(f208,plain,(
% 6.04/1.13    spl14_2 <=> v10_lattices(sK0)),
% 6.04/1.13    introduced(avatar_definition,[new_symbols(naming,[spl14_2])])).
% 6.04/1.13  fof(f225,plain,(
% 6.04/1.13    spl14_4),
% 6.04/1.13    inference(avatar_contradiction_clause,[],[f224])).
% 6.04/1.13  fof(f224,plain,(
% 6.04/1.13    $false | spl14_4),
% 6.04/1.13    inference(subsumption_resolution,[],[f218,f122])).
% 6.04/1.13  fof(f218,plain,(
% 6.04/1.13    ~l3_lattices(sK0) | spl14_4),
% 6.04/1.13    inference(avatar_component_clause,[],[f216])).
% 6.04/1.13  fof(f216,plain,(
% 6.04/1.13    spl14_4 <=> l3_lattices(sK0)),
% 6.04/1.13    introduced(avatar_definition,[new_symbols(naming,[spl14_4])])).
% 6.04/1.13  fof(f223,plain,(
% 6.04/1.13    spl14_1 | ~spl14_2 | ~spl14_3 | ~spl14_4 | ~spl14_5),
% 6.04/1.13    inference(avatar_split_clause,[],[f123,f220,f216,f212,f208,f204])).
% 6.04/1.14  fof(f123,plain,(
% 6.04/1.14    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 6.04/1.14    inference(cnf_transformation,[],[f73])).
% 6.04/1.14  % SZS output end Proof for theBenchmark
% 6.04/1.14  % (23038)------------------------------
% 6.04/1.14  % (23038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.04/1.14  % (23038)Termination reason: Refutation
% 6.04/1.14  
% 6.04/1.14  % (23038)Memory used [KB]: 15607
% 6.04/1.14  % (23038)Time elapsed: 0.692 s
% 6.04/1.14  % (23038)------------------------------
% 6.04/1.14  % (23038)------------------------------
% 6.04/1.14  % (23029)Success in time 0.765 s
%------------------------------------------------------------------------------
