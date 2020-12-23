%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : lattice3__t51_lattice3.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:59 EDT 2019

% Result     : Theorem 1.80s
% Output     : Refutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :  236 ( 650 expanded)
%              Number of leaves         :   39 ( 174 expanded)
%              Depth                    :   34
%              Number of atoms          : 1259 (4402 expanded)
%              Number of equality atoms :  141 ( 473 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37563,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f235,f239,f339,f474,f3195,f37146,f37152,f37274,f37287,f37441,f37453,f37556,f37562])).

fof(f37562,plain,(
    ~ spl11_0 ),
    inference(avatar_contradiction_clause,[],[f37561])).

fof(f37561,plain,
    ( $false
    | ~ spl11_0 ),
    inference(subsumption_resolution,[],[f210,f134])).

fof(f134,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f105,plain,
    ( ( k6_lattices(sK0) != k15_lattice3(sK0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | ~ v14_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f104])).

fof(f104,plain,
    ( ? [X0] :
        ( ( k6_lattices(X0) != k15_lattice3(X0,u1_struct_0(X0))
          | ~ l3_lattices(X0)
          | ~ v14_lattices(X0)
          | ~ v10_lattices(X0)
          | v2_struct_0(X0) )
        & l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ( k6_lattices(sK0) != k15_lattice3(sK0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v14_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
      & l3_lattices(sK0)
      & v4_lattice3(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ? [X0] :
      ( ( k6_lattices(X0) != k15_lattice3(X0,u1_struct_0(X0))
        | ~ l3_lattices(X0)
        | ~ v14_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ( k6_lattices(X0) != k15_lattice3(X0,u1_struct_0(X0))
        | ~ l3_lattices(X0)
        | ~ v14_lattices(X0)
        | ~ v10_lattices(X0)
        | v2_struct_0(X0) )
      & l3_lattices(X0)
      & v4_lattice3(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v4_lattice3(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( k6_lattices(X0) = k15_lattice3(X0,u1_struct_0(X0))
          & l3_lattices(X0)
          & v14_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( k6_lattices(X0) = k15_lattice3(X0,u1_struct_0(X0))
        & l3_lattices(X0)
        & v14_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',t51_lattice3)).

fof(f210,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_0 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl11_0
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_0])])).

fof(f37556,plain,
    ( spl11_9
    | ~ spl11_152
    | ~ spl11_1420
    | ~ spl11_1422
    | ~ spl11_1436 ),
    inference(avatar_contradiction_clause,[],[f37555])).

fof(f37555,plain,
    ( $false
    | ~ spl11_9
    | ~ spl11_152
    | ~ spl11_1420
    | ~ spl11_1422
    | ~ spl11_1436 ),
    inference(subsumption_resolution,[],[f37554,f37139])).

fof(f37139,plain,
    ( m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl11_1420 ),
    inference(avatar_component_clause,[],[f37138])).

fof(f37138,plain,
    ( spl11_1420
  <=> m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1420])])).

fof(f37554,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl11_9
    | ~ spl11_152
    | ~ spl11_1422
    | ~ spl11_1436 ),
    inference(subsumption_resolution,[],[f37553,f1350])).

fof(f1350,plain,
    ( m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl11_152 ),
    inference(avatar_component_clause,[],[f1349])).

fof(f1349,plain,
    ( spl11_152
  <=> m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_152])])).

fof(f37553,plain,
    ( ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl11_9
    | ~ spl11_1422
    | ~ spl11_1436 ),
    inference(subsumption_resolution,[],[f37510,f234])).

fof(f234,plain,
    ( k6_lattices(sK0) != k15_lattice3(sK0,u1_struct_0(sK0))
    | ~ spl11_9 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl11_9
  <=> k6_lattices(sK0) != k15_lattice3(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_9])])).

fof(f37510,plain,
    ( k6_lattices(sK0) = k15_lattice3(sK0,u1_struct_0(sK0))
    | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl11_1422
    | ~ spl11_1436 ),
    inference(superposition,[],[f37145,f37423])).

fof(f37423,plain,
    ( ! [X1] :
        ( k6_lattices(sK0) = k3_lattices(sK0,X1,k6_lattices(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_1436 ),
    inference(avatar_component_clause,[],[f37422])).

fof(f37422,plain,
    ( spl11_1436
  <=> ! [X1] :
        ( k6_lattices(sK0) = k3_lattices(sK0,X1,k6_lattices(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1436])])).

fof(f37145,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,u1_struct_0(sK0)) = k3_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_1422 ),
    inference(avatar_component_clause,[],[f37144])).

fof(f37144,plain,
    ( spl11_1422
  <=> ! [X0] :
        ( k15_lattice3(sK0,u1_struct_0(sK0)) = k3_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1422])])).

fof(f37453,plain,
    ( ~ spl11_20
    | spl11_153 ),
    inference(avatar_contradiction_clause,[],[f37452])).

fof(f37452,plain,
    ( $false
    | ~ spl11_20
    | ~ spl11_153 ),
    inference(subsumption_resolution,[],[f37451,f134])).

fof(f37451,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_20
    | ~ spl11_153 ),
    inference(subsumption_resolution,[],[f37448,f332])).

fof(f332,plain,
    ( l2_lattices(sK0)
    | ~ spl11_20 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl11_20
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_20])])).

fof(f37448,plain,
    ( ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_153 ),
    inference(resolution,[],[f1347,f159])).

fof(f159,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0] :
      ( m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k6_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',dt_k6_lattices)).

fof(f1347,plain,
    ( ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
    | ~ spl11_153 ),
    inference(avatar_component_clause,[],[f1346])).

fof(f1346,plain,
    ( spl11_153
  <=> ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_153])])).

fof(f37441,plain,
    ( ~ spl11_153
    | spl11_1436
    | ~ spl11_4
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(avatar_split_clause,[],[f37413,f3182,f331,f218,f37422,f1346])).

fof(f218,plain,
    ( spl11_4
  <=> v14_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f3182,plain,
    ( spl11_204
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_204])])).

fof(f37413,plain,
    ( ! [X4] :
        ( k6_lattices(sK0) = k3_lattices(sK0,X4,k6_lattices(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0)) )
    | ~ spl11_4
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(duplicate_literal_removal,[],[f37405])).

fof(f37405,plain,
    ( ! [X4] :
        ( k6_lattices(sK0) = k3_lattices(sK0,X4,k6_lattices(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(k6_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl11_4
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(superposition,[],[f3199,f37306])).

fof(f37306,plain,
    ( ! [X4] :
        ( k6_lattices(sK0) = k1_lattices(sK0,X4,k6_lattices(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl11_4
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f37305,f134])).

fof(f37305,plain,
    ( ! [X4] :
        ( k6_lattices(sK0) = k1_lattices(sK0,X4,k6_lattices(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl11_4
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f37293,f332])).

fof(f37293,plain,
    ( ! [X4] :
        ( ~ l2_lattices(sK0)
        | k6_lattices(sK0) = k1_lattices(sK0,X4,k6_lattices(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl11_4 ),
    inference(resolution,[],[f219,f236])).

fof(f236,plain,(
    ! [X0,X3] :
      ( ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0))
      | v2_struct_0(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(global_subsumption,[],[f159,f201])).

fof(f201,plain,(
    ! [X0,X3] :
      ( k6_lattices(X0) = k1_lattices(X0,X3,k6_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k6_lattices(X0),u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f161])).

fof(f161,plain,(
    ! [X0,X3,X1] :
      ( k1_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k6_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f109,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ( ( k1_lattices(X0,sK1(X0,X1),X1) != X1
                  | k1_lattices(X0,X1,sK1(X0,X1)) != X1 )
                & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f107,f108])).

fof(f108,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k1_lattices(X0,X2,X1) != X1
            | k1_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k1_lattices(X0,sK1(X0,X1),X1) != X1
          | k1_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f107,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k1_lattices(X0,X3,X1) = X1
                    & k1_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f106])).

fof(f106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k6_lattices(X0) = X1
              | ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k6_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k6_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v14_lattices(X0)
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v14_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k6_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',d17_lattices)).

fof(f219,plain,
    ( v14_lattices(sK0)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f218])).

fof(f3199,plain,
    ( ! [X0,X1] :
        ( k3_lattices(sK0,X1,X0) = k1_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f3198,f134])).

fof(f3198,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k3_lattices(sK0,X1,X0) = k1_lattices(sK0,X1,X0)
        | v2_struct_0(sK0) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f3196,f332])).

fof(f3196,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | k3_lattices(sK0,X1,X0) = k1_lattices(sK0,X1,X0)
        | v2_struct_0(sK0) )
    | ~ spl11_204 ),
    inference(resolution,[],[f3183,f187])).

fof(f187,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f92])).

fof(f92,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f91])).

fof(f91,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',redefinition_k3_lattices)).

fof(f3183,plain,
    ( v4_lattices(sK0)
    | ~ spl11_204 ),
    inference(avatar_component_clause,[],[f3182])).

fof(f37287,plain,(
    spl11_7 ),
    inference(avatar_contradiction_clause,[],[f37286])).

fof(f37286,plain,
    ( $false
    | ~ spl11_7 ),
    inference(subsumption_resolution,[],[f228,f137])).

fof(f137,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f228,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl11_7 ),
    inference(avatar_component_clause,[],[f227])).

fof(f227,plain,
    ( spl11_7
  <=> ~ l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_7])])).

fof(f37274,plain,
    ( spl11_5
    | ~ spl11_20
    | ~ spl11_204
    | ~ spl11_1420
    | ~ spl11_1422 ),
    inference(avatar_contradiction_clause,[],[f37273])).

fof(f37273,plain,
    ( $false
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204
    | ~ spl11_1420
    | ~ spl11_1422 ),
    inference(subsumption_resolution,[],[f37272,f134])).

fof(f37272,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204
    | ~ spl11_1420
    | ~ spl11_1422 ),
    inference(subsumption_resolution,[],[f37271,f332])).

fof(f37271,plain,
    ( ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204
    | ~ spl11_1420
    | ~ spl11_1422 ),
    inference(subsumption_resolution,[],[f37270,f37139])).

fof(f37270,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204
    | ~ spl11_1420
    | ~ spl11_1422 ),
    inference(subsumption_resolution,[],[f37267,f222])).

fof(f222,plain,
    ( ~ v14_lattices(sK0)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f221])).

fof(f221,plain,
    ( spl11_5
  <=> ~ v14_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f37267,plain,
    ( v14_lattices(sK0)
    | ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204
    | ~ spl11_1420
    | ~ spl11_1422 ),
    inference(resolution,[],[f37242,f167])).

fof(f167,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v14_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f114,plain,(
    ! [X0] :
      ( ( ( v14_lattices(X0)
          | ! [X1] :
              ( ( ( k1_lattices(X0,sK2(X0,X1),X1) != X1
                  | k1_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( k1_lattices(X0,X4,sK3(X0)) = sK3(X0)
                  & k1_lattices(X0,sK3(X0),X4) = sK3(X0) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) )
          | ~ v14_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f111,f113,f112])).

fof(f112,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k1_lattices(X0,X2,X1) != X1
            | k1_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k1_lattices(X0,sK2(X0,X1),X1) != X1
          | k1_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f113,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k1_lattices(X0,X4,X3) = X3
                & k1_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( k1_lattices(X0,X4,sK3(X0)) = sK3(X0)
              & k1_lattices(X0,sK3(X0),X4) = sK3(X0) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f111,plain,(
    ! [X0] :
      ( ( ( v14_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X3] :
              ( ! [X4] :
                  ( ( k1_lattices(X0,X4,X3) = X3
                    & k1_lattices(X0,X3,X4) = X3 )
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              & m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v14_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f110])).

fof(f110,plain,(
    ! [X0] :
      ( ( ( v14_lattices(X0)
          | ! [X1] :
              ( ? [X2] :
                  ( ( k1_lattices(X0,X2,X1) != X1
                    | k1_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ? [X1] :
              ( ! [X2] :
                  ( ( k1_lattices(X0,X2,X1) = X1
                    & k1_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v14_lattices(X0) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ( v14_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v14_lattices(X0)
      <=> ? [X1] :
            ( ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k1_lattices(X0,X2,X1) = X1
                  & k1_lattices(X0,X1,X2) = X1 ) )
            & m1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',d14_lattices)).

fof(f37242,plain,
    ( ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204
    | ~ spl11_1420
    | ~ spl11_1422 ),
    inference(subsumption_resolution,[],[f37182,f37139])).

fof(f37182,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204
    | ~ spl11_1422 ),
    inference(trivial_inequality_removal,[],[f37181])).

fof(f37181,plain,
    ( k15_lattice3(sK0,u1_struct_0(sK0)) != k15_lattice3(sK0,u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204
    | ~ spl11_1422 ),
    inference(duplicate_literal_removal,[],[f37178])).

fof(f37178,plain,
    ( k15_lattice3(sK0,u1_struct_0(sK0)) != k15_lattice3(sK0,u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ m1_subset_1(sK2(sK0,k15_lattice3(sK0,u1_struct_0(sK0))),u1_struct_0(sK0))
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204
    | ~ spl11_1422 ),
    inference(superposition,[],[f36028,f37145])).

fof(f36028,plain,
    ( ! [X1] :
        ( k3_lattices(sK0,X1,sK2(sK0,X1)) != X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X1),u1_struct_0(sK0)) )
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(duplicate_literal_removal,[],[f36027])).

fof(f36027,plain,
    ( ! [X1] :
        ( k3_lattices(sK0,X1,sK2(sK0,X1)) != X1
        | k3_lattices(sK0,X1,sK2(sK0,X1)) != X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X1),u1_struct_0(sK0)) )
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(superposition,[],[f35209,f3201])).

fof(f3201,plain,
    ( ! [X2,X3] :
        ( k3_lattices(sK0,X2,X3) = k3_lattices(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f3200,f134])).

fof(f3200,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k3_lattices(sK0,X2,X3) = k3_lattices(sK0,X3,X2)
        | v2_struct_0(sK0) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f3197,f332])).

fof(f3197,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | k3_lattices(sK0,X2,X3) = k3_lattices(sK0,X3,X2)
        | v2_struct_0(sK0) )
    | ~ spl11_204 ),
    inference(resolution,[],[f3183,f186])).

fof(f186,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f90])).

fof(f90,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f89])).

fof(f89,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k3_lattices(X0,X2,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',commutativity_k3_lattices)).

fof(f35209,plain,
    ( ! [X0] :
        ( k3_lattices(sK0,sK2(sK0,X0),X0) != X0
        | k3_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(duplicate_literal_removal,[],[f35208])).

fof(f35208,plain,
    ( ! [X0] :
        ( k3_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | k3_lattices(sK0,sK2(sK0,X0),X0) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(superposition,[],[f3212,f3199])).

fof(f3212,plain,
    ( ! [X4] :
        ( k1_lattices(sK0,X4,sK2(sK0,X4)) != X4
        | k3_lattices(sK0,sK2(sK0,X4),X4) != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X4),u1_struct_0(sK0)) )
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f3211,f134])).

fof(f3211,plain,
    ( ! [X4] :
        ( k3_lattices(sK0,sK2(sK0,X4),X4) != X4
        | k1_lattices(sK0,X4,sK2(sK0,X4)) != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ m1_subset_1(sK2(sK0,X4),u1_struct_0(sK0)) )
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f3210,f332])).

fof(f3210,plain,
    ( ! [X4] :
        ( k3_lattices(sK0,sK2(sK0,X4),X4) != X4
        | k1_lattices(sK0,X4,sK2(sK0,X4)) != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(sK2(sK0,X4),u1_struct_0(sK0)) )
    | ~ spl11_5
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f3205,f222])).

fof(f3205,plain,
    ( ! [X4] :
        ( k3_lattices(sK0,sK2(sK0,X4),X4) != X4
        | v14_lattices(sK0)
        | k1_lattices(sK0,X4,sK2(sK0,X4)) != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(sK2(sK0,X4),u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(duplicate_literal_removal,[],[f3204])).

fof(f3204,plain,
    ( ! [X4] :
        ( k3_lattices(sK0,sK2(sK0,X4),X4) != X4
        | v14_lattices(sK0)
        | k1_lattices(sK0,X4,sK2(sK0,X4)) != X4
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(sK2(sK0,X4),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(superposition,[],[f168,f3199])).

fof(f168,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,sK2(X0,X1),X1) != X1
      | v14_lattices(X0)
      | k1_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f37152,plain,(
    spl11_1421 ),
    inference(avatar_contradiction_clause,[],[f37151])).

fof(f37151,plain,
    ( $false
    | ~ spl11_1421 ),
    inference(subsumption_resolution,[],[f37150,f134])).

fof(f37150,plain,
    ( v2_struct_0(sK0)
    | ~ spl11_1421 ),
    inference(subsumption_resolution,[],[f37147,f137])).

fof(f37147,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_1421 ),
    inference(resolution,[],[f37142,f174])).

fof(f174,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',dt_k15_lattice3)).

fof(f37142,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ spl11_1421 ),
    inference(avatar_component_clause,[],[f37141])).

fof(f37141,plain,
    ( spl11_1421
  <=> ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1421])])).

fof(f37146,plain,
    ( ~ spl11_1421
    | spl11_1422
    | spl11_19
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(avatar_split_clause,[],[f37136,f3182,f331,f325,f37144,f37141])).

fof(f325,plain,
    ( spl11_19
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_19])])).

fof(f37136,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,u1_struct_0(sK0)) = k3_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0)) )
    | ~ spl11_19
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(duplicate_literal_removal,[],[f37131])).

fof(f37131,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,u1_struct_0(sK0)) = k3_lattices(sK0,k15_lattice3(sK0,u1_struct_0(sK0)),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k15_lattice3(sK0,u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_19
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(resolution,[],[f37129,f3219])).

fof(f3219,plain,
    ( ! [X0,X1] :
        ( r2_hidden(k3_lattices(sK0,X1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl11_19
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f3218,f326])).

fof(f326,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_19 ),
    inference(avatar_component_clause,[],[f325])).

fof(f3218,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0))
        | r2_hidden(k3_lattices(sK0,X1,X0),u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(resolution,[],[f3209,f173])).

fof(f173,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f38])).

fof(f38,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',t2_subset)).

fof(f3209,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k3_lattices(sK0,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f3208,f134])).

fof(f3208,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k3_lattices(sK0,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f3206,f332])).

fof(f3206,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k3_lattices(sK0,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(duplicate_literal_removal,[],[f3203])).

fof(f3203,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k3_lattices(sK0,X2,X3),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(superposition,[],[f188,f3199])).

fof(f188,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f94])).

fof(f94,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f93])).

fof(f93,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',dt_k1_lattices)).

fof(f37129,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k3_lattices(sK0,k15_lattice3(sK0,X0),X1),X0)
        | k15_lattice3(sK0,X0) = k3_lattices(sK0,k15_lattice3(sK0,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f37128,f134])).

fof(f37128,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k3_lattices(sK0,k15_lattice3(sK0,X0),X1),X0)
        | k15_lattice3(sK0,X0) = k3_lattices(sK0,k15_lattice3(sK0,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f37125,f137])).

fof(f37125,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k3_lattices(sK0,k15_lattice3(sK0,X0),X1),X0)
        | k15_lattice3(sK0,X0) = k3_lattices(sK0,k15_lattice3(sK0,X0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(resolution,[],[f13061,f174])).

fof(f13061,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))
        | ~ r2_hidden(k3_lattices(sK0,k15_lattice3(sK0,X2),X3),X2)
        | k15_lattice3(sK0,X2) = k3_lattices(sK0,k15_lattice3(sK0,X2),X3)
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f13057,f3209])).

fof(f13057,plain,
    ( ! [X2,X3] :
        ( k15_lattice3(sK0,X2) = k3_lattices(sK0,k15_lattice3(sK0,X2),X3)
        | ~ m1_subset_1(k3_lattices(sK0,k15_lattice3(sK0,X2),X3),u1_struct_0(sK0))
        | ~ r2_hidden(k3_lattices(sK0,k15_lattice3(sK0,X2),X3),X2)
        | ~ m1_subset_1(k15_lattice3(sK0,X2),u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(resolution,[],[f13054,f3207])).

fof(f3207,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,X0,k3_lattices(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(duplicate_literal_removal,[],[f3202])).

fof(f3202,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,X0,k3_lattices(sK0,X0,X1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(superposition,[],[f3176,f3199])).

fof(f3176,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,X0,k1_lattices(sK0,X0,X1))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3175,f134])).

fof(f3175,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | r1_lattices(sK0,X0,k1_lattices(sK0,X0,X1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f3174,f137])).

fof(f3174,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,X0,k1_lattices(sK0,X0,X1))
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f2603,f135])).

fof(f135,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f2603,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X2,k1_lattices(X1,X2,X0))
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f2602,f151])).

fof(f151,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f47])).

fof(f47,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',cc1_lattices)).

fof(f2602,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v6_lattices(X1)
      | r1_lattices(X1,X2,k1_lattices(X1,X2,X0))
      | v2_struct_0(X1)
      | ~ v10_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f2601,f153])).

fof(f153,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2601,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | r1_lattices(X1,X2,k1_lattices(X1,X2,X0))
      | v2_struct_0(X1)
      | ~ v10_lattices(X1) ) ),
    inference(subsumption_resolution,[],[f2600,f154])).

fof(f154,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f2600,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | r1_lattices(X1,X2,k1_lattices(X1,X2,X0))
      | v2_struct_0(X1)
      | ~ v10_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f2599])).

fof(f2599,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | r1_lattices(X1,X2,k1_lattices(X1,X2,X0))
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f155,f150])).

fof(f150,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( ~ v5_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',t22_lattices)).

fof(f13054,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | k15_lattice3(sK0,X1) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f13053,f134])).

fof(f13053,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = X0
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ r2_hidden(X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f13050,f137])).

fof(f13050,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = X0
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X1),X0)
        | ~ r2_hidden(X0,X1)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(resolution,[],[f7277,f174])).

fof(f7277,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = X2
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X1),X2)
        | ~ r2_hidden(X2,X1) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f7276,f134])).

fof(f7276,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = X2
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X1),X2)
        | ~ r2_hidden(X2,X1)
        | v2_struct_0(sK0) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f7275,f135])).

fof(f7275,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = X2
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X1),X2)
        | ~ r2_hidden(X2,X1)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f7274,f136])).

fof(f136,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f105])).

fof(f7274,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = X2
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X1),X2)
        | ~ r2_hidden(X2,X1)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f7272,f137])).

fof(f7272,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = X2
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X1),X2)
        | ~ r2_hidden(X2,X1)
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(duplicate_literal_removal,[],[f7269])).

fof(f7269,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k15_lattice3(sK0,X1) = X2
        | ~ r1_lattices(sK0,k15_lattice3(sK0,X1),X2)
        | ~ r2_hidden(X2,X1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v4_lattice3(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(resolution,[],[f5200,f156])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( r3_lattices(X0,X1,k15_lattice3(X0,X2))
      | ~ r2_hidden(X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) )
              | ~ r2_hidden(X1,X2) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f40])).

fof(f40,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v4_lattice3(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( r2_hidden(X1,X2)
             => ( r3_lattices(X0,k16_lattice3(X0,X2),X1)
                & r3_lattices(X0,X1,k15_lattice3(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',t38_lattice3)).

fof(f5200,plain,
    ( ! [X4,X5] :
        ( ~ r3_lattices(sK0,X4,X5)
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | X4 = X5
        | ~ r1_lattices(sK0,X5,X4) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f5199,f134])).

fof(f5199,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X4,X5)
        | X4 = X5
        | ~ r1_lattices(sK0,X5,X4)
        | v2_struct_0(sK0) )
    | ~ spl11_20
    | ~ spl11_204 ),
    inference(subsumption_resolution,[],[f5198,f3183])).

fof(f5198,plain,
    ( ! [X4,X5] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X4,X5)
        | X4 = X5
        | ~ r1_lattices(sK0,X5,X4)
        | ~ v4_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f5193,f332])).

fof(f5193,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X4,X5)
      | X4 = X5
      | ~ r1_lattices(sK0,X5,X4)
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f5192])).

fof(f5192,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X4,X5)
      | X4 = X5
      | ~ r1_lattices(sK0,X5,X4)
      | ~ m1_subset_1(X4,u1_struct_0(sK0))
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ l2_lattices(sK0)
      | ~ v4_lattices(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f3943,f158])).

fof(f158,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X2,X1)
      | X1 = X2
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    inference(ennf_transformation,[],[f37])).

fof(f37,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',t26_lattices)).

fof(f3943,plain,(
    ! [X0,X1] :
      ( r1_lattices(sK0,X1,X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f3942,f134])).

fof(f3942,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(subsumption_resolution,[],[f3941,f137])).

fof(f3941,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ l3_lattices(sK0)
      | r1_lattices(sK0,X1,X0)
      | v2_struct_0(sK0)
      | ~ r3_lattices(sK0,X1,X0) ) ),
    inference(resolution,[],[f2500,f135])).

fof(f2500,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | v2_struct_0(X0)
      | ~ r3_lattices(X0,X1,X2) ) ),
    inference(subsumption_resolution,[],[f2499,f151])).

fof(f2499,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(subsumption_resolution,[],[f2498,f153])).

fof(f2498,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f2497])).

fof(f2497,plain,(
    ! [X2,X0,X1] :
      ( ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f183,f154])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f121])).

fof(f121,plain,(
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
    inference(nnf_transformation,[],[f86])).

fof(f86,plain,(
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
    inference(flattening,[],[f85])).

fof(f85,plain,(
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
    inference(ennf_transformation,[],[f33])).

fof(f33,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',redefinition_r3_lattices)).

fof(f3195,plain,(
    spl11_205 ),
    inference(avatar_contradiction_clause,[],[f3194])).

fof(f3194,plain,
    ( $false
    | ~ spl11_205 ),
    inference(subsumption_resolution,[],[f3193,f137])).

fof(f3193,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl11_205 ),
    inference(subsumption_resolution,[],[f3192,f134])).

fof(f3192,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl11_205 ),
    inference(subsumption_resolution,[],[f3191,f135])).

fof(f3191,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl11_205 ),
    inference(resolution,[],[f3186,f149])).

fof(f149,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f3186,plain,
    ( ~ v4_lattices(sK0)
    | ~ spl11_205 ),
    inference(avatar_component_clause,[],[f3185])).

fof(f3185,plain,
    ( spl11_205
  <=> ~ v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_205])])).

fof(f474,plain,
    ( ~ spl11_18
    | ~ spl11_20 ),
    inference(avatar_contradiction_clause,[],[f473])).

fof(f473,plain,
    ( $false
    | ~ spl11_18
    | ~ spl11_20 ),
    inference(subsumption_resolution,[],[f471,f332])).

fof(f471,plain,
    ( ~ l2_lattices(sK0)
    | ~ spl11_18 ),
    inference(resolution,[],[f467,f142])).

fof(f142,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',dt_l2_lattices)).

fof(f467,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl11_18 ),
    inference(subsumption_resolution,[],[f462,f134])).

fof(f462,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl11_18 ),
    inference(resolution,[],[f329,f169])).

fof(f169,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f48])).

fof(f48,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',fc2_struct_0)).

fof(f329,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl11_18 ),
    inference(avatar_component_clause,[],[f328])).

fof(f328,plain,
    ( spl11_18
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_18])])).

fof(f339,plain,(
    spl11_21 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | ~ spl11_21 ),
    inference(subsumption_resolution,[],[f337,f137])).

fof(f337,plain,
    ( ~ l3_lattices(sK0)
    | ~ spl11_21 ),
    inference(resolution,[],[f335,f144])).

fof(f144,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/lattice3__t51_lattice3.p',dt_l3_lattices)).

fof(f335,plain,
    ( ~ l2_lattices(sK0)
    | ~ spl11_21 ),
    inference(avatar_component_clause,[],[f334])).

fof(f334,plain,
    ( spl11_21
  <=> ~ l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_21])])).

fof(f239,plain,(
    spl11_3 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f216,f135])).

fof(f216,plain,
    ( ~ v10_lattices(sK0)
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f215])).

fof(f215,plain,
    ( spl11_3
  <=> ~ v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f235,plain,
    ( spl11_0
    | ~ spl11_3
    | ~ spl11_5
    | ~ spl11_7
    | ~ spl11_9 ),
    inference(avatar_split_clause,[],[f138,f233,f227,f221,f215,f209])).

fof(f138,plain,
    ( k6_lattices(sK0) != k15_lattice3(sK0,u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v14_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f105])).
%------------------------------------------------------------------------------
