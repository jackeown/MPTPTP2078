%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  242 ( 547 expanded)
%              Number of leaves         :   55 ( 247 expanded)
%              Depth                    :   13
%              Number of atoms          : 1200 (2748 expanded)
%              Number of equality atoms :  195 ( 518 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f558,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f113,f115,f119,f121,f123,f128,f134,f145,f163,f165,f167,f169,f196,f203,f207,f211,f221,f229,f243,f245,f247,f261,f263,f278,f324,f336,f358,f392,f399,f420,f433,f447,f496,f518,f541,f548])).

fof(f548,plain,
    ( spl7_47
    | ~ spl7_50
    | ~ spl7_51
    | spl7_57 ),
    inference(avatar_split_clause,[],[f547,f538,f445,f431,f418])).

fof(f418,plain,
    ( spl7_47
  <=> k5_lattices(sK0) = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f431,plain,
    ( spl7_50
  <=> m1_subset_1(sK3(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f445,plain,
    ( spl7_51
  <=> ! [X1] :
        ( sK3(sK0) = k2_lattices(sK0,sK1(sK0,X1),sK3(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f538,plain,
    ( spl7_57
  <=> sK3(sK0) = k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).

fof(f547,plain,
    ( ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | k5_lattices(sK0) = sK3(sK0)
    | ~ spl7_51
    | spl7_57 ),
    inference(trivial_inequality_removal,[],[f544])).

fof(f544,plain,
    ( sK3(sK0) != sK3(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | k5_lattices(sK0) = sK3(sK0)
    | ~ spl7_51
    | spl7_57 ),
    inference(superposition,[],[f539,f446])).

fof(f446,plain,
    ( ! [X1] :
        ( sK3(sK0) = k2_lattices(sK0,sK1(sK0,X1),sK3(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = X1 )
    | ~ spl7_51 ),
    inference(avatar_component_clause,[],[f445])).

fof(f539,plain,
    ( sK3(sK0) != k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0))
    | spl7_57 ),
    inference(avatar_component_clause,[],[f538])).

fof(f541,plain,
    ( ~ spl7_57
    | ~ spl7_50
    | spl7_47
    | ~ spl7_16
    | ~ spl7_53 ),
    inference(avatar_split_clause,[],[f536,f516,f201,f418,f431,f538])).

fof(f201,plain,
    ( spl7_16
  <=> ! [X0] :
        ( k2_lattices(sK0,sK1(sK0,X0),X0) != X0
        | k5_lattices(sK0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f516,plain,
    ( spl7_53
  <=> sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f536,plain,
    ( k5_lattices(sK0) = sK3(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | sK3(sK0) != k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0))
    | ~ spl7_16
    | ~ spl7_53 ),
    inference(trivial_inequality_removal,[],[f532])).

fof(f532,plain,
    ( sK3(sK0) != sK3(sK0)
    | k5_lattices(sK0) = sK3(sK0)
    | ~ m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | sK3(sK0) != k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0))
    | ~ spl7_16
    | ~ spl7_53 ),
    inference(superposition,[],[f202,f517])).

fof(f517,plain,
    ( sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0)))
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f516])).

fof(f202,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK1(sK0,X0)) != X0
        | k5_lattices(sK0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,sK1(sK0,X0),X0) != X0 )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f201])).

fof(f518,plain,
    ( spl7_47
    | spl7_53
    | ~ spl7_50
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f506,f494,f431,f516,f418])).

fof(f494,plain,
    ( spl7_52
  <=> ! [X1] :
        ( sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,X1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f506,plain,
    ( sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0)))
    | k5_lattices(sK0) = sK3(sK0)
    | ~ spl7_50
    | ~ spl7_52 ),
    inference(resolution,[],[f495,f432])).

fof(f432,plain,
    ( m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ spl7_50 ),
    inference(avatar_component_clause,[],[f431])).

fof(f495,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,X1))
        | k5_lattices(sK0) = X1 )
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f494])).

fof(f496,plain,
    ( spl7_1
    | ~ spl7_12
    | ~ spl7_3
    | spl7_52
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f487,f209,f494,f105,f157,f99])).

fof(f99,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f157,plain,
    ( spl7_12
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f105,plain,
    ( spl7_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f209,plain,
    ( spl7_18
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK3(sK0) = k2_lattices(sK0,sK3(sK0),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f487,plain,
    ( ! [X1] :
        ( sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,X1))
        | k5_lattices(sK0) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_18 ),
    inference(resolution,[],[f210,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK1(X0,X1),u1_struct_0(X0))
      | k5_lattices(X0) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).

fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
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
    inference(rectify,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f210,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK3(sK0) = k2_lattices(sK0,sK3(sK0),X2) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f209])).

fof(f447,plain,
    ( spl7_1
    | ~ spl7_12
    | ~ spl7_3
    | spl7_51
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f438,f205,f445,f105,f157,f99])).

fof(f205,plain,
    ( spl7_17
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK3(sK0) = k2_lattices(sK0,X1,sK3(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f438,plain,
    ( ! [X1] :
        ( sK3(sK0) = k2_lattices(sK0,sK1(sK0,X1),sK3(sK0))
        | k5_lattices(sK0) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_17 ),
    inference(resolution,[],[f206,f76])).

fof(f206,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK3(sK0) = k2_lattices(sK0,X1,sK3(sK0)) )
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f205])).

fof(f433,plain,
    ( spl7_1
    | ~ spl7_4
    | spl7_50
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f416,f397,f431,f108,f99])).

fof(f108,plain,
    ( spl7_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f397,plain,
    ( spl7_45
  <=> k15_lattice3(sK0,k1_xboole_0) = sK3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f416,plain,
    ( m1_subset_1(sK3(sK0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_45 ),
    inference(superposition,[],[f92,f398])).

fof(f398,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = sK3(sK0)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f397])).

fof(f92,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f420,plain,
    ( ~ spl7_47
    | spl7_5
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f406,f397,f111,f418])).

fof(f111,plain,
    ( spl7_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f406,plain,
    ( k5_lattices(sK0) != sK3(sK0)
    | spl7_5
    | ~ spl7_45 ),
    inference(superposition,[],[f112,f398])).

fof(f112,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f111])).

fof(f399,plain,
    ( spl7_45
    | ~ spl7_37
    | ~ spl7_39 ),
    inference(avatar_split_clause,[],[f395,f356,f334,f397])).

fof(f334,plain,
    ( spl7_37
  <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f356,plain,
    ( spl7_39
  <=> ! [X0] : sK3(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).

fof(f395,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = sK3(sK0)
    | ~ spl7_37
    | ~ spl7_39 ),
    inference(forward_demodulation,[],[f335,f357])).

fof(f357,plain,
    ( ! [X0] : sK3(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0))
    | ~ spl7_39 ),
    inference(avatar_component_clause,[],[f356])).

fof(f335,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f334])).

fof(f392,plain,
    ( ~ spl7_24
    | ~ spl7_19
    | ~ spl7_34 ),
    inference(avatar_split_clause,[],[f391,f322,f219,f252])).

fof(f252,plain,
    ( spl7_24
  <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f219,plain,
    ( spl7_19
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f322,plain,
    ( spl7_34
  <=> ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f391,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl7_19
    | ~ spl7_34 ),
    inference(trivial_inequality_removal,[],[f387])).

fof(f387,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl7_19
    | ~ spl7_34 ),
    inference(superposition,[],[f220,f323])).

fof(f323,plain,
    ( ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X0)))
    | ~ spl7_34 ),
    inference(avatar_component_clause,[],[f322])).

fof(f220,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f219])).

fof(f358,plain,
    ( spl7_1
    | ~ spl7_4
    | spl7_39
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f348,f205,f356,f108,f99])).

fof(f348,plain,
    ( ! [X0] :
        ( sK3(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_17 ),
    inference(resolution,[],[f206,f92])).

fof(f336,plain,
    ( spl7_1
    | ~ spl7_12
    | ~ spl7_3
    | spl7_37
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f267,f259,f334,f105,f157,f99])).

fof(f259,plain,
    ( spl7_26
  <=> ! [X1] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).

fof(f267,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0))
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_26 ),
    inference(resolution,[],[f260,f78])).

fof(f78,plain,(
    ! [X0] :
      ( m1_subset_1(sK3(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f49,f51,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
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

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f260,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) )
    | ~ spl7_26 ),
    inference(avatar_component_clause,[],[f259])).

fof(f324,plain,
    ( spl7_1
    | ~ spl7_4
    | spl7_34
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f314,f276,f322,f108,f99])).

fof(f276,plain,
    ( spl7_28
  <=> ! [X2] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f314,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X0)))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_28 ),
    inference(resolution,[],[f277,f92])).

fof(f277,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2)) )
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f276])).

fof(f278,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_3
    | spl7_28
    | ~ spl7_26 ),
    inference(avatar_split_clause,[],[f266,f259,f276,f105,f157,f99])).

fof(f266,plain,
    ( ! [X2] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2))
        | v13_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_26 ),
    inference(resolution,[],[f260,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f263,plain,
    ( spl7_1
    | ~ spl7_4
    | spl7_24 ),
    inference(avatar_split_clause,[],[f262,f252,f108,f99])).

fof(f262,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_24 ),
    inference(resolution,[],[f253,f92])).

fof(f253,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl7_24 ),
    inference(avatar_component_clause,[],[f252])).

fof(f261,plain,
    ( ~ spl7_24
    | spl7_26
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_23 ),
    inference(avatar_split_clause,[],[f250,f241,f132,f126,f259,f252])).

fof(f126,plain,
    ( spl7_7
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f132,plain,
    ( spl7_8
  <=> ! [X1,X0] :
        ( r2_hidden(sK6(sK0,X0,X1),X0)
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f241,plain,
    ( spl7_23
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X2) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f250,plain,
    ( ! [X1] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_23 ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,
    ( ! [X1] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_23 ),
    inference(resolution,[],[f242,f137])).

fof(f137,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(superposition,[],[f136,f127])).

fof(f127,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f136,plain,
    ( ! [X0] : r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | ~ spl7_8 ),
    inference(resolution,[],[f135,f66])).

fof(f66,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f135,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK6(sK0,X0,X1))
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) )
    | ~ spl7_8 ),
    inference(resolution,[],[f133,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f133,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(sK0,X0,X1),X0)
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f132])).

fof(f242,plain,
    ( ! [X2,X3] :
        ( ~ r3_lattices(sK0,X3,X2)
        | k2_lattices(sK0,X3,X2) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f241])).

fof(f247,plain,
    ( ~ spl7_4
    | spl7_1
    | ~ spl7_2
    | spl7_22 ),
    inference(avatar_split_clause,[],[f246,f238,f102,f99,f108])).

fof(f102,plain,
    ( spl7_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f238,plain,
    ( spl7_22
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f246,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl7_22 ),
    inference(resolution,[],[f239,f71])).

fof(f71,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f239,plain,
    ( ~ v9_lattices(sK0)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f238])).

fof(f245,plain,
    ( ~ spl7_4
    | spl7_1
    | ~ spl7_2
    | spl7_21 ),
    inference(avatar_split_clause,[],[f244,f235,f102,f99,f108])).

fof(f235,plain,
    ( spl7_21
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f244,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl7_21 ),
    inference(resolution,[],[f236,f70])).

fof(f70,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f236,plain,
    ( ~ v8_lattices(sK0)
    | spl7_21 ),
    inference(avatar_component_clause,[],[f235])).

fof(f243,plain,
    ( spl7_1
    | ~ spl7_21
    | ~ spl7_22
    | ~ spl7_4
    | spl7_23
    | ~ spl7_20 ),
    inference(avatar_split_clause,[],[f232,f227,f241,f108,f238,f235,f99])).

fof(f227,plain,
    ( spl7_20
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1)
        | r1_lattices(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f232,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X2) = X3
        | ~ l3_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ v8_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_20 ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X2) = X3
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ v8_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_20 ),
    inference(resolution,[],[f228,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f228,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f227])).

fof(f229,plain,
    ( spl7_1
    | ~ spl7_13
    | ~ spl7_4
    | spl7_20
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f224,f102,f227,f108,f160,f99])).

fof(f160,plain,
    ( spl7_13
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f224,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r1_lattices(sK0,X0,X1)
        | ~ r3_lattices(sK0,X0,X1)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f223,f120])).

fof(f120,plain,
    ( v10_lattices(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f223,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X2,X0)
      | ~ r3_lattices(X1,X2,X0)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f222])).

fof(f222,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X2,X0)
      | ~ r3_lattices(X1,X2,X0)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f175,f70])).

fof(f175,plain,(
    ! [X2,X0,X1] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,X2)
      | ~ r3_lattices(X0,X1,X2)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ v10_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f174])).

fof(f174,plain,(
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
    inference(resolution,[],[f94,f71])).

fof(f94,plain,(
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
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f221,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_3
    | spl7_19
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f217,f194,f143,f219,f105,f157,f99])).

fof(f143,plain,
    ( spl7_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f194,plain,
    ( spl7_15
  <=> ! [X0] :
        ( k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | k2_lattices(sK0,sK2(sK0,X0),X0) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(duplicate_literal_removal,[],[f216])).

fof(f216,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | v13_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(resolution,[],[f215,f81])).

fof(f215,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 )
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(duplicate_literal_removal,[],[f212])).

fof(f212,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(superposition,[],[f195,f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f143])).

fof(f195,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,sK2(sK0,X0),X0) != X0
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f194])).

fof(f211,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_18
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f199,f105,f209,f157,f99])).

fof(f199,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK3(sK0) = k2_lattices(sK0,sK3(sK0),X2)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f192,f79])).

fof(f79,plain,(
    ! [X4,X0] :
      ( ~ v13_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | sK3(X0) = k2_lattices(X0,sK3(X0),X4)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f192,plain,
    ( v13_lattices(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f207,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_17
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f198,f105,f205,f157,f99])).

fof(f198,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | sK3(sK0) = k2_lattices(sK0,X1,sK3(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f192,f80])).

fof(f80,plain,(
    ! [X4,X0] :
      ( ~ v13_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | sK3(X0) = k2_lattices(X0,X4,sK3(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f203,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_16
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f197,f105,f201,f157,f99])).

fof(f197,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,sK1(sK0,X0),X0) != X0
        | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = X0
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f192,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v13_lattices(X0)
      | k2_lattices(X0,sK1(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK1(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k5_lattices(X0) = X1
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f196,plain,
    ( ~ spl7_4
    | spl7_3
    | spl7_15
    | spl7_1 ),
    inference(avatar_split_clause,[],[f191,f99,f194,f105,f108])).

fof(f191,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v13_lattices(sK0)
        | k2_lattices(sK0,sK2(sK0,X0),X0) != X0
        | ~ l3_lattices(sK0) )
    | spl7_1 ),
    inference(resolution,[],[f173,f122])).

fof(f122,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f173,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v13_lattices(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f82,f67])).

fof(f67,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ l1_lattices(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v13_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f169,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_13
    | spl7_11 ),
    inference(avatar_split_clause,[],[f168,f154,f160,f157,f99])).

fof(f154,plain,
    ( spl7_11
  <=> m1_subset_1(sK5(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f168,plain,
    ( v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_11 ),
    inference(resolution,[],[f155,f85])).

fof(f85,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),u1_struct_0(X0))
      | v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f54,f56,f55])).

fof(f55,plain,(
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

% (7594)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f56,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f155,plain,
    ( ~ m1_subset_1(sK5(sK0),u1_struct_0(sK0))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f167,plain,
    ( ~ spl7_4
    | spl7_12 ),
    inference(avatar_split_clause,[],[f166,f157,f108])).

fof(f166,plain,
    ( ~ l3_lattices(sK0)
    | spl7_12 ),
    inference(resolution,[],[f158,f67])).

fof(f158,plain,
    ( ~ l1_lattices(sK0)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f157])).

% (7592)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f165,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_13
    | spl7_10 ),
    inference(avatar_split_clause,[],[f164,f151,f160,f157,f99])).

fof(f151,plain,
    ( spl7_10
  <=> m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f164,plain,
    ( v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_10 ),
    inference(resolution,[],[f152,f84])).

% (7595)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
fof(f84,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f152,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f151])).

fof(f163,plain,
    ( ~ spl7_11
    | ~ spl7_10
    | spl7_1
    | ~ spl7_12
    | spl7_13
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f148,f143,f160,f157,f99,f151,f154])).

fof(f148,plain,
    ( v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0),u1_struct_0(sK0))
    | ~ spl7_9 ),
    inference(trivial_inequality_removal,[],[f147])).

fof(f147,plain,
    ( k2_lattices(sK0,sK4(sK0),sK5(sK0)) != k2_lattices(sK0,sK4(sK0),sK5(sK0))
    | v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0),u1_struct_0(sK0))
    | ~ spl7_9 ),
    inference(superposition,[],[f86,f144])).

fof(f86,plain,(
    ! [X0] :
      ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
      | v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f145,plain,
    ( ~ spl7_4
    | spl7_1
    | spl7_9
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f141,f102,f143,f99,f108])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f140,f120])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f139])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f138,f69])).

fof(f69,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f83,f67])).

fof(f83,plain,(
    ! [X4,X0,X3] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f134,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_8
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f130,f117,f132,f108,f102,f99])).

fof(f117,plain,
    ( spl7_6
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(sK0,X0,X1),X0)
        | ~ l3_lattices(sK0)
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f90,f118])).

fof(f118,plain,
    ( v4_lattice3(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ l3_lattices(X0)
      | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ( ! [X4] :
                ( ~ r2_hidden(X4,X2)
                | ~ r3_lattices(X0,sK6(X0,X1,X2),X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(sK6(X0,X1,X2),X1)
            & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f58])).

fof(f58,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r2_hidden(X4,X2)
              | ~ r3_lattices(X0,X3,X4)
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & r2_hidden(X3,X1)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ~ r2_hidden(X4,X2)
            | ~ r3_lattices(X0,sK6(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).

fof(f128,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_7
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f124,f117,f126,f108,f102,f99])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f87,f118])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
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
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).

fof(f123,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f61,f99])).

fof(f61,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f41])).

fof(f41,plain,
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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

fof(f121,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f62,f102])).

fof(f62,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f119,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f63,f117])).

fof(f63,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f115,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f64,f108])).

fof(f64,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f65,f111,f108,f105,f102,f99])).

fof(f65,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n018.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 20:57:12 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (7575)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (7575)Refutation not found, incomplete strategy% (7575)------------------------------
% 0.22/0.48  % (7575)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (7575)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (7575)Memory used [KB]: 6140
% 0.22/0.48  % (7575)Time elapsed: 0.061 s
% 0.22/0.48  % (7575)------------------------------
% 0.22/0.48  % (7575)------------------------------
% 0.22/0.48  % (7587)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.49  % (7581)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.49  % (7583)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (7587)Refutation not found, incomplete strategy% (7587)------------------------------
% 0.22/0.49  % (7587)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (7587)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (7587)Memory used [KB]: 6140
% 0.22/0.49  % (7587)Time elapsed: 0.002 s
% 0.22/0.49  % (7587)------------------------------
% 0.22/0.49  % (7587)------------------------------
% 0.22/0.49  % (7577)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.49  % (7580)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.49  % (7578)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (7582)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.50  % (7589)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (7576)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (7576)Refutation not found, incomplete strategy% (7576)------------------------------
% 0.22/0.50  % (7576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7576)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (7576)Memory used [KB]: 10618
% 0.22/0.50  % (7576)Time elapsed: 0.081 s
% 0.22/0.50  % (7576)------------------------------
% 0.22/0.50  % (7576)------------------------------
% 0.22/0.50  % (7579)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.50  % (7585)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (7590)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (7586)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (7588)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (7591)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.51  % (7593)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (7581)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f558,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f113,f115,f119,f121,f123,f128,f134,f145,f163,f165,f167,f169,f196,f203,f207,f211,f221,f229,f243,f245,f247,f261,f263,f278,f324,f336,f358,f392,f399,f420,f433,f447,f496,f518,f541,f548])).
% 0.22/0.51  fof(f548,plain,(
% 0.22/0.51    spl7_47 | ~spl7_50 | ~spl7_51 | spl7_57),
% 0.22/0.51    inference(avatar_split_clause,[],[f547,f538,f445,f431,f418])).
% 0.22/0.51  fof(f418,plain,(
% 0.22/0.51    spl7_47 <=> k5_lattices(sK0) = sK3(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 0.22/0.51  fof(f431,plain,(
% 0.22/0.51    spl7_50 <=> m1_subset_1(sK3(sK0),u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 0.22/0.51  fof(f445,plain,(
% 0.22/0.51    spl7_51 <=> ! [X1] : (sK3(sK0) = k2_lattices(sK0,sK1(sK0,X1),sK3(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = X1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 0.22/0.51  fof(f538,plain,(
% 0.22/0.51    spl7_57 <=> sK3(sK0) = k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_57])])).
% 0.22/0.51  fof(f547,plain,(
% 0.22/0.51    ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | k5_lattices(sK0) = sK3(sK0) | (~spl7_51 | spl7_57)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f544])).
% 0.22/0.51  fof(f544,plain,(
% 0.22/0.51    sK3(sK0) != sK3(sK0) | ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | k5_lattices(sK0) = sK3(sK0) | (~spl7_51 | spl7_57)),
% 0.22/0.51    inference(superposition,[],[f539,f446])).
% 0.22/0.51  fof(f446,plain,(
% 0.22/0.51    ( ! [X1] : (sK3(sK0) = k2_lattices(sK0,sK1(sK0,X1),sK3(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = X1) ) | ~spl7_51),
% 0.22/0.51    inference(avatar_component_clause,[],[f445])).
% 0.22/0.51  fof(f539,plain,(
% 0.22/0.51    sK3(sK0) != k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0)) | spl7_57),
% 0.22/0.51    inference(avatar_component_clause,[],[f538])).
% 0.22/0.51  fof(f541,plain,(
% 0.22/0.51    ~spl7_57 | ~spl7_50 | spl7_47 | ~spl7_16 | ~spl7_53),
% 0.22/0.51    inference(avatar_split_clause,[],[f536,f516,f201,f418,f431,f538])).
% 0.22/0.51  fof(f201,plain,(
% 0.22/0.51    spl7_16 <=> ! [X0] : (k2_lattices(sK0,sK1(sK0,X0),X0) != X0 | k5_lattices(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.22/0.51  fof(f516,plain,(
% 0.22/0.51    spl7_53 <=> sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 0.22/0.51  fof(f536,plain,(
% 0.22/0.51    k5_lattices(sK0) = sK3(sK0) | ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | sK3(sK0) != k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0)) | (~spl7_16 | ~spl7_53)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f532])).
% 0.22/0.51  fof(f532,plain,(
% 0.22/0.51    sK3(sK0) != sK3(sK0) | k5_lattices(sK0) = sK3(sK0) | ~m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | sK3(sK0) != k2_lattices(sK0,sK1(sK0,sK3(sK0)),sK3(sK0)) | (~spl7_16 | ~spl7_53)),
% 0.22/0.51    inference(superposition,[],[f202,f517])).
% 0.22/0.51  fof(f517,plain,(
% 0.22/0.51    sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0))) | ~spl7_53),
% 0.22/0.51    inference(avatar_component_clause,[],[f516])).
% 0.22/0.51  fof(f202,plain,(
% 0.22/0.51    ( ! [X0] : (k2_lattices(sK0,X0,sK1(sK0,X0)) != X0 | k5_lattices(sK0) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,sK1(sK0,X0),X0) != X0) ) | ~spl7_16),
% 0.22/0.51    inference(avatar_component_clause,[],[f201])).
% 0.22/0.51  fof(f518,plain,(
% 0.22/0.51    spl7_47 | spl7_53 | ~spl7_50 | ~spl7_52),
% 0.22/0.51    inference(avatar_split_clause,[],[f506,f494,f431,f516,f418])).
% 0.22/0.51  fof(f494,plain,(
% 0.22/0.51    spl7_52 <=> ! [X1] : (sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,X1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = X1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 0.22/0.51  fof(f506,plain,(
% 0.22/0.51    sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,sK3(sK0))) | k5_lattices(sK0) = sK3(sK0) | (~spl7_50 | ~spl7_52)),
% 0.22/0.51    inference(resolution,[],[f495,f432])).
% 0.22/0.51  fof(f432,plain,(
% 0.22/0.51    m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~spl7_50),
% 0.22/0.51    inference(avatar_component_clause,[],[f431])).
% 0.22/0.51  fof(f495,plain,(
% 0.22/0.51    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,X1)) | k5_lattices(sK0) = X1) ) | ~spl7_52),
% 0.22/0.51    inference(avatar_component_clause,[],[f494])).
% 0.22/0.51  fof(f496,plain,(
% 0.22/0.51    spl7_1 | ~spl7_12 | ~spl7_3 | spl7_52 | ~spl7_18),
% 0.22/0.51    inference(avatar_split_clause,[],[f487,f209,f494,f105,f157,f99])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    spl7_1 <=> v2_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.22/0.51  fof(f157,plain,(
% 0.22/0.51    spl7_12 <=> l1_lattices(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    spl7_3 <=> v13_lattices(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.22/0.51  fof(f209,plain,(
% 0.22/0.51    spl7_18 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK3(sK0) = k2_lattices(sK0,sK3(sK0),X2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.22/0.51  fof(f487,plain,(
% 0.22/0.51    ( ! [X1] : (sK3(sK0) = k2_lattices(sK0,sK3(sK0),sK1(sK0,X1)) | k5_lattices(sK0) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_18),
% 0.22/0.51    inference(resolution,[],[f210,f76])).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) | k5_lattices(X0) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f47])).
% 0.22/0.51  fof(f47,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f45,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(rectify,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK3(sK0) = k2_lattices(sK0,sK3(sK0),X2)) ) | ~spl7_18),
% 0.22/0.51    inference(avatar_component_clause,[],[f209])).
% 0.22/0.51  fof(f447,plain,(
% 0.22/0.51    spl7_1 | ~spl7_12 | ~spl7_3 | spl7_51 | ~spl7_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f438,f205,f445,f105,f157,f99])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    spl7_17 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | sK3(sK0) = k2_lattices(sK0,X1,sK3(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 0.22/0.51  fof(f438,plain,(
% 0.22/0.51    ( ! [X1] : (sK3(sK0) = k2_lattices(sK0,sK1(sK0,X1),sK3(sK0)) | k5_lattices(sK0) = X1 | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_17),
% 0.22/0.51    inference(resolution,[],[f206,f76])).
% 0.22/0.51  fof(f206,plain,(
% 0.22/0.51    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | sK3(sK0) = k2_lattices(sK0,X1,sK3(sK0))) ) | ~spl7_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f205])).
% 0.22/0.51  fof(f433,plain,(
% 0.22/0.51    spl7_1 | ~spl7_4 | spl7_50 | ~spl7_45),
% 0.22/0.51    inference(avatar_split_clause,[],[f416,f397,f431,f108,f99])).
% 0.22/0.51  fof(f108,plain,(
% 0.22/0.51    spl7_4 <=> l3_lattices(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.22/0.51  fof(f397,plain,(
% 0.22/0.51    spl7_45 <=> k15_lattice3(sK0,k1_xboole_0) = sK3(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 0.22/0.51  fof(f416,plain,(
% 0.22/0.51    m1_subset_1(sK3(sK0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0) | ~spl7_45),
% 0.22/0.51    inference(superposition,[],[f92,f398])).
% 0.22/0.51  fof(f398,plain,(
% 0.22/0.51    k15_lattice3(sK0,k1_xboole_0) = sK3(sK0) | ~spl7_45),
% 0.22/0.51    inference(avatar_component_clause,[],[f397])).
% 0.22/0.51  fof(f92,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f37])).
% 0.22/0.51  fof(f37,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 0.22/0.51  fof(f420,plain,(
% 0.22/0.51    ~spl7_47 | spl7_5 | ~spl7_45),
% 0.22/0.51    inference(avatar_split_clause,[],[f406,f397,f111,f418])).
% 0.22/0.51  fof(f111,plain,(
% 0.22/0.51    spl7_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.22/0.51  fof(f406,plain,(
% 0.22/0.51    k5_lattices(sK0) != sK3(sK0) | (spl7_5 | ~spl7_45)),
% 0.22/0.51    inference(superposition,[],[f112,f398])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl7_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f111])).
% 0.22/0.51  fof(f399,plain,(
% 0.22/0.51    spl7_45 | ~spl7_37 | ~spl7_39),
% 0.22/0.51    inference(avatar_split_clause,[],[f395,f356,f334,f397])).
% 0.22/0.51  fof(f334,plain,(
% 0.22/0.51    spl7_37 <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).
% 0.22/0.51  fof(f356,plain,(
% 0.22/0.51    spl7_39 <=> ! [X0] : sK3(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_39])])).
% 0.22/0.51  fof(f395,plain,(
% 0.22/0.51    k15_lattice3(sK0,k1_xboole_0) = sK3(sK0) | (~spl7_37 | ~spl7_39)),
% 0.22/0.51    inference(forward_demodulation,[],[f335,f357])).
% 0.22/0.51  fof(f357,plain,(
% 0.22/0.51    ( ! [X0] : (sK3(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0))) ) | ~spl7_39),
% 0.22/0.51    inference(avatar_component_clause,[],[f356])).
% 0.22/0.51  fof(f335,plain,(
% 0.22/0.51    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0)) | ~spl7_37),
% 0.22/0.51    inference(avatar_component_clause,[],[f334])).
% 0.22/0.51  fof(f392,plain,(
% 0.22/0.51    ~spl7_24 | ~spl7_19 | ~spl7_34),
% 0.22/0.51    inference(avatar_split_clause,[],[f391,f322,f219,f252])).
% 0.22/0.51  fof(f252,plain,(
% 0.22/0.51    spl7_24 <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    spl7_19 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 0.22/0.51  fof(f322,plain,(
% 0.22/0.51    spl7_34 <=> ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).
% 0.22/0.51  fof(f391,plain,(
% 0.22/0.51    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (~spl7_19 | ~spl7_34)),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f387])).
% 0.22/0.51  fof(f387,plain,(
% 0.22/0.51    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (~spl7_19 | ~spl7_34)),
% 0.22/0.51    inference(superposition,[],[f220,f323])).
% 0.22/0.51  fof(f323,plain,(
% 0.22/0.51    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X0)))) ) | ~spl7_34),
% 0.22/0.51    inference(avatar_component_clause,[],[f322])).
% 0.22/0.51  fof(f220,plain,(
% 0.22/0.51    ( ! [X0] : (k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f219])).
% 0.22/0.51  fof(f358,plain,(
% 0.22/0.51    spl7_1 | ~spl7_4 | spl7_39 | ~spl7_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f348,f205,f356,f108,f99])).
% 0.22/0.51  fof(f348,plain,(
% 0.22/0.51    ( ! [X0] : (sK3(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK3(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_17),
% 0.22/0.51    inference(resolution,[],[f206,f92])).
% 0.22/0.51  fof(f336,plain,(
% 0.22/0.51    spl7_1 | ~spl7_12 | ~spl7_3 | spl7_37 | ~spl7_26),
% 0.22/0.51    inference(avatar_split_clause,[],[f267,f259,f334,f105,f157,f99])).
% 0.22/0.51  fof(f259,plain,(
% 0.22/0.51    spl7_26 <=> ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_26])])).
% 0.22/0.51  fof(f267,plain,(
% 0.22/0.51    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl7_26),
% 0.22/0.51    inference(resolution,[],[f260,f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(sK3(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f52])).
% 0.22/0.51  fof(f52,plain,(
% 0.22/0.51    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f49,f51,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(rectify,[],[f48])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 0.22/0.51  fof(f260,plain,(
% 0.22/0.51    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)) ) | ~spl7_26),
% 0.22/0.51    inference(avatar_component_clause,[],[f259])).
% 0.22/0.51  fof(f324,plain,(
% 0.22/0.51    spl7_1 | ~spl7_4 | spl7_34 | ~spl7_28),
% 0.22/0.51    inference(avatar_split_clause,[],[f314,f276,f322,f108,f99])).
% 0.22/0.51  fof(f276,plain,(
% 0.22/0.51    spl7_28 <=> ! [X2] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 0.22/0.51  fof(f314,plain,(
% 0.22/0.51    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,k15_lattice3(sK0,X0))) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_28),
% 0.22/0.51    inference(resolution,[],[f277,f92])).
% 0.22/0.51  fof(f277,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2))) ) | ~spl7_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f276])).
% 0.22/0.51  fof(f278,plain,(
% 0.22/0.51    spl7_1 | ~spl7_12 | spl7_3 | spl7_28 | ~spl7_26),
% 0.22/0.51    inference(avatar_split_clause,[],[f266,f259,f276,f105,f157,f99])).
% 0.22/0.51  fof(f266,plain,(
% 0.22/0.51    ( ! [X2] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2)) | v13_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_26),
% 0.22/0.51    inference(resolution,[],[f260,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f52])).
% 0.22/0.51  fof(f263,plain,(
% 0.22/0.51    spl7_1 | ~spl7_4 | spl7_24),
% 0.22/0.51    inference(avatar_split_clause,[],[f262,f252,f108,f99])).
% 0.22/0.51  fof(f262,plain,(
% 0.22/0.51    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl7_24),
% 0.22/0.51    inference(resolution,[],[f253,f92])).
% 0.22/0.51  fof(f253,plain,(
% 0.22/0.51    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | spl7_24),
% 0.22/0.51    inference(avatar_component_clause,[],[f252])).
% 0.22/0.51  fof(f261,plain,(
% 0.22/0.51    ~spl7_24 | spl7_26 | ~spl7_7 | ~spl7_8 | ~spl7_23),
% 0.22/0.51    inference(avatar_split_clause,[],[f250,f241,f132,f126,f259,f252])).
% 0.22/0.51  fof(f126,plain,(
% 0.22/0.51    spl7_7 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.22/0.51  fof(f132,plain,(
% 0.22/0.51    spl7_8 <=> ! [X1,X0] : (r2_hidden(sK6(sK0,X0,X1),X0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.22/0.51  fof(f241,plain,(
% 0.22/0.51    spl7_23 <=> ! [X3,X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.22/0.51  fof(f250,plain,(
% 0.22/0.51    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl7_7 | ~spl7_8 | ~spl7_23)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f249])).
% 0.22/0.51  fof(f249,plain,(
% 0.22/0.51    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl7_7 | ~spl7_8 | ~spl7_23)),
% 0.22/0.51    inference(resolution,[],[f242,f137])).
% 0.22/0.51  fof(f137,plain,(
% 0.22/0.51    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl7_7 | ~spl7_8)),
% 0.22/0.51    inference(superposition,[],[f136,f127])).
% 0.22/0.51  fof(f127,plain,(
% 0.22/0.51    ( ! [X0] : (k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_7),
% 0.22/0.51    inference(avatar_component_clause,[],[f126])).
% 0.22/0.51  fof(f136,plain,(
% 0.22/0.51    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | ~spl7_8),
% 0.22/0.51    inference(resolution,[],[f135,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.51  fof(f135,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,sK6(sK0,X0,X1)) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))) ) | ~spl7_8),
% 0.22/0.51    inference(resolution,[],[f133,f93])).
% 0.22/0.51  fof(f93,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.51  fof(f133,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,X1),X0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))) ) | ~spl7_8),
% 0.22/0.51    inference(avatar_component_clause,[],[f132])).
% 0.22/0.51  fof(f242,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~r3_lattices(sK0,X3,X2) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl7_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f241])).
% 0.22/0.51  fof(f247,plain,(
% 0.22/0.51    ~spl7_4 | spl7_1 | ~spl7_2 | spl7_22),
% 0.22/0.51    inference(avatar_split_clause,[],[f246,f238,f102,f99,f108])).
% 0.22/0.51  fof(f102,plain,(
% 0.22/0.51    spl7_2 <=> v10_lattices(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.22/0.51  fof(f238,plain,(
% 0.22/0.51    spl7_22 <=> v9_lattices(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.22/0.51  fof(f246,plain,(
% 0.22/0.51    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl7_22),
% 0.22/0.51    inference(resolution,[],[f239,f71])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f16])).
% 0.22/0.51  fof(f16,plain,(
% 0.22/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.22/0.51  fof(f239,plain,(
% 0.22/0.51    ~v9_lattices(sK0) | spl7_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f238])).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    ~spl7_4 | spl7_1 | ~spl7_2 | spl7_21),
% 0.22/0.51    inference(avatar_split_clause,[],[f244,f235,f102,f99,f108])).
% 0.22/0.51  fof(f235,plain,(
% 0.22/0.51    spl7_21 <=> v8_lattices(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl7_21),
% 0.22/0.51    inference(resolution,[],[f236,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f236,plain,(
% 0.22/0.51    ~v8_lattices(sK0) | spl7_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f235])).
% 0.22/0.51  fof(f243,plain,(
% 0.22/0.51    spl7_1 | ~spl7_21 | ~spl7_22 | ~spl7_4 | spl7_23 | ~spl7_20),
% 0.22/0.51    inference(avatar_split_clause,[],[f232,f227,f241,f108,f238,f235,f99])).
% 0.22/0.51  fof(f227,plain,(
% 0.22/0.51    spl7_20 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | r1_lattices(sK0,X0,X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.22/0.51  fof(f232,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_20),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f231])).
% 0.22/0.51  fof(f231,plain,(
% 0.22/0.51    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_20),
% 0.22/0.51    inference(resolution,[],[f228,f72])).
% 0.22/0.51  fof(f72,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) = X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f7])).
% 0.22/0.51  fof(f7,axiom,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 0.22/0.51  fof(f228,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f227])).
% 0.22/0.51  fof(f229,plain,(
% 0.22/0.51    spl7_1 | ~spl7_13 | ~spl7_4 | spl7_20 | ~spl7_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f224,f102,f227,f108,f160,f99])).
% 0.22/0.51  fof(f160,plain,(
% 0.22/0.51    spl7_13 <=> v6_lattices(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.22/0.51  fof(f224,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,X0,X1) | ~r3_lattices(sK0,X0,X1) | ~v6_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_2),
% 0.22/0.51    inference(resolution,[],[f223,f120])).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    v10_lattices(sK0) | ~spl7_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f102])).
% 0.22/0.51  fof(f223,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X2,X0) | ~r3_lattices(X1,X2,X0) | ~v6_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f222])).
% 0.22/0.51  fof(f222,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X2,X0) | ~r3_lattices(X1,X2,X0) | ~v6_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.22/0.51    inference(resolution,[],[f175,f70])).
% 0.22/0.51  fof(f175,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v8_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f174])).
% 0.22/0.51  fof(f174,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.22/0.51    inference(resolution,[],[f94,f71])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f60])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f40])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f39])).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f6])).
% 0.22/0.51  fof(f6,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.22/0.51  fof(f221,plain,(
% 0.22/0.51    spl7_1 | ~spl7_12 | spl7_3 | spl7_19 | ~spl7_9 | ~spl7_15),
% 0.22/0.51    inference(avatar_split_clause,[],[f217,f194,f143,f219,f105,f157,f99])).
% 0.22/0.51  fof(f143,plain,(
% 0.22/0.51    spl7_9 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.22/0.51  fof(f194,plain,(
% 0.22/0.51    spl7_15 <=> ! [X0] : (k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | k2_lattices(sK0,sK2(sK0,X0),X0) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl7_9 | ~spl7_15)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f216])).
% 0.22/0.51  fof(f216,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | v13_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl7_9 | ~spl7_15)),
% 0.22/0.51    inference(resolution,[],[f215,f81])).
% 0.22/0.51  fof(f215,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0) ) | (~spl7_9 | ~spl7_15)),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f212])).
% 0.22/0.51  fof(f212,plain,(
% 0.22/0.51    ( ! [X0] : (k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0))) ) | (~spl7_9 | ~spl7_15)),
% 0.22/0.51    inference(superposition,[],[f195,f144])).
% 0.22/0.51  fof(f144,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_9),
% 0.22/0.51    inference(avatar_component_clause,[],[f143])).
% 0.22/0.51  fof(f195,plain,(
% 0.22/0.51    ( ! [X0] : (k2_lattices(sK0,sK2(sK0,X0),X0) != X0 | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_15),
% 0.22/0.51    inference(avatar_component_clause,[],[f194])).
% 0.22/0.51  fof(f211,plain,(
% 0.22/0.51    spl7_1 | ~spl7_12 | spl7_18 | ~spl7_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f199,f105,f209,f157,f99])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK3(sK0) = k2_lattices(sK0,sK3(sK0),X2) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_3),
% 0.22/0.51    inference(resolution,[],[f192,f79])).
% 0.22/0.51  fof(f79,plain,(
% 0.22/0.51    ( ! [X4,X0] : (~v13_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | sK3(X0) = k2_lattices(X0,sK3(X0),X4) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f52])).
% 0.22/0.51  fof(f192,plain,(
% 0.22/0.51    v13_lattices(sK0) | ~spl7_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f105])).
% 0.22/0.51  fof(f207,plain,(
% 0.22/0.51    spl7_1 | ~spl7_12 | spl7_17 | ~spl7_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f198,f105,f205,f157,f99])).
% 0.22/0.51  fof(f198,plain,(
% 0.22/0.51    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | sK3(sK0) = k2_lattices(sK0,X1,sK3(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_3),
% 0.22/0.51    inference(resolution,[],[f192,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X4,X0] : (~v13_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | sK3(X0) = k2_lattices(X0,X4,sK3(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f52])).
% 0.22/0.51  fof(f203,plain,(
% 0.22/0.51    spl7_1 | ~spl7_12 | spl7_16 | ~spl7_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f197,f105,f201,f157,f99])).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    ( ! [X0] : (k2_lattices(sK0,sK1(sK0,X0),X0) != X0 | k2_lattices(sK0,X0,sK1(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = X0 | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_3),
% 0.22/0.51    inference(resolution,[],[f192,f77])).
% 0.22/0.51  fof(f77,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v13_lattices(X0) | k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | k5_lattices(X0) = X1 | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f47])).
% 0.22/0.51  fof(f196,plain,(
% 0.22/0.51    ~spl7_4 | spl7_3 | spl7_15 | spl7_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f191,f99,f194,f105,f108])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    ( ! [X0] : (k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v13_lattices(sK0) | k2_lattices(sK0,sK2(sK0,X0),X0) != X0 | ~l3_lattices(sK0)) ) | spl7_1),
% 0.22/0.51    inference(resolution,[],[f173,f122])).
% 0.22/0.51  fof(f122,plain,(
% 0.22/0.51    ~v2_struct_0(sK0) | spl7_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f99])).
% 0.22/0.51  fof(f173,plain,(
% 0.22/0.51    ( ! [X0,X1] : (v2_struct_0(X0) | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | v13_lattices(X0) | k2_lattices(X0,sK2(X0,X1),X1) != X1 | ~l3_lattices(X0)) )),
% 0.22/0.51    inference(resolution,[],[f82,f67])).
% 0.22/0.51  fof(f67,plain,(
% 0.22/0.51    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f21])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 0.22/0.51    inference(pure_predicate_removal,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~l1_lattices(X0) | k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | v13_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f52])).
% 0.22/0.51  fof(f169,plain,(
% 0.22/0.51    spl7_1 | ~spl7_12 | spl7_13 | spl7_11),
% 0.22/0.51    inference(avatar_split_clause,[],[f168,f154,f160,f157,f99])).
% 0.22/0.51  fof(f154,plain,(
% 0.22/0.51    spl7_11 <=> m1_subset_1(sK5(sK0),u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.22/0.51  fof(f168,plain,(
% 0.22/0.51    v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | spl7_11),
% 0.22/0.51    inference(resolution,[],[f155,f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(sK5(X0),u1_struct_0(X0)) | v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f54,f56,f55])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  % (7594)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f54,plain,(
% 0.22/0.51    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(rectify,[],[f53])).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f31])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 0.22/0.51  fof(f155,plain,(
% 0.22/0.51    ~m1_subset_1(sK5(sK0),u1_struct_0(sK0)) | spl7_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f154])).
% 0.22/0.51  fof(f167,plain,(
% 0.22/0.51    ~spl7_4 | spl7_12),
% 0.22/0.51    inference(avatar_split_clause,[],[f166,f157,f108])).
% 0.22/0.51  fof(f166,plain,(
% 0.22/0.51    ~l3_lattices(sK0) | spl7_12),
% 0.22/0.51    inference(resolution,[],[f158,f67])).
% 0.22/0.51  fof(f158,plain,(
% 0.22/0.51    ~l1_lattices(sK0) | spl7_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f157])).
% 0.22/0.51  % (7592)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  fof(f165,plain,(
% 0.22/0.51    spl7_1 | ~spl7_12 | spl7_13 | spl7_10),
% 0.22/0.51    inference(avatar_split_clause,[],[f164,f151,f160,f157,f99])).
% 0.22/0.51  fof(f151,plain,(
% 0.22/0.51    spl7_10 <=> m1_subset_1(sK4(sK0),u1_struct_0(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.22/0.51  fof(f164,plain,(
% 0.22/0.51    v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | spl7_10),
% 0.22/0.51    inference(resolution,[],[f152,f84])).
% 0.22/0.51  % (7595)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.51  fof(f84,plain,(
% 0.22/0.51    ( ! [X0] : (m1_subset_1(sK4(X0),u1_struct_0(X0)) | v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f57])).
% 0.22/0.51  fof(f152,plain,(
% 0.22/0.51    ~m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | spl7_10),
% 0.22/0.51    inference(avatar_component_clause,[],[f151])).
% 0.22/0.51  fof(f163,plain,(
% 0.22/0.51    ~spl7_11 | ~spl7_10 | spl7_1 | ~spl7_12 | spl7_13 | ~spl7_9),
% 0.22/0.51    inference(avatar_split_clause,[],[f148,f143,f160,f157,f99,f151,f154])).
% 0.22/0.51  fof(f148,plain,(
% 0.22/0.51    v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0),u1_struct_0(sK0)) | ~spl7_9),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f147])).
% 0.22/0.51  fof(f147,plain,(
% 0.22/0.51    k2_lattices(sK0,sK4(sK0),sK5(sK0)) != k2_lattices(sK0,sK4(sK0),sK5(sK0)) | v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0),u1_struct_0(sK0)) | ~spl7_9),
% 0.22/0.51    inference(superposition,[],[f86,f144])).
% 0.22/0.51  fof(f86,plain,(
% 0.22/0.51    ( ! [X0] : (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) | v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f57])).
% 0.22/0.51  fof(f145,plain,(
% 0.22/0.51    ~spl7_4 | spl7_1 | spl7_9 | ~spl7_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f141,f102,f143,f99,f108])).
% 0.22/0.51  fof(f141,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_2),
% 0.22/0.51    inference(resolution,[],[f140,f120])).
% 0.22/0.51  fof(f140,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f139])).
% 0.22/0.51  fof(f139,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.22/0.51    inference(resolution,[],[f138,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f138,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v6_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.22/0.51    inference(resolution,[],[f83,f67])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    ( ! [X4,X0,X3] : (~l1_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f57])).
% 0.22/0.51  fof(f134,plain,(
% 0.22/0.51    spl7_1 | ~spl7_2 | ~spl7_4 | spl7_8 | ~spl7_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f130,f117,f132,f108,f102,f99])).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    spl7_6 <=> v4_lattice3(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.22/0.51  fof(f130,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,X1),X0) | ~l3_lattices(sK0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_6),
% 0.22/0.51    inference(resolution,[],[f90,f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    v4_lattice3(sK0) | ~spl7_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f117])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | r2_hidden(sK6(X0,X1,X2),X1) | ~l3_lattices(X0) | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f59])).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK6(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f35,f58])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK6(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).
% 0.22/0.51  fof(f128,plain,(
% 0.22/0.51    spl7_1 | ~spl7_2 | ~spl7_4 | spl7_7 | ~spl7_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f124,f117,f126,f108,f102,f99])).
% 0.22/0.51  fof(f124,plain,(
% 0.22/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_6),
% 0.22/0.51    inference(resolution,[],[f87,f118])).
% 0.22/0.51  fof(f87,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v4_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).
% 0.22/0.51  fof(f123,plain,(
% 0.22/0.51    ~spl7_1),
% 0.22/0.51    inference(avatar_split_clause,[],[f61,f99])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ~v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,negated_conjecture,(
% 0.22/0.51    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    inference(negated_conjecture,[],[f13])).
% 0.22/0.51  fof(f13,conjecture,(
% 0.22/0.51    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    spl7_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f62,f102])).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    v10_lattices(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    spl7_6),
% 0.22/0.51    inference(avatar_split_clause,[],[f63,f117])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    v4_lattice3(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    spl7_4),
% 0.22/0.51    inference(avatar_split_clause,[],[f64,f108])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    l3_lattices(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f65,f111,f108,f105,f102,f99])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (7581)------------------------------
% 0.22/0.51  % (7581)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (7581)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (7581)Memory used [KB]: 11001
% 0.22/0.51  % (7581)Time elapsed: 0.084 s
% 0.22/0.51  % (7581)------------------------------
% 0.22/0.51  % (7581)------------------------------
% 0.22/0.52  % (7574)Success in time 0.153 s
%------------------------------------------------------------------------------
