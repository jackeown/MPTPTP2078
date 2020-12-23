%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  225 ( 491 expanded)
%              Number of leaves         :   51 ( 216 expanded)
%              Depth                    :   13
%              Number of atoms          : 1123 (2473 expanded)
%              Number of equality atoms :  164 ( 403 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f589,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f119,f123,f125,f127,f134,f140,f151,f169,f171,f173,f175,f202,f210,f218,f232,f240,f254,f256,f258,f272,f274,f299,f380,f392,f453,f457,f501,f508,f542,f588])).

fof(f588,plain,
    ( spl7_1
    | ~ spl7_12
    | ~ spl7_3
    | spl7_64
    | ~ spl7_16
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f586,f451,f208,f540,f109,f163,f103])).

fof(f103,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f163,plain,
    ( spl7_12
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f109,plain,
    ( spl7_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f540,plain,
    ( spl7_64
  <=> k5_lattices(sK0) = sK4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f208,plain,
    ( spl7_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f451,plain,
    ( spl7_52
  <=> sK4(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f586,plain,
    ( k5_lattices(sK0) = sK4(sK0)
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_16
    | ~ spl7_52 ),
    inference(forward_demodulation,[],[f575,f452])).

fof(f452,plain,
    ( sK4(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f451])).

fof(f575,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0))
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_16 ),
    inference(resolution,[],[f209,f87])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( ( v13_lattices(X0)
          | ! [X1] :
              ( ( ( k2_lattices(X0,sK3(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK3(X0,X1)) != X1 )
                & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ( ! [X4] :
                ( ( sK4(X0) = k2_lattices(X0,X4,sK4(X0))
                  & sK4(X0) = k2_lattices(X0,sK4(X0),X4) )
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & m1_subset_1(sK4(X0),u1_struct_0(X0)) )
          | ~ v13_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK3(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK3(X0,X1)) != X1 )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( ( k2_lattices(X0,X4,X3) = X3
                & k2_lattices(X0,X3,X4) = X3 )
              | ~ m1_subset_1(X4,u1_struct_0(X0)) )
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( ! [X4] :
            ( ( sK4(X0) = k2_lattices(X0,X4,sK4(X0))
              & sK4(X0) = k2_lattices(X0,sK4(X0),X4) )
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f209,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f208])).

fof(f542,plain,
    ( ~ spl7_64
    | spl7_5
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f524,f506,f115,f540])).

fof(f115,plain,
    ( spl7_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f506,plain,
    ( spl7_60
  <=> k15_lattice3(sK0,k1_xboole_0) = sK4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f524,plain,
    ( k5_lattices(sK0) != sK4(sK0)
    | spl7_5
    | ~ spl7_60 ),
    inference(superposition,[],[f116,f507])).

fof(f507,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = sK4(sK0)
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f506])).

fof(f116,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f508,plain,
    ( spl7_60
    | ~ spl7_43
    | ~ spl7_53 ),
    inference(avatar_split_clause,[],[f504,f455,f390,f506])).

fof(f390,plain,
    ( spl7_43
  <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f455,plain,
    ( spl7_53
  <=> ! [X0] : sK4(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f504,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = sK4(sK0)
    | ~ spl7_43
    | ~ spl7_53 ),
    inference(forward_demodulation,[],[f391,f456])).

fof(f456,plain,
    ( ! [X0] : sK4(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK4(sK0))
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f455])).

fof(f391,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK4(sK0))
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f390])).

fof(f501,plain,
    ( ~ spl7_25
    | ~ spl7_20
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f500,f378,f230,f263])).

fof(f263,plain,
    ( spl7_25
  <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f230,plain,
    ( spl7_20
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f378,plain,
    ( spl7_40
  <=> ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f500,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl7_20
    | ~ spl7_40 ),
    inference(trivial_inequality_removal,[],[f496])).

fof(f496,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl7_20
    | ~ spl7_40 ),
    inference(superposition,[],[f231,f379])).

fof(f379,plain,
    ( ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0)))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f378])).

fof(f231,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f230])).

fof(f457,plain,
    ( spl7_1
    | ~ spl7_4
    | spl7_53
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f443,f216,f455,f112,f103])).

fof(f112,plain,
    ( spl7_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f216,plain,
    ( spl7_18
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK4(sK0) = k2_lattices(sK0,X2,sK4(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f443,plain,
    ( ! [X0] :
        ( sK4(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK4(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_18 ),
    inference(resolution,[],[f217,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f217,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK4(sK0) = k2_lattices(sK0,X2,sK4(sK0)) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f216])).

fof(f453,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_52
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f442,f216,f451,f163,f103])).

fof(f442,plain,
    ( sK4(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_18 ),
    inference(resolution,[],[f217,f82])).

fof(f82,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f392,plain,
    ( spl7_1
    | ~ spl7_12
    | ~ spl7_3
    | spl7_43
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f280,f270,f390,f109,f163,f103])).

fof(f270,plain,
    ( spl7_27
  <=> ! [X1] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f280,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK4(sK0))
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_27 ),
    inference(resolution,[],[f271,f87])).

fof(f271,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f270])).

fof(f380,plain,
    ( spl7_1
    | ~ spl7_4
    | spl7_40
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f366,f297,f378,f112,f103])).

fof(f297,plain,
    ( spl7_31
  <=> ! [X4] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f366,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0)))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_31 ),
    inference(resolution,[],[f298,f96])).

fof(f298,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X4)) )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f297])).

fof(f299,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_3
    | spl7_31
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f279,f270,f297,f109,f163,f103])).

fof(f279,plain,
    ( ! [X4] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X4))
        | v13_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_27 ),
    inference(resolution,[],[f271,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f274,plain,
    ( spl7_1
    | ~ spl7_4
    | spl7_25 ),
    inference(avatar_split_clause,[],[f273,f263,f112,f103])).

fof(f273,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_25 ),
    inference(resolution,[],[f264,f96])).

fof(f264,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f263])).

fof(f272,plain,
    ( ~ spl7_25
    | spl7_27
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f261,f252,f138,f132,f270,f263])).

fof(f132,plain,
    ( spl7_7
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f138,plain,
    ( spl7_8
  <=> ! [X1,X0] :
        ( r2_hidden(sK1(sK0,X0,X1),X0)
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f252,plain,
    ( spl7_24
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X2) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f261,plain,
    ( ! [X1] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_24 ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,
    ( ! [X1] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_24 ),
    inference(resolution,[],[f253,f143])).

fof(f143,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(superposition,[],[f142,f133])).

fof(f133,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f132])).

fof(f142,plain,
    ( ! [X0] : r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | ~ spl7_8 ),
    inference(resolution,[],[f141,f69])).

fof(f69,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,sK1(sK0,X0,X1))
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) )
    | ~ spl7_8 ),
    inference(resolution,[],[f139,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f139,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(sK0,X0,X1),X0)
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f138])).

fof(f253,plain,
    ( ! [X2,X3] :
        ( ~ r3_lattices(sK0,X3,X2)
        | k2_lattices(sK0,X3,X2) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f252])).

fof(f258,plain,
    ( ~ spl7_4
    | spl7_1
    | ~ spl7_2
    | spl7_23 ),
    inference(avatar_split_clause,[],[f257,f249,f106,f103,f112])).

fof(f106,plain,
    ( spl7_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f249,plain,
    ( spl7_23
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f257,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl7_23 ),
    inference(resolution,[],[f250,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
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

fof(f250,plain,
    ( ~ v9_lattices(sK0)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f249])).

fof(f256,plain,
    ( ~ spl7_4
    | spl7_1
    | ~ spl7_2
    | spl7_22 ),
    inference(avatar_split_clause,[],[f255,f246,f106,f103,f112])).

fof(f246,plain,
    ( spl7_22
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f255,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl7_22 ),
    inference(resolution,[],[f247,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f247,plain,
    ( ~ v8_lattices(sK0)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f246])).

fof(f254,plain,
    ( spl7_1
    | ~ spl7_22
    | ~ spl7_23
    | ~ spl7_4
    | spl7_24
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f243,f238,f252,f112,f249,f246,f103])).

fof(f238,plain,
    ( spl7_21
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1)
        | r1_lattices(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f243,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X2) = X3
        | ~ l3_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ v8_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_21 ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,
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
    | ~ spl7_21 ),
    inference(resolution,[],[f239,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(f239,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f238])).

fof(f240,plain,
    ( spl7_1
    | ~ spl7_13
    | ~ spl7_4
    | spl7_21
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f235,f106,f238,f112,f166,f103])).

fof(f166,plain,
    ( spl7_13
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f235,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r1_lattices(sK0,X0,X1)
        | ~ r3_lattices(sK0,X0,X1)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f234,f124])).

fof(f124,plain,
    ( v10_lattices(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f106])).

fof(f234,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X2,X0)
      | ~ r3_lattices(X1,X2,X0)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f233])).

fof(f233,plain,(
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
    inference(resolution,[],[f181,f73])).

fof(f181,plain,(
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
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,(
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
    inference(resolution,[],[f98,f74])).

fof(f98,plain,(
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
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f232,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_3
    | spl7_20
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f228,f200,f149,f230,f109,f163,f103])).

fof(f149,plain,
    ( spl7_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f200,plain,
    ( spl7_15
  <=> ! [X0] :
        ( k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | k2_lattices(sK0,sK3(sK0,X0),X0) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f228,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(duplicate_literal_removal,[],[f227])).

fof(f227,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | v13_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(resolution,[],[f226,f90])).

fof(f226,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 )
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(duplicate_literal_removal,[],[f223])).

fof(f223,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(superposition,[],[f201,f150])).

fof(f150,plain,
    ( ! [X0,X1] :
        ( k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f149])).

fof(f201,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,sK3(sK0,X0),X0) != X0
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f200])).

fof(f218,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_18
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f205,f109,f216,f163,f103])).

fof(f205,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK4(sK0) = k2_lattices(sK0,X2,sK4(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f198,f89])).

fof(f89,plain,(
    ! [X4,X0] :
      ( ~ v13_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | sK4(X0) = k2_lattices(X0,X4,sK4(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f198,plain,
    ( v13_lattices(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f109])).

fof(f210,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_16
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f203,f109,f208,f163,f103])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f198,f129])).

fof(f129,plain,(
    ! [X0,X3] :
      ( ~ v13_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f82,f101])).

fof(f101,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

% (24461)Refutation not found, incomplete strategy% (24461)------------------------------
% (24461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24461)Termination reason: Refutation not found, incomplete strategy

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f34])).

% (24461)Memory used [KB]: 10618
% (24461)Time elapsed: 0.082 s
% (24461)------------------------------
% (24461)------------------------------
fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f202,plain,
    ( ~ spl7_4
    | spl7_3
    | spl7_15
    | spl7_1 ),
    inference(avatar_split_clause,[],[f197,f103,f200,f109,f112])).

fof(f197,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v13_lattices(sK0)
        | k2_lattices(sK0,sK3(sK0,X0),X0) != X0
        | ~ l3_lattices(sK0) )
    | spl7_1 ),
    inference(resolution,[],[f179,f126])).

fof(f126,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f103])).

fof(f179,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | k2_lattices(X0,X1,sK3(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v13_lattices(X0)
      | k2_lattices(X0,sK3(X0,X1),X1) != X1
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f91,f70])).

fof(f70,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ l1_lattices(X0)
      | k2_lattices(X0,sK3(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK3(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v13_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f175,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_13
    | spl7_11 ),
    inference(avatar_split_clause,[],[f174,f160,f166,f163,f103])).

fof(f160,plain,
    ( spl7_11
  <=> m1_subset_1(sK6(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f174,plain,
    ( v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_11 ),
    inference(resolution,[],[f161,f94])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0),u1_struct_0(X0))
      | v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0] :
      ( ( ( v6_lattices(X0)
          | ( k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0))
            & m1_subset_1(sK6(X0),u1_struct_0(X0))
            & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v6_lattices(X0) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f59,f61,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1)
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k2_lattices(X0,sK5(X0),X2) != k2_lattices(X0,X2,sK5(X0))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK5(X0),X2) != k2_lattices(X0,X2,sK5(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).

fof(f161,plain,
    ( ~ m1_subset_1(sK6(sK0),u1_struct_0(sK0))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f160])).

fof(f173,plain,
    ( ~ spl7_4
    | spl7_12 ),
    inference(avatar_split_clause,[],[f172,f163,f112])).

fof(f172,plain,
    ( ~ l3_lattices(sK0)
    | spl7_12 ),
    inference(resolution,[],[f164,f70])).

fof(f164,plain,
    ( ~ l1_lattices(sK0)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f163])).

fof(f171,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_13
    | spl7_10 ),
    inference(avatar_split_clause,[],[f170,f157,f166,f163,f103])).

fof(f157,plain,
    ( spl7_10
  <=> m1_subset_1(sK5(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f170,plain,
    ( v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_10 ),
    inference(resolution,[],[f158,f93])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),u1_struct_0(X0))
      | v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f158,plain,
    ( ~ m1_subset_1(sK5(sK0),u1_struct_0(sK0))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f157])).

fof(f169,plain,
    ( ~ spl7_11
    | ~ spl7_10
    | spl7_1
    | ~ spl7_12
    | spl7_13
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f154,f149,f166,f163,f103,f157,f160])).

fof(f154,plain,
    ( v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK5(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0),u1_struct_0(sK0))
    | ~ spl7_9 ),
    inference(trivial_inequality_removal,[],[f153])).

fof(f153,plain,
    ( k2_lattices(sK0,sK5(sK0),sK6(sK0)) != k2_lattices(sK0,sK5(sK0),sK6(sK0))
    | v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK5(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0),u1_struct_0(sK0))
    | ~ spl7_9 ),
    inference(superposition,[],[f95,f150])).

fof(f95,plain,(
    ! [X0] :
      ( k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0))
      | v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f151,plain,
    ( ~ spl7_4
    | spl7_1
    | spl7_9
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f147,f106,f149,f103,f112])).

fof(f147,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f146,f124])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f144,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f92,f70])).

fof(f92,plain,(
    ! [X4,X0,X3] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f140,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_8
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f136,f121,f138,f112,f106,f103])).

fof(f121,plain,
    ( spl7_6
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(sK0,X0,X1),X0)
        | ~ l3_lattices(sK0)
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f80,f122])).

fof(f122,plain,
    ( v4_lattice3(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ l3_lattices(X0)
      | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
          | ( ! [X4] :
                ( ~ r2_hidden(X4,X2)
                | ~ r3_lattices(X0,sK1(X0,X1,X2),X4)
                | ~ m1_subset_1(X4,u1_struct_0(X0)) )
            & r2_hidden(sK1(X0,X1,X2),X1)
            & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f47])).

fof(f47,plain,(
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
            | ~ r3_lattices(X0,sK1(X0,X1,X2),X4)
            | ~ m1_subset_1(X4,u1_struct_0(X0)) )
        & r2_hidden(sK1(X0,X1,X2),X1)
        & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f134,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_7
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f130,f121,f132,f112,f106,f103])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f77,f122])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
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
         => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).

fof(f127,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f64,f103])).

fof(f64,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f44])).

fof(f44,plain,
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
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

fof(f125,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f65,f106])).

fof(f65,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f123,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f66,f121])).

fof(f66,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f119,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f67,f112])).

fof(f67,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f117,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f68,f115,f112,f109,f106,f103])).

fof(f68,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:57:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (24474)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (24475)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.46  % (24465)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (24476)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.47  % (24462)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.47  % (24466)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (24464)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (24473)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.48  % (24468)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.48  % (24460)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (24477)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (24460)Refutation not found, incomplete strategy% (24460)------------------------------
% 0.20/0.48  % (24460)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (24460)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (24460)Memory used [KB]: 6140
% 0.20/0.48  % (24460)Time elapsed: 0.072 s
% 0.20/0.48  % (24460)------------------------------
% 0.20/0.48  % (24460)------------------------------
% 0.20/0.49  % (24467)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (24472)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (24472)Refutation not found, incomplete strategy% (24472)------------------------------
% 0.20/0.49  % (24472)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (24472)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (24472)Memory used [KB]: 6140
% 0.20/0.49  % (24472)Time elapsed: 0.002 s
% 0.20/0.49  % (24472)------------------------------
% 0.20/0.49  % (24472)------------------------------
% 0.20/0.49  % (24478)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.49  % (24461)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (24466)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f589,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f117,f119,f123,f125,f127,f134,f140,f151,f169,f171,f173,f175,f202,f210,f218,f232,f240,f254,f256,f258,f272,f274,f299,f380,f392,f453,f457,f501,f508,f542,f588])).
% 0.20/0.49  fof(f588,plain,(
% 0.20/0.49    spl7_1 | ~spl7_12 | ~spl7_3 | spl7_64 | ~spl7_16 | ~spl7_52),
% 0.20/0.49    inference(avatar_split_clause,[],[f586,f451,f208,f540,f109,f163,f103])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    spl7_1 <=> v2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    spl7_12 <=> l1_lattices(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.20/0.49  fof(f109,plain,(
% 0.20/0.49    spl7_3 <=> v13_lattices(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.20/0.49  fof(f540,plain,(
% 0.20/0.49    spl7_64 <=> k5_lattices(sK0) = sK4(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    spl7_16 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.20/0.49  fof(f451,plain,(
% 0.20/0.49    spl7_52 <=> sK4(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 0.20/0.49  fof(f586,plain,(
% 0.20/0.49    k5_lattices(sK0) = sK4(sK0) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl7_16 | ~spl7_52)),
% 0.20/0.49    inference(forward_demodulation,[],[f575,f452])).
% 0.20/0.49  fof(f452,plain,(
% 0.20/0.49    sK4(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0)) | ~spl7_52),
% 0.20/0.49    inference(avatar_component_clause,[],[f451])).
% 0.20/0.49  fof(f575,plain,(
% 0.20/0.49    k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl7_16),
% 0.20/0.49    inference(resolution,[],[f209,f87])).
% 0.20/0.49  fof(f87,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK3(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK3(X0,X1)) != X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK4(X0) = k2_lattices(X0,X4,sK4(X0)) & sK4(X0) = k2_lattices(X0,sK4(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f54,f56,f55])).
% 0.20/0.49  fof(f55,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK3(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK3(X0,X1)) != X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK4(X0) = k2_lattices(X0,X4,sK4(X0)) & sK4(X0) = k2_lattices(X0,sK4(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(rectify,[],[f53])).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_lattices)).
% 0.20/0.49  fof(f209,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)) ) | ~spl7_16),
% 0.20/0.49    inference(avatar_component_clause,[],[f208])).
% 0.20/0.49  fof(f542,plain,(
% 0.20/0.49    ~spl7_64 | spl7_5 | ~spl7_60),
% 0.20/0.49    inference(avatar_split_clause,[],[f524,f506,f115,f540])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    spl7_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.20/0.49  fof(f506,plain,(
% 0.20/0.49    spl7_60 <=> k15_lattice3(sK0,k1_xboole_0) = sK4(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 0.20/0.49  fof(f524,plain,(
% 0.20/0.49    k5_lattices(sK0) != sK4(sK0) | (spl7_5 | ~spl7_60)),
% 0.20/0.49    inference(superposition,[],[f116,f507])).
% 0.20/0.49  fof(f507,plain,(
% 0.20/0.49    k15_lattice3(sK0,k1_xboole_0) = sK4(sK0) | ~spl7_60),
% 0.20/0.49    inference(avatar_component_clause,[],[f506])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl7_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f115])).
% 0.20/0.49  fof(f508,plain,(
% 0.20/0.49    spl7_60 | ~spl7_43 | ~spl7_53),
% 0.20/0.49    inference(avatar_split_clause,[],[f504,f455,f390,f506])).
% 0.20/0.49  fof(f390,plain,(
% 0.20/0.49    spl7_43 <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK4(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.20/0.49  fof(f455,plain,(
% 0.20/0.49    spl7_53 <=> ! [X0] : sK4(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK4(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 0.20/0.49  fof(f504,plain,(
% 0.20/0.49    k15_lattice3(sK0,k1_xboole_0) = sK4(sK0) | (~spl7_43 | ~spl7_53)),
% 0.20/0.49    inference(forward_demodulation,[],[f391,f456])).
% 0.20/0.49  fof(f456,plain,(
% 0.20/0.49    ( ! [X0] : (sK4(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK4(sK0))) ) | ~spl7_53),
% 0.20/0.49    inference(avatar_component_clause,[],[f455])).
% 0.20/0.49  fof(f391,plain,(
% 0.20/0.49    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK4(sK0)) | ~spl7_43),
% 0.20/0.49    inference(avatar_component_clause,[],[f390])).
% 0.20/0.49  fof(f501,plain,(
% 0.20/0.49    ~spl7_25 | ~spl7_20 | ~spl7_40),
% 0.20/0.49    inference(avatar_split_clause,[],[f500,f378,f230,f263])).
% 0.20/0.49  fof(f263,plain,(
% 0.20/0.49    spl7_25 <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.20/0.49  fof(f230,plain,(
% 0.20/0.49    spl7_20 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.20/0.49  fof(f378,plain,(
% 0.20/0.49    spl7_40 <=> ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 0.20/0.49  fof(f500,plain,(
% 0.20/0.49    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (~spl7_20 | ~spl7_40)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f496])).
% 0.20/0.49  fof(f496,plain,(
% 0.20/0.49    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (~spl7_20 | ~spl7_40)),
% 0.20/0.49    inference(superposition,[],[f231,f379])).
% 0.20/0.49  fof(f379,plain,(
% 0.20/0.49    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0)))) ) | ~spl7_40),
% 0.20/0.49    inference(avatar_component_clause,[],[f378])).
% 0.20/0.49  fof(f231,plain,(
% 0.20/0.49    ( ! [X0] : (k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f230])).
% 0.20/0.49  fof(f457,plain,(
% 0.20/0.49    spl7_1 | ~spl7_4 | spl7_53 | ~spl7_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f443,f216,f455,f112,f103])).
% 0.20/0.49  fof(f112,plain,(
% 0.20/0.49    spl7_4 <=> l3_lattices(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.20/0.49  fof(f216,plain,(
% 0.20/0.49    spl7_18 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK4(sK0) = k2_lattices(sK0,X2,sK4(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.20/0.49  fof(f443,plain,(
% 0.20/0.49    ( ! [X0] : (sK4(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK4(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_18),
% 0.20/0.49    inference(resolution,[],[f217,f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 0.20/0.49  fof(f217,plain,(
% 0.20/0.49    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK4(sK0) = k2_lattices(sK0,X2,sK4(sK0))) ) | ~spl7_18),
% 0.20/0.49    inference(avatar_component_clause,[],[f216])).
% 0.20/0.49  fof(f453,plain,(
% 0.20/0.49    spl7_1 | ~spl7_12 | spl7_52 | ~spl7_18),
% 0.20/0.49    inference(avatar_split_clause,[],[f442,f216,f451,f163,f103])).
% 0.20/0.49  fof(f442,plain,(
% 0.20/0.49    sK4(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl7_18),
% 0.20/0.49    inference(resolution,[],[f217,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 0.20/0.49  fof(f392,plain,(
% 0.20/0.49    spl7_1 | ~spl7_12 | ~spl7_3 | spl7_43 | ~spl7_27),
% 0.20/0.49    inference(avatar_split_clause,[],[f280,f270,f390,f109,f163,f103])).
% 0.20/0.49  fof(f270,plain,(
% 0.20/0.49    spl7_27 <=> ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.20/0.49  fof(f280,plain,(
% 0.20/0.49    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK4(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl7_27),
% 0.20/0.49    inference(resolution,[],[f271,f87])).
% 0.20/0.49  fof(f271,plain,(
% 0.20/0.49    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)) ) | ~spl7_27),
% 0.20/0.49    inference(avatar_component_clause,[],[f270])).
% 0.20/0.49  fof(f380,plain,(
% 0.20/0.49    spl7_1 | ~spl7_4 | spl7_40 | ~spl7_31),
% 0.20/0.49    inference(avatar_split_clause,[],[f366,f297,f378,f112,f103])).
% 0.20/0.49  fof(f297,plain,(
% 0.20/0.49    spl7_31 <=> ! [X4] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.20/0.49  fof(f366,plain,(
% 0.20/0.49    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0))) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_31),
% 0.20/0.49    inference(resolution,[],[f298,f96])).
% 0.20/0.49  fof(f298,plain,(
% 0.20/0.49    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X4))) ) | ~spl7_31),
% 0.20/0.49    inference(avatar_component_clause,[],[f297])).
% 0.20/0.49  fof(f299,plain,(
% 0.20/0.49    spl7_1 | ~spl7_12 | spl7_3 | spl7_31 | ~spl7_27),
% 0.20/0.49    inference(avatar_split_clause,[],[f279,f270,f297,f109,f163,f103])).
% 0.20/0.49  fof(f279,plain,(
% 0.20/0.49    ( ! [X4] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X4)) | v13_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_27),
% 0.20/0.49    inference(resolution,[],[f271,f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f57])).
% 0.20/0.49  fof(f274,plain,(
% 0.20/0.49    spl7_1 | ~spl7_4 | spl7_25),
% 0.20/0.49    inference(avatar_split_clause,[],[f273,f263,f112,f103])).
% 0.20/0.49  fof(f273,plain,(
% 0.20/0.49    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl7_25),
% 0.20/0.49    inference(resolution,[],[f264,f96])).
% 0.20/0.49  fof(f264,plain,(
% 0.20/0.49    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | spl7_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f263])).
% 0.20/0.49  fof(f272,plain,(
% 0.20/0.49    ~spl7_25 | spl7_27 | ~spl7_7 | ~spl7_8 | ~spl7_24),
% 0.20/0.49    inference(avatar_split_clause,[],[f261,f252,f138,f132,f270,f263])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    spl7_7 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    spl7_8 <=> ! [X1,X0] : (r2_hidden(sK1(sK0,X0,X1),X0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.20/0.49  fof(f252,plain,(
% 0.20/0.49    spl7_24 <=> ! [X3,X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.20/0.49  fof(f261,plain,(
% 0.20/0.49    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl7_7 | ~spl7_8 | ~spl7_24)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f260])).
% 0.20/0.49  fof(f260,plain,(
% 0.20/0.49    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl7_7 | ~spl7_8 | ~spl7_24)),
% 0.20/0.49    inference(resolution,[],[f253,f143])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl7_7 | ~spl7_8)),
% 0.20/0.49    inference(superposition,[],[f142,f133])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    ( ! [X0] : (k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f132])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | ~spl7_8),
% 0.20/0.49    inference(resolution,[],[f141,f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,sK1(sK0,X0,X1)) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))) ) | ~spl7_8),
% 0.20/0.49    inference(resolution,[],[f139,f97])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK1(sK0,X0,X1),X0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))) ) | ~spl7_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f138])).
% 0.20/0.49  fof(f253,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~r3_lattices(sK0,X3,X2) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl7_24),
% 0.20/0.49    inference(avatar_component_clause,[],[f252])).
% 0.20/0.49  fof(f258,plain,(
% 0.20/0.49    ~spl7_4 | spl7_1 | ~spl7_2 | spl7_23),
% 0.20/0.49    inference(avatar_split_clause,[],[f257,f249,f106,f103,f112])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    spl7_2 <=> v10_lattices(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.20/0.49  fof(f249,plain,(
% 0.20/0.49    spl7_23 <=> v9_lattices(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.20/0.49  fof(f257,plain,(
% 0.20/0.49    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl7_23),
% 0.20/0.49    inference(resolution,[],[f250,f74])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.49    inference(flattening,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.20/0.49  fof(f250,plain,(
% 0.20/0.49    ~v9_lattices(sK0) | spl7_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f249])).
% 0.20/0.49  fof(f256,plain,(
% 0.20/0.49    ~spl7_4 | spl7_1 | ~spl7_2 | spl7_22),
% 0.20/0.49    inference(avatar_split_clause,[],[f255,f246,f106,f103,f112])).
% 0.20/0.49  fof(f246,plain,(
% 0.20/0.49    spl7_22 <=> v8_lattices(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.20/0.49  fof(f255,plain,(
% 0.20/0.49    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl7_22),
% 0.20/0.49    inference(resolution,[],[f247,f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f247,plain,(
% 0.20/0.49    ~v8_lattices(sK0) | spl7_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f246])).
% 0.20/0.49  fof(f254,plain,(
% 0.20/0.49    spl7_1 | ~spl7_22 | ~spl7_23 | ~spl7_4 | spl7_24 | ~spl7_21),
% 0.20/0.49    inference(avatar_split_clause,[],[f243,f238,f252,f112,f249,f246,f103])).
% 0.20/0.49  fof(f238,plain,(
% 0.20/0.49    spl7_21 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | r1_lattices(sK0,X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.20/0.49  fof(f243,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_21),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f242])).
% 0.20/0.49  fof(f242,plain,(
% 0.20/0.49    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_21),
% 0.20/0.49    inference(resolution,[],[f239,f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) = X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 0.20/0.49  fof(f239,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f238])).
% 0.20/0.49  fof(f240,plain,(
% 0.20/0.49    spl7_1 | ~spl7_13 | ~spl7_4 | spl7_21 | ~spl7_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f235,f106,f238,f112,f166,f103])).
% 0.20/0.49  fof(f166,plain,(
% 0.20/0.49    spl7_13 <=> v6_lattices(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.20/0.49  fof(f235,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,X0,X1) | ~r3_lattices(sK0,X0,X1) | ~v6_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_2),
% 0.20/0.49    inference(resolution,[],[f234,f124])).
% 0.20/0.49  fof(f124,plain,(
% 0.20/0.49    v10_lattices(sK0) | ~spl7_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f106])).
% 0.20/0.49  fof(f234,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X2,X0) | ~r3_lattices(X1,X2,X0) | ~v6_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f233])).
% 0.20/0.49  fof(f233,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X2,X0) | ~r3_lattices(X1,X2,X0) | ~v6_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.20/0.49    inference(resolution,[],[f181,f73])).
% 0.20/0.49  fof(f181,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v8_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f180])).
% 0.20/0.49  fof(f180,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.49    inference(resolution,[],[f98,f74])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.20/0.49  fof(f232,plain,(
% 0.20/0.49    spl7_1 | ~spl7_12 | spl7_3 | spl7_20 | ~spl7_9 | ~spl7_15),
% 0.20/0.49    inference(avatar_split_clause,[],[f228,f200,f149,f230,f109,f163,f103])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    spl7_9 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    spl7_15 <=> ! [X0] : (k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | k2_lattices(sK0,sK3(sK0,X0),X0) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.20/0.49  fof(f228,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl7_9 | ~spl7_15)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f227])).
% 0.20/0.49  fof(f227,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | v13_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl7_9 | ~spl7_15)),
% 0.20/0.49    inference(resolution,[],[f226,f90])).
% 0.20/0.49  fof(f226,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0) ) | (~spl7_9 | ~spl7_15)),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f223])).
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    ( ! [X0] : (k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))) ) | (~spl7_9 | ~spl7_15)),
% 0.20/0.49    inference(superposition,[],[f201,f150])).
% 0.20/0.49  fof(f150,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f149])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    ( ! [X0] : (k2_lattices(sK0,sK3(sK0,X0),X0) != X0 | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f200])).
% 0.20/0.49  fof(f218,plain,(
% 0.20/0.49    spl7_1 | ~spl7_12 | spl7_18 | ~spl7_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f205,f109,f216,f163,f103])).
% 0.20/0.49  fof(f205,plain,(
% 0.20/0.49    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK4(sK0) = k2_lattices(sK0,X2,sK4(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_3),
% 0.20/0.49    inference(resolution,[],[f198,f89])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X4,X0] : (~v13_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | sK4(X0) = k2_lattices(X0,X4,sK4(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f57])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    v13_lattices(sK0) | ~spl7_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f109])).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    spl7_1 | ~spl7_12 | spl7_16 | ~spl7_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f203,f109,f208,f163,f103])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_3),
% 0.20/0.49    inference(resolution,[],[f198,f129])).
% 0.20/0.49  fof(f129,plain,(
% 0.20/0.49    ( ! [X0,X3] : (~v13_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(global_subsumption,[],[f82,f101])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(equality_resolution,[],[f83])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f50,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(rectify,[],[f49])).
% 0.20/0.49  % (24461)Refutation not found, incomplete strategy% (24461)------------------------------
% 0.20/0.49  % (24461)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (24461)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f34])).
% 0.20/0.49  % (24461)Memory used [KB]: 10618
% 0.20/0.49  % (24461)Time elapsed: 0.082 s
% 0.20/0.49  % (24461)------------------------------
% 0.20/0.49  % (24461)------------------------------
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    ~spl7_4 | spl7_3 | spl7_15 | spl7_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f197,f103,f200,f109,f112])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    ( ! [X0] : (k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v13_lattices(sK0) | k2_lattices(sK0,sK3(sK0,X0),X0) != X0 | ~l3_lattices(sK0)) ) | spl7_1),
% 0.20/0.49    inference(resolution,[],[f179,f126])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    ~v2_struct_0(sK0) | spl7_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f103])).
% 0.20/0.49  fof(f179,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | k2_lattices(X0,X1,sK3(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | v13_lattices(X0) | k2_lattices(X0,sK3(X0,X1),X1) != X1 | ~l3_lattices(X0)) )),
% 0.20/0.49    inference(resolution,[],[f91,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 0.20/0.49    inference(pure_predicate_removal,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_lattices(X0) | k2_lattices(X0,sK3(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK3(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | v13_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f57])).
% 0.20/0.49  fof(f175,plain,(
% 0.20/0.49    spl7_1 | ~spl7_12 | spl7_13 | spl7_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f174,f160,f166,f163,f103])).
% 0.20/0.49  fof(f160,plain,(
% 0.20/0.49    spl7_11 <=> m1_subset_1(sK6(sK0),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | spl7_11),
% 0.20/0.49    inference(resolution,[],[f161,f94])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK6(X0),u1_struct_0(X0)) | v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f62])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f59,f61,f60])).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK5(X0),X2) != k2_lattices(X0,X2,sK5(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ! [X0] : (? [X2] : (k2_lattices(X0,sK5(X0),X2) != k2_lattices(X0,X2,sK5(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(rectify,[],[f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_lattices)).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    ~m1_subset_1(sK6(sK0),u1_struct_0(sK0)) | spl7_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f160])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    ~spl7_4 | spl7_12),
% 0.20/0.49    inference(avatar_split_clause,[],[f172,f163,f112])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    ~l3_lattices(sK0) | spl7_12),
% 0.20/0.49    inference(resolution,[],[f164,f70])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    ~l1_lattices(sK0) | spl7_12),
% 0.20/0.49    inference(avatar_component_clause,[],[f163])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    spl7_1 | ~spl7_12 | spl7_13 | spl7_10),
% 0.20/0.49    inference(avatar_split_clause,[],[f170,f157,f166,f163,f103])).
% 0.20/0.49  fof(f157,plain,(
% 0.20/0.49    spl7_10 <=> m1_subset_1(sK5(sK0),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | spl7_10),
% 0.20/0.49    inference(resolution,[],[f158,f93])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(sK5(X0),u1_struct_0(X0)) | v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f62])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    ~m1_subset_1(sK5(sK0),u1_struct_0(sK0)) | spl7_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f157])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    ~spl7_11 | ~spl7_10 | spl7_1 | ~spl7_12 | spl7_13 | ~spl7_9),
% 0.20/0.49    inference(avatar_split_clause,[],[f154,f149,f166,f163,f103,f157,f160])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK5(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK0),u1_struct_0(sK0)) | ~spl7_9),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f153])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    k2_lattices(sK0,sK5(sK0),sK6(sK0)) != k2_lattices(sK0,sK5(sK0),sK6(sK0)) | v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK5(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK0),u1_struct_0(sK0)) | ~spl7_9),
% 0.20/0.49    inference(superposition,[],[f95,f150])).
% 0.20/0.49  fof(f95,plain,(
% 0.20/0.49    ( ! [X0] : (k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0)) | v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f62])).
% 0.20/0.49  fof(f151,plain,(
% 0.20/0.49    ~spl7_4 | spl7_1 | spl7_9 | ~spl7_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f147,f106,f149,f103,f112])).
% 0.20/0.49  fof(f147,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_2),
% 0.20/0.49    inference(resolution,[],[f146,f124])).
% 0.20/0.49  fof(f146,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f145])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.20/0.49    inference(resolution,[],[f144,f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v6_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.20/0.49    inference(resolution,[],[f92,f70])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ( ! [X4,X0,X3] : (~l1_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f62])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    spl7_1 | ~spl7_2 | ~spl7_4 | spl7_8 | ~spl7_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f136,f121,f138,f112,f106,f103])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    spl7_6 <=> v4_lattice3(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r2_hidden(sK1(sK0,X0,X1),X0) | ~l3_lattices(sK0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_6),
% 0.20/0.49    inference(resolution,[],[f80,f122])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    v4_lattice3(sK0) | ~spl7_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f121])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | r2_hidden(sK1(X0,X1,X2),X1) | ~l3_lattices(X0) | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK1(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK1(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_lattice3)).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    spl7_1 | ~spl7_2 | ~spl7_4 | spl7_7 | ~spl7_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f130,f121,f132,f112,f106,f103])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_6),
% 0.20/0.49    inference(resolution,[],[f77,f122])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v4_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_lattice3)).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    ~spl7_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f64,f103])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(negated_conjecture,[],[f14])).
% 0.20/0.49  fof(f14,conjecture,(
% 0.20/0.49    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_lattice3)).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    spl7_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f65,f106])).
% 0.20/0.49  fof(f65,plain,(
% 0.20/0.49    v10_lattices(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f123,plain,(
% 0.20/0.49    spl7_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f66,f121])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    v4_lattice3(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    spl7_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f67,f112])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    l3_lattices(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  fof(f117,plain,(
% 0.20/0.49    spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f68,f115,f112,f109,f106,f103])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f45])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (24466)------------------------------
% 0.20/0.49  % (24466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (24466)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (24466)Memory used [KB]: 11001
% 0.20/0.49  % (24466)Time elapsed: 0.070 s
% 0.20/0.49  % (24466)------------------------------
% 0.20/0.49  % (24466)------------------------------
% 0.20/0.49  % (24459)Success in time 0.146 s
%------------------------------------------------------------------------------
