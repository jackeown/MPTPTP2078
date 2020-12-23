%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  227 ( 493 expanded)
%              Number of leaves         :   51 ( 216 expanded)
%              Depth                    :   13
%              Number of atoms          : 1133 (2483 expanded)
%              Number of equality atoms :  182 ( 421 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f591,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f124,f128,f130,f132,f143,f149,f159,f177,f179,f181,f183,f210,f218,f226,f240,f248,f262,f264,f266,f280,f282,f307,f388,f400,f461,f465,f509,f516,f550,f590])).

fof(f590,plain,
    ( spl7_1
    | ~ spl7_12
    | ~ spl7_3
    | spl7_64
    | ~ spl7_16
    | ~ spl7_52 ),
    inference(avatar_split_clause,[],[f588,f459,f216,f548,f114,f171,f108])).

fof(f108,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f171,plain,
    ( spl7_12
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f114,plain,
    ( spl7_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f548,plain,
    ( spl7_64
  <=> k5_lattices(sK0) = sK4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).

fof(f216,plain,
    ( spl7_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f459,plain,
    ( spl7_52
  <=> sK4(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f588,plain,
    ( k5_lattices(sK0) = sK4(sK0)
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_16
    | ~ spl7_52 ),
    inference(forward_demodulation,[],[f577,f460])).

fof(f460,plain,
    ( sK4(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0))
    | ~ spl7_52 ),
    inference(avatar_component_clause,[],[f459])).

fof(f577,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0))
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_16 ),
    inference(resolution,[],[f217,f87])).

fof(f87,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f53,f55,f54])).

fof(f54,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK3(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK3(X0,X1)) != X1 )
        & m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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

fof(f53,plain,(
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
    inference(rectify,[],[f52])).

fof(f52,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).

fof(f217,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f216])).

fof(f550,plain,
    ( ~ spl7_64
    | spl7_5
    | ~ spl7_60 ),
    inference(avatar_split_clause,[],[f532,f514,f120,f548])).

fof(f120,plain,
    ( spl7_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f514,plain,
    ( spl7_60
  <=> k15_lattice3(sK0,k1_xboole_0) = sK4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).

fof(f532,plain,
    ( k5_lattices(sK0) != sK4(sK0)
    | spl7_5
    | ~ spl7_60 ),
    inference(superposition,[],[f121,f515])).

fof(f515,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = sK4(sK0)
    | ~ spl7_60 ),
    inference(avatar_component_clause,[],[f514])).

fof(f121,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | spl7_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f516,plain,
    ( spl7_60
    | ~ spl7_43
    | ~ spl7_53 ),
    inference(avatar_split_clause,[],[f512,f463,f398,f514])).

fof(f398,plain,
    ( spl7_43
  <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f463,plain,
    ( spl7_53
  <=> ! [X0] : sK4(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK4(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f512,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = sK4(sK0)
    | ~ spl7_43
    | ~ spl7_53 ),
    inference(forward_demodulation,[],[f399,f464])).

fof(f464,plain,
    ( ! [X0] : sK4(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK4(sK0))
    | ~ spl7_53 ),
    inference(avatar_component_clause,[],[f463])).

fof(f399,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK4(sK0))
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f398])).

fof(f509,plain,
    ( ~ spl7_25
    | ~ spl7_20
    | ~ spl7_40 ),
    inference(avatar_split_clause,[],[f508,f386,f238,f271])).

fof(f271,plain,
    ( spl7_25
  <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).

fof(f238,plain,
    ( spl7_20
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f386,plain,
    ( spl7_40
  <=> ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).

fof(f508,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl7_20
    | ~ spl7_40 ),
    inference(trivial_inequality_removal,[],[f504])).

fof(f504,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl7_20
    | ~ spl7_40 ),
    inference(superposition,[],[f239,f387])).

fof(f387,plain,
    ( ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0)))
    | ~ spl7_40 ),
    inference(avatar_component_clause,[],[f386])).

fof(f239,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f238])).

fof(f465,plain,
    ( spl7_1
    | ~ spl7_4
    | spl7_53
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f451,f224,f463,f117,f108])).

fof(f117,plain,
    ( spl7_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f224,plain,
    ( spl7_18
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK4(sK0) = k2_lattices(sK0,X2,sK4(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f451,plain,
    ( ! [X0] :
        ( sK4(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK4(sK0))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_18 ),
    inference(resolution,[],[f225,f97])).

fof(f97,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f225,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK4(sK0) = k2_lattices(sK0,X2,sK4(sK0)) )
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f224])).

fof(f461,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_52
    | ~ spl7_18 ),
    inference(avatar_split_clause,[],[f450,f224,f459,f171,f108])).

fof(f450,plain,
    ( sK4(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_18 ),
    inference(resolution,[],[f225,f82])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f400,plain,
    ( spl7_1
    | ~ spl7_12
    | ~ spl7_3
    | spl7_43
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f288,f278,f398,f114,f171,f108])).

fof(f278,plain,
    ( spl7_27
  <=> ! [X1] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).

fof(f288,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK4(sK0))
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl7_27 ),
    inference(resolution,[],[f279,f87])).

fof(f279,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) )
    | ~ spl7_27 ),
    inference(avatar_component_clause,[],[f278])).

fof(f388,plain,
    ( spl7_1
    | ~ spl7_4
    | spl7_40
    | ~ spl7_31 ),
    inference(avatar_split_clause,[],[f374,f305,f386,f117,f108])).

fof(f305,plain,
    ( spl7_31
  <=> ! [X4] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X4))
        | ~ m1_subset_1(X4,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).

fof(f374,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0)))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_31 ),
    inference(resolution,[],[f306,f97])).

fof(f306,plain,
    ( ! [X4] :
        ( ~ m1_subset_1(X4,u1_struct_0(sK0))
        | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X4)) )
    | ~ spl7_31 ),
    inference(avatar_component_clause,[],[f305])).

fof(f307,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_3
    | spl7_31
    | ~ spl7_27 ),
    inference(avatar_split_clause,[],[f287,f278,f305,f114,f171,f108])).

fof(f287,plain,
    ( ! [X4] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X4))
        | v13_lattices(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_27 ),
    inference(resolution,[],[f279,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK3(X0,X1),u1_struct_0(X0))
      | v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f282,plain,
    ( spl7_1
    | ~ spl7_4
    | spl7_25 ),
    inference(avatar_split_clause,[],[f281,f271,f117,f108])).

fof(f281,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_25 ),
    inference(resolution,[],[f272,f97])).

fof(f272,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl7_25 ),
    inference(avatar_component_clause,[],[f271])).

fof(f280,plain,
    ( ~ spl7_25
    | spl7_27
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_24 ),
    inference(avatar_split_clause,[],[f269,f260,f147,f141,f278,f271])).

fof(f141,plain,
    ( spl7_7
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f147,plain,
    ( spl7_8
  <=> ! [X1,X0] :
        ( r2_hidden(sK1(sK0,X0,X1),X0)
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f260,plain,
    ( spl7_24
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X2) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f269,plain,
    ( ! [X1] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_24 ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,
    ( ! [X1] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)
        | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_7
    | ~ spl7_8
    | ~ spl7_24 ),
    inference(resolution,[],[f261,f151])).

fof(f151,plain,
    ( ! [X0] :
        ( r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_7
    | ~ spl7_8 ),
    inference(superposition,[],[f150,f142])).

fof(f142,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f141])).

fof(f150,plain,
    ( ! [X0] : r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | ~ spl7_8 ),
    inference(resolution,[],[f148,f135])).

fof(f135,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f96,f105])).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f96,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f148,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(sK0,X0,X1),X0)
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) )
    | ~ spl7_8 ),
    inference(avatar_component_clause,[],[f147])).

fof(f261,plain,
    ( ! [X2,X3] :
        ( ~ r3_lattices(sK0,X3,X2)
        | k2_lattices(sK0,X3,X2) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f260])).

fof(f266,plain,
    ( ~ spl7_4
    | spl7_1
    | ~ spl7_2
    | spl7_23 ),
    inference(avatar_split_clause,[],[f265,f257,f111,f108,f117])).

fof(f111,plain,
    ( spl7_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f257,plain,
    ( spl7_23
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f265,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl7_23 ),
    inference(resolution,[],[f258,f74])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f258,plain,
    ( ~ v9_lattices(sK0)
    | spl7_23 ),
    inference(avatar_component_clause,[],[f257])).

fof(f264,plain,
    ( ~ spl7_4
    | spl7_1
    | ~ spl7_2
    | spl7_22 ),
    inference(avatar_split_clause,[],[f263,f254,f111,f108,f117])).

fof(f254,plain,
    ( spl7_22
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f263,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl7_22 ),
    inference(resolution,[],[f255,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f255,plain,
    ( ~ v8_lattices(sK0)
    | spl7_22 ),
    inference(avatar_component_clause,[],[f254])).

fof(f262,plain,
    ( spl7_1
    | ~ spl7_22
    | ~ spl7_23
    | ~ spl7_4
    | spl7_24
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f251,f246,f260,f117,f257,f254,f108])).

fof(f246,plain,
    ( spl7_21
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1)
        | r1_lattices(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f251,plain,
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
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,
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
    inference(resolution,[],[f247,f75])).

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
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).

fof(f247,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f246])).

fof(f248,plain,
    ( spl7_1
    | ~ spl7_13
    | ~ spl7_4
    | spl7_21
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f243,f111,f246,f117,f174,f108])).

fof(f174,plain,
    ( spl7_13
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r1_lattices(sK0,X0,X1)
        | ~ r3_lattices(sK0,X0,X1)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f242,f129])).

fof(f129,plain,
    ( v10_lattices(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f242,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X2,X0)
      | ~ r3_lattices(X1,X2,X0)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f241])).

fof(f241,plain,(
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
    inference(resolution,[],[f189,f73])).

fof(f189,plain,(
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
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
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
    inference(resolution,[],[f101,f74])).

fof(f101,plain,(
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
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    inference(nnf_transformation,[],[f42])).

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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f240,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_3
    | spl7_20
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(avatar_split_clause,[],[f236,f208,f157,f238,f114,f171,f108])).

fof(f157,plain,
    ( spl7_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f208,plain,
    ( spl7_15
  <=> ! [X0] :
        ( k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | k2_lattices(sK0,sK3(sK0,X0),X0) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f236,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(duplicate_literal_removal,[],[f235])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | v13_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(resolution,[],[f234,f90])).

fof(f234,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 )
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(duplicate_literal_removal,[],[f231])).

fof(f231,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl7_9
    | ~ spl7_15 ),
    inference(superposition,[],[f209,f158])).

fof(f158,plain,
    ( ! [X0,X1] :
        ( k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f157])).

fof(f209,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,sK3(sK0,X0),X0) != X0
        | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl7_15 ),
    inference(avatar_component_clause,[],[f208])).

fof(f226,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_18
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f213,f114,f224,f171,f108])).

fof(f213,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | sK4(sK0) = k2_lattices(sK0,X2,sK4(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f206,f89])).

fof(f89,plain,(
    ! [X4,X0] :
      ( ~ v13_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | sK4(X0) = k2_lattices(X0,X4,sK4(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f206,plain,
    ( v13_lattices(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f114])).

fof(f218,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_16
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f211,f114,f216,f171,f108])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f206,f134])).

fof(f134,plain,(
    ! [X0,X3] :
      ( ~ v13_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f82,f104])).

fof(f104,plain,(
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
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).

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

fof(f49,plain,(
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
    inference(rectify,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

fof(f210,plain,
    ( ~ spl7_4
    | spl7_3
    | spl7_15
    | spl7_1 ),
    inference(avatar_split_clause,[],[f205,f108,f208,f114,f117])).

fof(f205,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK3(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v13_lattices(sK0)
        | k2_lattices(sK0,sK3(sK0,X0),X0) != X0
        | ~ l3_lattices(sK0) )
    | spl7_1 ),
    inference(resolution,[],[f187,f131])).

fof(f131,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f187,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ l1_lattices(X0)
      | k2_lattices(X0,sK3(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK3(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v13_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f183,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_13
    | spl7_11 ),
    inference(avatar_split_clause,[],[f182,f168,f174,f171,f108])).

fof(f168,plain,
    ( spl7_11
  <=> m1_subset_1(sK6(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f182,plain,
    ( v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_11 ),
    inference(resolution,[],[f169,f94])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(sK6(X0),u1_struct_0(X0))
      | v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f58,f60,f59])).

fof(f59,plain,(
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

fof(f60,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK5(X0),X2) != k2_lattices(X0,X2,sK5(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0))
        & m1_subset_1(sK6(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).

fof(f169,plain,
    ( ~ m1_subset_1(sK6(sK0),u1_struct_0(sK0))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f168])).

fof(f181,plain,
    ( ~ spl7_4
    | spl7_12 ),
    inference(avatar_split_clause,[],[f180,f171,f117])).

fof(f180,plain,
    ( ~ l3_lattices(sK0)
    | spl7_12 ),
    inference(resolution,[],[f172,f70])).

fof(f172,plain,
    ( ~ l1_lattices(sK0)
    | spl7_12 ),
    inference(avatar_component_clause,[],[f171])).

fof(f179,plain,
    ( spl7_1
    | ~ spl7_12
    | spl7_13
    | spl7_10 ),
    inference(avatar_split_clause,[],[f178,f165,f174,f171,f108])).

fof(f165,plain,
    ( spl7_10
  <=> m1_subset_1(sK5(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f178,plain,
    ( v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl7_10 ),
    inference(resolution,[],[f166,f93])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),u1_struct_0(X0))
      | v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f166,plain,
    ( ~ m1_subset_1(sK5(sK0),u1_struct_0(sK0))
    | spl7_10 ),
    inference(avatar_component_clause,[],[f165])).

fof(f177,plain,
    ( ~ spl7_11
    | ~ spl7_10
    | spl7_1
    | ~ spl7_12
    | spl7_13
    | ~ spl7_9 ),
    inference(avatar_split_clause,[],[f162,f157,f174,f171,f108,f165,f168])).

fof(f162,plain,
    ( v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK5(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0),u1_struct_0(sK0))
    | ~ spl7_9 ),
    inference(trivial_inequality_removal,[],[f161])).

fof(f161,plain,
    ( k2_lattices(sK0,sK5(sK0),sK6(sK0)) != k2_lattices(sK0,sK5(sK0),sK6(sK0))
    | v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK5(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK6(sK0),u1_struct_0(sK0))
    | ~ spl7_9 ),
    inference(superposition,[],[f95,f158])).

fof(f95,plain,(
    ! [X0] :
      ( k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0))
      | v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f159,plain,
    ( ~ spl7_4
    | spl7_1
    | spl7_9
    | ~ spl7_2 ),
    inference(avatar_split_clause,[],[f155,f111,f157,f108,f117])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f154,f129])).

fof(f154,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f152,f72])).

fof(f72,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f152,plain,(
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
    inference(cnf_transformation,[],[f61])).

fof(f149,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_8
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f145,f126,f147,f117,f111,f108])).

fof(f126,plain,
    ( spl7_6
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(sK0,X0,X1),X0)
        | ~ l3_lattices(sK0)
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f80,f127])).

fof(f127,plain,
    ( v4_lattice3(sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f126])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | r2_hidden(sK1(X0,X1,X2),X1)
      | ~ l3_lattices(X0)
      | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f46])).

fof(f46,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).

fof(f143,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_4
    | spl7_7
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f139,f126,f141,f117,f111,f108])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl7_6 ),
    inference(resolution,[],[f77,f127])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

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
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 )
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
         => ( k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1
            & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).

fof(f132,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f65,f108])).

fof(f65,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f43])).

fof(f43,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).

fof(f130,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f66,f111])).

fof(f66,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f128,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f67,f126])).

fof(f67,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f124,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f68,f117])).

fof(f68,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f122,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5 ),
    inference(avatar_split_clause,[],[f69,f120,f117,f114,f111,f108])).

fof(f69,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:17:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (24920)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (24922)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (24911)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (24913)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (24920)Refutation not found, incomplete strategy% (24920)------------------------------
% 0.21/0.48  % (24920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24920)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (24920)Memory used [KB]: 6140
% 0.21/0.48  % (24920)Time elapsed: 0.003 s
% 0.21/0.48  % (24920)------------------------------
% 0.21/0.48  % (24920)------------------------------
% 0.21/0.49  % (24928)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (24921)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (24907)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (24907)Refutation not found, incomplete strategy% (24907)------------------------------
% 0.21/0.50  % (24907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (24907)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (24907)Memory used [KB]: 6140
% 0.21/0.50  % (24907)Time elapsed: 0.083 s
% 0.21/0.50  % (24907)------------------------------
% 0.21/0.50  % (24907)------------------------------
% 0.21/0.50  % (24927)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (24914)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (24925)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (24928)Refutation not found, incomplete strategy% (24928)------------------------------
% 0.21/0.51  % (24928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24928)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24928)Memory used [KB]: 10618
% 0.21/0.51  % (24928)Time elapsed: 0.073 s
% 0.21/0.51  % (24928)------------------------------
% 0.21/0.51  % (24928)------------------------------
% 0.21/0.51  % (24910)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (24908)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (24909)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (24924)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (24908)Refutation not found, incomplete strategy% (24908)------------------------------
% 0.21/0.51  % (24908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24908)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24908)Memory used [KB]: 10618
% 0.21/0.51  % (24908)Time elapsed: 0.093 s
% 0.21/0.51  % (24908)------------------------------
% 0.21/0.51  % (24908)------------------------------
% 0.21/0.51  % (24910)Refutation not found, incomplete strategy% (24910)------------------------------
% 0.21/0.51  % (24910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24910)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24910)Memory used [KB]: 10618
% 0.21/0.51  % (24910)Time elapsed: 0.096 s
% 0.21/0.51  % (24910)------------------------------
% 0.21/0.51  % (24910)------------------------------
% 0.21/0.51  % (24915)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (24919)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (24917)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (24926)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (24916)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (24923)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (24918)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.53  % (24918)Refutation not found, incomplete strategy% (24918)------------------------------
% 0.21/0.53  % (24918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24918)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24918)Memory used [KB]: 6268
% 0.21/0.53  % (24918)Time elapsed: 0.116 s
% 0.21/0.53  % (24918)------------------------------
% 0.21/0.53  % (24918)------------------------------
% 0.21/0.53  % (24914)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f591,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f122,f124,f128,f130,f132,f143,f149,f159,f177,f179,f181,f183,f210,f218,f226,f240,f248,f262,f264,f266,f280,f282,f307,f388,f400,f461,f465,f509,f516,f550,f590])).
% 0.21/0.54  fof(f590,plain,(
% 0.21/0.54    spl7_1 | ~spl7_12 | ~spl7_3 | spl7_64 | ~spl7_16 | ~spl7_52),
% 0.21/0.54    inference(avatar_split_clause,[],[f588,f459,f216,f548,f114,f171,f108])).
% 0.21/0.54  fof(f108,plain,(
% 0.21/0.54    spl7_1 <=> v2_struct_0(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 0.21/0.54  fof(f171,plain,(
% 0.21/0.54    spl7_12 <=> l1_lattices(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 0.21/0.54  fof(f114,plain,(
% 0.21/0.54    spl7_3 <=> v13_lattices(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 0.21/0.54  fof(f548,plain,(
% 0.21/0.54    spl7_64 <=> k5_lattices(sK0) = sK4(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_64])])).
% 0.21/0.54  fof(f216,plain,(
% 0.21/0.54    spl7_16 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).
% 0.21/0.54  fof(f459,plain,(
% 0.21/0.54    spl7_52 <=> sK4(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 0.21/0.54  fof(f588,plain,(
% 0.21/0.54    k5_lattices(sK0) = sK4(sK0) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl7_16 | ~spl7_52)),
% 0.21/0.54    inference(forward_demodulation,[],[f577,f460])).
% 0.21/0.54  fof(f460,plain,(
% 0.21/0.54    sK4(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0)) | ~spl7_52),
% 0.21/0.54    inference(avatar_component_clause,[],[f459])).
% 0.21/0.54  fof(f577,plain,(
% 0.21/0.54    k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl7_16),
% 0.21/0.54    inference(resolution,[],[f217,f87])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(sK4(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK3(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK3(X0,X1)) != X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK4(X0) = k2_lattices(X0,X4,sK4(X0)) & sK4(X0) = k2_lattices(X0,sK4(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f53,f55,f54])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK3(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK3(X0,X1)) != X1) & m1_subset_1(sK3(X0,X1),u1_struct_0(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK4(X0) = k2_lattices(X0,X4,sK4(X0)) & sK4(X0) = k2_lattices(X0,sK4(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(rectify,[],[f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(nnf_transformation,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 0.21/0.54  fof(f217,plain,(
% 0.21/0.54    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)) ) | ~spl7_16),
% 0.21/0.54    inference(avatar_component_clause,[],[f216])).
% 0.21/0.54  fof(f550,plain,(
% 0.21/0.54    ~spl7_64 | spl7_5 | ~spl7_60),
% 0.21/0.54    inference(avatar_split_clause,[],[f532,f514,f120,f548])).
% 0.21/0.54  fof(f120,plain,(
% 0.21/0.54    spl7_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 0.21/0.54  fof(f514,plain,(
% 0.21/0.54    spl7_60 <=> k15_lattice3(sK0,k1_xboole_0) = sK4(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_60])])).
% 0.21/0.54  fof(f532,plain,(
% 0.21/0.54    k5_lattices(sK0) != sK4(sK0) | (spl7_5 | ~spl7_60)),
% 0.21/0.54    inference(superposition,[],[f121,f515])).
% 0.21/0.54  fof(f515,plain,(
% 0.21/0.54    k15_lattice3(sK0,k1_xboole_0) = sK4(sK0) | ~spl7_60),
% 0.21/0.54    inference(avatar_component_clause,[],[f514])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | spl7_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f120])).
% 0.21/0.54  fof(f516,plain,(
% 0.21/0.54    spl7_60 | ~spl7_43 | ~spl7_53),
% 0.21/0.54    inference(avatar_split_clause,[],[f512,f463,f398,f514])).
% 0.21/0.54  fof(f398,plain,(
% 0.21/0.54    spl7_43 <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK4(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 0.21/0.54  fof(f463,plain,(
% 0.21/0.54    spl7_53 <=> ! [X0] : sK4(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK4(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 0.21/0.54  fof(f512,plain,(
% 0.21/0.54    k15_lattice3(sK0,k1_xboole_0) = sK4(sK0) | (~spl7_43 | ~spl7_53)),
% 0.21/0.54    inference(forward_demodulation,[],[f399,f464])).
% 0.21/0.54  fof(f464,plain,(
% 0.21/0.54    ( ! [X0] : (sK4(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK4(sK0))) ) | ~spl7_53),
% 0.21/0.54    inference(avatar_component_clause,[],[f463])).
% 0.21/0.54  fof(f399,plain,(
% 0.21/0.54    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK4(sK0)) | ~spl7_43),
% 0.21/0.54    inference(avatar_component_clause,[],[f398])).
% 0.21/0.54  fof(f509,plain,(
% 0.21/0.54    ~spl7_25 | ~spl7_20 | ~spl7_40),
% 0.21/0.54    inference(avatar_split_clause,[],[f508,f386,f238,f271])).
% 0.21/0.54  fof(f271,plain,(
% 0.21/0.54    spl7_25 <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_25])])).
% 0.21/0.54  fof(f238,plain,(
% 0.21/0.54    spl7_20 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 0.21/0.54  fof(f386,plain,(
% 0.21/0.54    spl7_40 <=> ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_40])])).
% 0.21/0.54  fof(f508,plain,(
% 0.21/0.54    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (~spl7_20 | ~spl7_40)),
% 0.21/0.54    inference(trivial_inequality_removal,[],[f504])).
% 0.21/0.54  fof(f504,plain,(
% 0.21/0.54    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (~spl7_20 | ~spl7_40)),
% 0.21/0.54    inference(superposition,[],[f239,f387])).
% 0.21/0.54  fof(f387,plain,(
% 0.21/0.54    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0)))) ) | ~spl7_40),
% 0.21/0.54    inference(avatar_component_clause,[],[f386])).
% 0.21/0.54  fof(f239,plain,(
% 0.21/0.54    ( ! [X0] : (k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_20),
% 0.21/0.54    inference(avatar_component_clause,[],[f238])).
% 0.21/0.54  fof(f465,plain,(
% 0.21/0.54    spl7_1 | ~spl7_4 | spl7_53 | ~spl7_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f451,f224,f463,f117,f108])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    spl7_4 <=> l3_lattices(sK0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 0.21/0.54  fof(f224,plain,(
% 0.21/0.54    spl7_18 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK4(sK0) = k2_lattices(sK0,X2,sK4(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 0.21/0.54  fof(f451,plain,(
% 0.21/0.54    ( ! [X0] : (sK4(sK0) = k2_lattices(sK0,k15_lattice3(sK0,X0),sK4(sK0)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_18),
% 0.21/0.54    inference(resolution,[],[f225,f97])).
% 0.21/0.54  fof(f97,plain,(
% 0.21/0.54    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f39])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 0.21/0.54  fof(f225,plain,(
% 0.21/0.54    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK4(sK0) = k2_lattices(sK0,X2,sK4(sK0))) ) | ~spl7_18),
% 0.21/0.54    inference(avatar_component_clause,[],[f224])).
% 0.21/0.54  fof(f461,plain,(
% 0.21/0.54    spl7_1 | ~spl7_12 | spl7_52 | ~spl7_18),
% 0.21/0.54    inference(avatar_split_clause,[],[f450,f224,f459,f171,f108])).
% 0.21/0.54  fof(f450,plain,(
% 0.21/0.54    sK4(sK0) = k2_lattices(sK0,k5_lattices(sK0),sK4(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl7_18),
% 0.21/0.54    inference(resolution,[],[f225,f82])).
% 0.21/0.54  fof(f82,plain,(
% 0.21/0.54    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f32])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.54    inference(flattening,[],[f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.54    inference(ennf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.21/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 0.21/0.54  fof(f400,plain,(
% 0.21/0.54    spl7_1 | ~spl7_12 | ~spl7_3 | spl7_43 | ~spl7_27),
% 0.21/0.54    inference(avatar_split_clause,[],[f288,f278,f398,f114,f171,f108])).
% 0.21/0.54  fof(f278,plain,(
% 0.21/0.54    spl7_27 <=> ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl7_27])])).
% 0.21/0.55  fof(f288,plain,(
% 0.21/0.55    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK4(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl7_27),
% 0.21/0.55    inference(resolution,[],[f279,f87])).
% 0.21/0.55  fof(f279,plain,(
% 0.21/0.55    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1)) ) | ~spl7_27),
% 0.21/0.55    inference(avatar_component_clause,[],[f278])).
% 0.21/0.55  fof(f388,plain,(
% 0.21/0.55    spl7_1 | ~spl7_4 | spl7_40 | ~spl7_31),
% 0.21/0.55    inference(avatar_split_clause,[],[f374,f305,f386,f117,f108])).
% 0.21/0.55  fof(f305,plain,(
% 0.21/0.55    spl7_31 <=> ! [X4] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X4)) | ~m1_subset_1(X4,u1_struct_0(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_31])])).
% 0.21/0.55  fof(f374,plain,(
% 0.21/0.55    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,k15_lattice3(sK0,X0))) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_31),
% 0.21/0.55    inference(resolution,[],[f306,f97])).
% 0.21/0.55  fof(f306,plain,(
% 0.21/0.55    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X4))) ) | ~spl7_31),
% 0.21/0.55    inference(avatar_component_clause,[],[f305])).
% 0.21/0.55  fof(f307,plain,(
% 0.21/0.55    spl7_1 | ~spl7_12 | spl7_3 | spl7_31 | ~spl7_27),
% 0.21/0.55    inference(avatar_split_clause,[],[f287,f278,f305,f114,f171,f108])).
% 0.21/0.55  fof(f287,plain,(
% 0.21/0.55    ( ! [X4] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK3(sK0,X4)) | v13_lattices(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_27),
% 0.21/0.55    inference(resolution,[],[f279,f90])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    ( ! [X0,X1] : (m1_subset_1(sK3(X0,X1),u1_struct_0(X0)) | v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f56])).
% 0.21/0.55  fof(f282,plain,(
% 0.21/0.55    spl7_1 | ~spl7_4 | spl7_25),
% 0.21/0.55    inference(avatar_split_clause,[],[f281,f271,f117,f108])).
% 0.21/0.55  fof(f281,plain,(
% 0.21/0.55    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl7_25),
% 0.21/0.55    inference(resolution,[],[f272,f97])).
% 0.21/0.55  fof(f272,plain,(
% 0.21/0.55    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | spl7_25),
% 0.21/0.55    inference(avatar_component_clause,[],[f271])).
% 0.21/0.55  fof(f280,plain,(
% 0.21/0.55    ~spl7_25 | spl7_27 | ~spl7_7 | ~spl7_8 | ~spl7_24),
% 0.21/0.55    inference(avatar_split_clause,[],[f269,f260,f147,f141,f278,f271])).
% 0.21/0.55  fof(f141,plain,(
% 0.21/0.55    spl7_7 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 0.21/0.55  fof(f147,plain,(
% 0.21/0.55    spl7_8 <=> ! [X1,X0] : (r2_hidden(sK1(sK0,X0,X1),X0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).
% 0.21/0.55  fof(f260,plain,(
% 0.21/0.55    spl7_24 <=> ! [X3,X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 0.21/0.55  fof(f269,plain,(
% 0.21/0.55    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl7_7 | ~spl7_8 | ~spl7_24)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f268])).
% 0.21/0.55  fof(f268,plain,(
% 0.21/0.55    ( ! [X1] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X1) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | (~spl7_7 | ~spl7_8 | ~spl7_24)),
% 0.21/0.55    inference(resolution,[],[f261,f151])).
% 0.21/0.55  fof(f151,plain,(
% 0.21/0.55    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl7_7 | ~spl7_8)),
% 0.21/0.55    inference(superposition,[],[f150,f142])).
% 0.21/0.55  fof(f142,plain,(
% 0.21/0.55    ( ! [X0] : (k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f141])).
% 0.21/0.55  fof(f150,plain,(
% 0.21/0.55    ( ! [X0] : (r3_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | ~spl7_8),
% 0.21/0.55    inference(resolution,[],[f148,f135])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.55    inference(superposition,[],[f96,f105])).
% 0.21/0.55  fof(f105,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f100])).
% 0.21/0.55  fof(f100,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 0.21/0.55    inference(cnf_transformation,[],[f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.55    inference(flattening,[],[f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 0.21/0.55    inference(nnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.55  fof(f148,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK1(sK0,X0,X1),X0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))) ) | ~spl7_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f147])).
% 0.21/0.55  fof(f261,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~r3_lattices(sK0,X3,X2) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl7_24),
% 0.21/0.55    inference(avatar_component_clause,[],[f260])).
% 0.21/0.55  fof(f266,plain,(
% 0.21/0.55    ~spl7_4 | spl7_1 | ~spl7_2 | spl7_23),
% 0.21/0.55    inference(avatar_split_clause,[],[f265,f257,f111,f108,f117])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    spl7_2 <=> v10_lattices(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 0.21/0.55  fof(f257,plain,(
% 0.21/0.55    spl7_23 <=> v9_lattices(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 0.21/0.55  fof(f265,plain,(
% 0.21/0.55    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl7_23),
% 0.21/0.55    inference(resolution,[],[f258,f74])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.55    inference(flattening,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.55    inference(pure_predicate_removal,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.55    inference(pure_predicate_removal,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.55    inference(pure_predicate_removal,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.55  fof(f258,plain,(
% 0.21/0.55    ~v9_lattices(sK0) | spl7_23),
% 0.21/0.55    inference(avatar_component_clause,[],[f257])).
% 0.21/0.55  fof(f264,plain,(
% 0.21/0.55    ~spl7_4 | spl7_1 | ~spl7_2 | spl7_22),
% 0.21/0.55    inference(avatar_split_clause,[],[f263,f254,f111,f108,f117])).
% 0.21/0.55  fof(f254,plain,(
% 0.21/0.55    spl7_22 <=> v8_lattices(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 0.21/0.55  fof(f263,plain,(
% 0.21/0.55    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl7_22),
% 0.21/0.55    inference(resolution,[],[f255,f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f255,plain,(
% 0.21/0.55    ~v8_lattices(sK0) | spl7_22),
% 0.21/0.55    inference(avatar_component_clause,[],[f254])).
% 0.21/0.55  fof(f262,plain,(
% 0.21/0.55    spl7_1 | ~spl7_22 | ~spl7_23 | ~spl7_4 | spl7_24 | ~spl7_21),
% 0.21/0.55    inference(avatar_split_clause,[],[f251,f246,f260,f117,f257,f254,f108])).
% 0.21/0.55  fof(f246,plain,(
% 0.21/0.55    spl7_21 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | r1_lattices(sK0,X0,X1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 0.21/0.55  fof(f251,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_21),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f250])).
% 0.21/0.55  fof(f250,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_21),
% 0.21/0.55    inference(resolution,[],[f247,f75])).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) = X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 0.21/0.55  fof(f247,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_21),
% 0.21/0.55    inference(avatar_component_clause,[],[f246])).
% 0.21/0.55  fof(f248,plain,(
% 0.21/0.55    spl7_1 | ~spl7_13 | ~spl7_4 | spl7_21 | ~spl7_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f243,f111,f246,f117,f174,f108])).
% 0.21/0.55  fof(f174,plain,(
% 0.21/0.55    spl7_13 <=> v6_lattices(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).
% 0.21/0.55  fof(f243,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,X0,X1) | ~r3_lattices(sK0,X0,X1) | ~v6_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_2),
% 0.21/0.55    inference(resolution,[],[f242,f129])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    v10_lattices(sK0) | ~spl7_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f111])).
% 0.21/0.55  fof(f242,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X2,X0) | ~r3_lattices(X1,X2,X0) | ~v6_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f241])).
% 0.21/0.55  fof(f241,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X2,X0) | ~r3_lattices(X1,X2,X0) | ~v6_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.21/0.55    inference(resolution,[],[f189,f73])).
% 0.21/0.55  fof(f189,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v8_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f188])).
% 0.21/0.55  fof(f188,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.55    inference(resolution,[],[f101,f74])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f42])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f41])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.21/0.55  fof(f240,plain,(
% 0.21/0.55    spl7_1 | ~spl7_12 | spl7_3 | spl7_20 | ~spl7_9 | ~spl7_15),
% 0.21/0.55    inference(avatar_split_clause,[],[f236,f208,f157,f238,f114,f171,f108])).
% 0.21/0.55  fof(f157,plain,(
% 0.21/0.55    spl7_9 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 0.21/0.55  fof(f208,plain,(
% 0.21/0.55    spl7_15 <=> ! [X0] : (k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | k2_lattices(sK0,sK3(sK0,X0),X0) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl7_9 | ~spl7_15)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f235])).
% 0.21/0.55  fof(f235,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | v13_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl7_9 | ~spl7_15)),
% 0.21/0.55    inference(resolution,[],[f234,f90])).
% 0.21/0.55  fof(f234,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0) ) | (~spl7_9 | ~spl7_15)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f231])).
% 0.21/0.55  fof(f231,plain,(
% 0.21/0.55    ( ! [X0] : (k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK3(sK0,X0),u1_struct_0(sK0))) ) | (~spl7_9 | ~spl7_15)),
% 0.21/0.55    inference(superposition,[],[f209,f158])).
% 0.21/0.55  fof(f158,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f157])).
% 0.21/0.55  fof(f209,plain,(
% 0.21/0.55    ( ! [X0] : (k2_lattices(sK0,sK3(sK0,X0),X0) != X0 | k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl7_15),
% 0.21/0.55    inference(avatar_component_clause,[],[f208])).
% 0.21/0.55  fof(f226,plain,(
% 0.21/0.55    spl7_1 | ~spl7_12 | spl7_18 | ~spl7_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f213,f114,f224,f171,f108])).
% 0.21/0.55  fof(f213,plain,(
% 0.21/0.55    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | sK4(sK0) = k2_lattices(sK0,X2,sK4(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_3),
% 0.21/0.55    inference(resolution,[],[f206,f89])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    ( ! [X4,X0] : (~v13_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | sK4(X0) = k2_lattices(X0,X4,sK4(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f56])).
% 0.21/0.55  fof(f206,plain,(
% 0.21/0.55    v13_lattices(sK0) | ~spl7_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f114])).
% 0.21/0.55  fof(f218,plain,(
% 0.21/0.55    spl7_1 | ~spl7_12 | spl7_16 | ~spl7_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f211,f114,f216,f171,f108])).
% 0.21/0.55  fof(f211,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_3),
% 0.21/0.55    inference(resolution,[],[f206,f134])).
% 0.21/0.55  fof(f134,plain,(
% 0.21/0.55    ( ! [X0,X3] : (~v13_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(global_subsumption,[],[f82,f104])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f83])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    ( ! [X0,X3,X1] : (k2_lattices(X0,X1,X3) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f49,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(rectify,[],[f48])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 0.21/0.55  fof(f210,plain,(
% 0.21/0.55    ~spl7_4 | spl7_3 | spl7_15 | spl7_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f205,f108,f208,f114,f117])).
% 0.21/0.55  fof(f205,plain,(
% 0.21/0.55    ( ! [X0] : (k2_lattices(sK0,X0,sK3(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v13_lattices(sK0) | k2_lattices(sK0,sK3(sK0,X0),X0) != X0 | ~l3_lattices(sK0)) ) | spl7_1),
% 0.21/0.55    inference(resolution,[],[f187,f131])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    ~v2_struct_0(sK0) | spl7_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f108])).
% 0.21/0.55  fof(f187,plain,(
% 0.21/0.55    ( ! [X0,X1] : (v2_struct_0(X0) | k2_lattices(X0,X1,sK3(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | v13_lattices(X0) | k2_lattices(X0,sK3(X0,X1),X1) != X1 | ~l3_lattices(X0)) )),
% 0.21/0.55    inference(resolution,[],[f91,f70])).
% 0.21/0.55  fof(f70,plain,(
% 0.21/0.55    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 0.21/0.55    inference(pure_predicate_removal,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~l1_lattices(X0) | k2_lattices(X0,sK3(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK3(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | v13_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f56])).
% 0.21/0.55  fof(f183,plain,(
% 0.21/0.55    spl7_1 | ~spl7_12 | spl7_13 | spl7_11),
% 0.21/0.55    inference(avatar_split_clause,[],[f182,f168,f174,f171,f108])).
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    spl7_11 <=> m1_subset_1(sK6(sK0),u1_struct_0(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 0.21/0.55  fof(f182,plain,(
% 0.21/0.55    v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | spl7_11),
% 0.21/0.55    inference(resolution,[],[f169,f94])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(sK6(X0),u1_struct_0(X0)) | v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6])],[f58,f60,f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK5(X0),X2) != k2_lattices(X0,X2,sK5(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ! [X0] : (? [X2] : (k2_lattices(X0,sK5(X0),X2) != k2_lattices(X0,X2,sK5(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0)) & m1_subset_1(sK6(X0),u1_struct_0(X0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(rectify,[],[f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f38])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 0.21/0.55  fof(f169,plain,(
% 0.21/0.55    ~m1_subset_1(sK6(sK0),u1_struct_0(sK0)) | spl7_11),
% 0.21/0.55    inference(avatar_component_clause,[],[f168])).
% 0.21/0.55  fof(f181,plain,(
% 0.21/0.55    ~spl7_4 | spl7_12),
% 0.21/0.55    inference(avatar_split_clause,[],[f180,f171,f117])).
% 0.21/0.55  fof(f180,plain,(
% 0.21/0.55    ~l3_lattices(sK0) | spl7_12),
% 0.21/0.55    inference(resolution,[],[f172,f70])).
% 0.21/0.55  fof(f172,plain,(
% 0.21/0.55    ~l1_lattices(sK0) | spl7_12),
% 0.21/0.55    inference(avatar_component_clause,[],[f171])).
% 0.21/0.55  fof(f179,plain,(
% 0.21/0.55    spl7_1 | ~spl7_12 | spl7_13 | spl7_10),
% 0.21/0.55    inference(avatar_split_clause,[],[f178,f165,f174,f171,f108])).
% 0.21/0.55  fof(f165,plain,(
% 0.21/0.55    spl7_10 <=> m1_subset_1(sK5(sK0),u1_struct_0(sK0))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).
% 0.21/0.55  fof(f178,plain,(
% 0.21/0.55    v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | spl7_10),
% 0.21/0.55    inference(resolution,[],[f166,f93])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ( ! [X0] : (m1_subset_1(sK5(X0),u1_struct_0(X0)) | v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f61])).
% 0.21/0.55  fof(f166,plain,(
% 0.21/0.55    ~m1_subset_1(sK5(sK0),u1_struct_0(sK0)) | spl7_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f165])).
% 0.21/0.55  fof(f177,plain,(
% 0.21/0.55    ~spl7_11 | ~spl7_10 | spl7_1 | ~spl7_12 | spl7_13 | ~spl7_9),
% 0.21/0.55    inference(avatar_split_clause,[],[f162,f157,f174,f171,f108,f165,f168])).
% 0.21/0.55  fof(f162,plain,(
% 0.21/0.55    v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK5(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK0),u1_struct_0(sK0)) | ~spl7_9),
% 0.21/0.55    inference(trivial_inequality_removal,[],[f161])).
% 0.21/0.55  fof(f161,plain,(
% 0.21/0.55    k2_lattices(sK0,sK5(sK0),sK6(sK0)) != k2_lattices(sK0,sK5(sK0),sK6(sK0)) | v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK5(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK6(sK0),u1_struct_0(sK0)) | ~spl7_9),
% 0.21/0.55    inference(superposition,[],[f95,f158])).
% 0.21/0.55  fof(f95,plain,(
% 0.21/0.55    ( ! [X0] : (k2_lattices(X0,sK5(X0),sK6(X0)) != k2_lattices(X0,sK6(X0),sK5(X0)) | v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f61])).
% 0.21/0.55  fof(f159,plain,(
% 0.21/0.55    ~spl7_4 | spl7_1 | spl7_9 | ~spl7_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f155,f111,f157,f108,f117])).
% 0.21/0.55  fof(f155,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl7_2),
% 0.21/0.55    inference(resolution,[],[f154,f129])).
% 0.21/0.55  fof(f154,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f153])).
% 0.21/0.55  fof(f153,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.21/0.55    inference(resolution,[],[f152,f72])).
% 0.21/0.55  fof(f72,plain,(
% 0.21/0.55    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f152,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v6_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.21/0.55    inference(resolution,[],[f92,f70])).
% 0.21/0.55  fof(f92,plain,(
% 0.21/0.55    ( ! [X4,X0,X3] : (~l1_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f61])).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    spl7_1 | ~spl7_2 | ~spl7_4 | spl7_8 | ~spl7_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f145,f126,f147,f117,f111,f108])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    spl7_6 <=> v4_lattice3(sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 0.21/0.55  fof(f145,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r2_hidden(sK1(sK0,X0,X1),X0) | ~l3_lattices(sK0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_6),
% 0.21/0.55    inference(resolution,[],[f80,f127])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    v4_lattice3(sK0) | ~spl7_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f126])).
% 0.21/0.55  fof(f80,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | r2_hidden(sK1(X0,X1,X2),X1) | ~l3_lattices(X0) | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f47])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK1(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f30,f46])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK1(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK1(X0,X1,X2),X1) & m1_subset_1(sK1(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,axiom,(
% 0.21/0.55    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).
% 0.21/0.55  fof(f143,plain,(
% 0.21/0.55    spl7_1 | ~spl7_2 | ~spl7_4 | spl7_7 | ~spl7_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f139,f126,f141,f117,f111,f108])).
% 0.21/0.55  fof(f139,plain,(
% 0.21/0.55    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k15_lattice3(sK0,a_2_3_lattice3(sK0,X0)) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl7_6),
% 0.21/0.55    inference(resolution,[],[f77,f127])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~v4_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1 | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : ((k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f12])).
% 0.21/0.55  fof(f12,axiom,(
% 0.21/0.55    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,a_2_4_lattice3(X0,X1)) = X1 & k15_lattice3(X0,a_2_3_lattice3(X0,X1)) = X1)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_lattice3)).
% 0.21/0.55  fof(f132,plain,(
% 0.21/0.55    ~spl7_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f65,f108])).
% 0.21/0.55  fof(f65,plain,(
% 0.21/0.55    ~v2_struct_0(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f43])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f15])).
% 0.21/0.55  fof(f15,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.55    inference(negated_conjecture,[],[f14])).
% 0.21/0.55  fof(f14,conjecture,(
% 0.21/0.55    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 0.21/0.55  fof(f130,plain,(
% 0.21/0.55    spl7_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f66,f111])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    v10_lattices(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    spl7_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f67,f126])).
% 0.21/0.55  fof(f67,plain,(
% 0.21/0.55    v4_lattice3(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    spl7_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f68,f117])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    l3_lattices(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    spl7_1 | ~spl7_2 | ~spl7_3 | ~spl7_4 | ~spl7_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f69,f120,f117,f114,f111,f108])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.55    inference(cnf_transformation,[],[f44])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (24914)------------------------------
% 0.21/0.55  % (24914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24914)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (24914)Memory used [KB]: 11001
% 0.21/0.55  % (24914)Time elapsed: 0.107 s
% 0.21/0.55  % (24914)------------------------------
% 0.21/0.55  % (24914)------------------------------
% 0.21/0.55  % (24898)Success in time 0.187 s
%------------------------------------------------------------------------------
