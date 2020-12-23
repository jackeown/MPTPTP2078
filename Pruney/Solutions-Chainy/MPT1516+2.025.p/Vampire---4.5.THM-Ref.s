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
% DateTime   : Thu Dec  3 13:15:52 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  205 ( 435 expanded)
%              Number of leaves         :   46 ( 184 expanded)
%              Depth                    :   13
%              Number of atoms          : 1068 (2188 expanded)
%              Number of equality atoms :  168 ( 339 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f972,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f147,f149,f153,f155,f157,f193,f201,f224,f242,f245,f251,f254,f295,f307,f326,f448,f462,f464,f466,f500,f512,f552,f603,f607,f758,f969])).

fof(f969,plain,
    ( ~ spl10_48
    | ~ spl10_27
    | ~ spl10_57 ),
    inference(avatar_split_clause,[],[f968,f605,f324,f533])).

fof(f533,plain,
    ( spl10_48
  <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).

fof(f324,plain,
    ( spl10_27
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f605,plain,
    ( spl10_57
  <=> ! [X2] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f968,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl10_27
    | ~ spl10_57 ),
    inference(trivial_inequality_removal,[],[f967])).

fof(f967,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl10_27
    | ~ spl10_57 ),
    inference(duplicate_literal_removal,[],[f963])).

fof(f963,plain,
    ( k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl10_27
    | ~ spl10_57 ),
    inference(superposition,[],[f325,f606])).

fof(f606,plain,
    ( ! [X2] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl10_57 ),
    inference(avatar_component_clause,[],[f605])).

fof(f325,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f324])).

fof(f758,plain,
    ( ~ spl10_48
    | spl10_5
    | ~ spl10_24
    | ~ spl10_56 ),
    inference(avatar_split_clause,[],[f748,f601,f305,f145,f533])).

fof(f145,plain,
    ( spl10_5
  <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f305,plain,
    ( spl10_24
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f601,plain,
    ( spl10_56
  <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f748,plain,
    ( k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)
    | ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | ~ spl10_24
    | ~ spl10_56 ),
    inference(superposition,[],[f602,f306])).

fof(f306,plain,
    ( ! [X1] :
        ( k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f305])).

fof(f602,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f601])).

fof(f607,plain,
    ( spl10_1
    | ~ spl10_16
    | spl10_3
    | spl10_57
    | ~ spl10_9
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f592,f510,f191,f605,f139,f236,f133])).

fof(f133,plain,
    ( spl10_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f236,plain,
    ( spl10_16
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f139,plain,
    ( spl10_3
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f191,plain,
    ( spl10_9
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f510,plain,
    ( spl10_46
  <=> ! [X1,X0] :
        ( r2_hidden(sK6(sK0,X0,X1),X0)
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).

fof(f592,plain,
    ( ! [X2] :
        ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2))
        | v13_lattices(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_9
    | ~ spl10_46 ),
    inference(resolution,[],[f524,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),u1_struct_0(X0))
      | v13_lattices(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f59,f61,f60])).

fof(f60,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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

fof(f59,plain,(
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
    inference(rectify,[],[f58])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f524,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0) )
    | ~ spl10_9
    | ~ spl10_46 ),
    inference(superposition,[],[f517,f192])).

fof(f192,plain,
    ( ! [X0] :
        ( k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f191])).

fof(f517,plain,
    ( ! [X0] : k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))
    | ~ spl10_46 ),
    inference(resolution,[],[f511,f160])).

fof(f160,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f112,f129])).

fof(f129,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f118])).

fof(f118,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f112,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : ~ r2_hidden(X0,k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

fof(f511,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(sK0,X0,X1),X0)
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) )
    | ~ spl10_46 ),
    inference(avatar_component_clause,[],[f510])).

fof(f603,plain,
    ( spl10_1
    | ~ spl10_16
    | spl10_56
    | ~ spl10_9
    | ~ spl10_46 ),
    inference(avatar_split_clause,[],[f589,f510,f191,f601,f236,f133])).

fof(f589,plain,
    ( k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_9
    | ~ spl10_46 ),
    inference(resolution,[],[f524,f93])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f552,plain,
    ( spl10_1
    | ~ spl10_4
    | spl10_48 ),
    inference(avatar_split_clause,[],[f550,f533,f142,f133])).

fof(f142,plain,
    ( spl10_4
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f550,plain,
    ( ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_48 ),
    inference(resolution,[],[f534,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).

fof(f534,plain,
    ( ~ m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))
    | spl10_48 ),
    inference(avatar_component_clause,[],[f533])).

fof(f512,plain,
    ( spl10_1
    | ~ spl10_4
    | spl10_46
    | ~ spl10_44 ),
    inference(avatar_split_clause,[],[f505,f498,f510,f142,f133])).

fof(f498,plain,
    ( spl10_44
  <=> ! [X1,X0] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
        | r2_hidden(sK6(sK0,X0,X1),X0)
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).

fof(f505,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(sK0,X0,X1),X0)
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_44 ),
    inference(resolution,[],[f499,f113])).

fof(f499,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,X0,X1),X0)
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) )
    | ~ spl10_44 ),
    inference(avatar_component_clause,[],[f498])).

fof(f500,plain,
    ( spl10_1
    | ~ spl10_4
    | spl10_44
    | ~ spl10_10
    | ~ spl10_41 ),
    inference(avatar_split_clause,[],[f493,f460,f199,f498,f142,f133])).

fof(f199,plain,
    ( spl10_10
  <=> ! [X1,X0] :
        ( r2_hidden(sK6(sK0,X0,X1),X0)
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).

fof(f460,plain,
    ( spl10_41
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X2) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X3,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f493,plain,
    ( ! [X0,X1] :
        ( k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,X0,X1),X0)
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_10
    | ~ spl10_41 ),
    inference(resolution,[],[f467,f113])).

fof(f467,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0))
        | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
        | ~ m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,X0,X1),X0) )
    | ~ spl10_10
    | ~ spl10_41 ),
    inference(resolution,[],[f461,f200])).

fof(f200,plain,
    ( ! [X0,X1] :
        ( r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
        | r2_hidden(sK6(sK0,X0,X1),X0) )
    | ~ spl10_10 ),
    inference(avatar_component_clause,[],[f199])).

fof(f461,plain,
    ( ! [X2,X3] :
        ( ~ r3_lattices(sK0,X3,X2)
        | k2_lattices(sK0,X3,X2) = X3
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f460])).

fof(f466,plain,
    ( ~ spl10_4
    | spl10_1
    | ~ spl10_2
    | spl10_40 ),
    inference(avatar_split_clause,[],[f465,f457,f136,f133,f142])).

fof(f136,plain,
    ( spl10_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f457,plain,
    ( spl10_40
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f465,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl10_40 ),
    inference(resolution,[],[f458,f89])).

fof(f89,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f21])).

fof(f21,plain,(
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
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
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

fof(f458,plain,
    ( ~ v9_lattices(sK0)
    | spl10_40 ),
    inference(avatar_component_clause,[],[f457])).

fof(f464,plain,
    ( ~ spl10_4
    | spl10_1
    | ~ spl10_2
    | spl10_39 ),
    inference(avatar_split_clause,[],[f463,f454,f136,f133,f142])).

fof(f454,plain,
    ( spl10_39
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).

fof(f463,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl10_39 ),
    inference(resolution,[],[f455,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f455,plain,
    ( ~ v8_lattices(sK0)
    | spl10_39 ),
    inference(avatar_component_clause,[],[f454])).

fof(f462,plain,
    ( spl10_1
    | ~ spl10_39
    | ~ spl10_40
    | ~ spl10_4
    | spl10_41
    | ~ spl10_38 ),
    inference(avatar_split_clause,[],[f451,f446,f460,f142,f457,f454,f133])).

fof(f446,plain,
    ( spl10_38
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1)
        | r1_lattices(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).

fof(f451,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X3,X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | k2_lattices(sK0,X3,X2) = X3
        | ~ l3_lattices(sK0)
        | ~ v9_lattices(sK0)
        | ~ v8_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_38 ),
    inference(duplicate_literal_removal,[],[f450])).

fof(f450,plain,
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
    | ~ spl10_38 ),
    inference(resolution,[],[f447,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | k2_lattices(X0,X1,X2) = X1
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f447,plain,
    ( ! [X0,X1] :
        ( r1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r3_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_38 ),
    inference(avatar_component_clause,[],[f446])).

fof(f448,plain,
    ( spl10_1
    | ~ spl10_17
    | ~ spl10_4
    | spl10_38
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f443,f136,f446,f142,f239,f133])).

fof(f239,plain,
    ( spl10_17
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f443,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | r1_lattices(sK0,X0,X1)
        | ~ r3_lattices(sK0,X0,X1)
        | ~ v6_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl10_2 ),
    inference(resolution,[],[f442,f154])).

fof(f154,plain,
    ( v10_lattices(sK0)
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f136])).

fof(f442,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | r1_lattices(X1,X2,X0)
      | ~ r3_lattices(X1,X2,X0)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f441])).

fof(f441,plain,(
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
    inference(resolution,[],[f264,f88])).

fof(f264,plain,(
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
    inference(duplicate_literal_removal,[],[f263])).

fof(f263,plain,(
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
    inference(resolution,[],[f119,f89])).

fof(f119,plain,(
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
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
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
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(flattening,[],[f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f326,plain,
    ( spl10_1
    | ~ spl10_16
    | spl10_3
    | spl10_27
    | ~ spl10_13
    | ~ spl10_22 ),
    inference(avatar_split_clause,[],[f322,f293,f222,f324,f139,f236,f133])).

fof(f222,plain,
    ( spl10_13
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f293,plain,
    ( spl10_22
  <=> ! [X0] :
        ( k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | k2_lattices(sK0,sK2(sK0,X0),X0) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | v13_lattices(sK0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_13
    | ~ spl10_22 ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | v13_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_13
    | ~ spl10_22 ),
    inference(resolution,[],[f319,f101])).

fof(f319,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 )
    | ~ spl10_13
    | ~ spl10_22 ),
    inference(duplicate_literal_removal,[],[f316])).

fof(f316,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl10_13
    | ~ spl10_22 ),
    inference(superposition,[],[f294,f223])).

fof(f223,plain,
    ( ! [X0,X1] :
        ( k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_13 ),
    inference(avatar_component_clause,[],[f222])).

fof(f294,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,sK2(sK0,X0),X0) != X0
        | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f293])).

fof(f307,plain,
    ( spl10_1
    | ~ spl10_16
    | spl10_24
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f297,f139,f305,f236,f133])).

fof(f297,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0))
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_3 ),
    inference(resolution,[],[f291,f158])).

fof(f158,plain,(
    ! [X0,X3] :
      ( ~ v13_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f93,f127])).

fof(f127,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f95])).

fof(f95,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).

fof(f56,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK1(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK1(X0,X1)) != X1 )
        & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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
    inference(rectify,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

fof(f291,plain,
    ( v13_lattices(sK0)
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f139])).

fof(f295,plain,
    ( ~ spl10_4
    | spl10_3
    | spl10_22
    | spl10_1 ),
    inference(avatar_split_clause,[],[f290,f133,f293,f139,f142])).

fof(f290,plain,
    ( ! [X0] :
        ( k2_lattices(sK0,X0,sK2(sK0,X0)) != X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v13_lattices(sK0)
        | k2_lattices(sK0,sK2(sK0,X0),X0) != X0
        | ~ l3_lattices(sK0) )
    | spl10_1 ),
    inference(resolution,[],[f262,f156])).

fof(f156,plain,
    ( ~ v2_struct_0(sK0)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f133])).

fof(f262,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v13_lattices(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f102,f85])).

fof(f85,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ l1_lattices(X0)
      | k2_lattices(X0,sK2(X0,X1),X1) != X1
      | k2_lattices(X0,X1,sK2(X0,X1)) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v13_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f254,plain,
    ( spl10_1
    | ~ spl10_16
    | spl10_17
    | spl10_15 ),
    inference(avatar_split_clause,[],[f252,f233,f239,f236,f133])).

fof(f233,plain,
    ( spl10_15
  <=> m1_subset_1(sK5(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f252,plain,
    ( v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_15 ),
    inference(resolution,[],[f234,f105])).

fof(f105,plain,(
    ! [X0] :
      ( m1_subset_1(sK5(X0),u1_struct_0(X0))
      | v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f64,f66,f65])).

fof(f65,plain,(
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

fof(f66,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
        & m1_subset_1(sK5(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
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
    inference(rectify,[],[f63])).

fof(f63,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( v6_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f234,plain,
    ( ~ m1_subset_1(sK5(sK0),u1_struct_0(sK0))
    | spl10_15 ),
    inference(avatar_component_clause,[],[f233])).

fof(f251,plain,
    ( ~ spl10_4
    | spl10_16 ),
    inference(avatar_split_clause,[],[f250,f236,f142])).

fof(f250,plain,
    ( ~ l3_lattices(sK0)
    | spl10_16 ),
    inference(resolution,[],[f237,f85])).

fof(f237,plain,
    ( ~ l1_lattices(sK0)
    | spl10_16 ),
    inference(avatar_component_clause,[],[f236])).

fof(f245,plain,
    ( spl10_1
    | ~ spl10_16
    | spl10_17
    | spl10_14 ),
    inference(avatar_split_clause,[],[f243,f230,f239,f236,f133])).

fof(f230,plain,
    ( spl10_14
  <=> m1_subset_1(sK4(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f243,plain,
    ( v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl10_14 ),
    inference(resolution,[],[f231,f104])).

fof(f104,plain,(
    ! [X0] :
      ( m1_subset_1(sK4(X0),u1_struct_0(X0))
      | v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f231,plain,
    ( ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | spl10_14 ),
    inference(avatar_component_clause,[],[f230])).

fof(f242,plain,
    ( ~ spl10_15
    | ~ spl10_14
    | spl10_1
    | ~ spl10_16
    | spl10_17
    | ~ spl10_13 ),
    inference(avatar_split_clause,[],[f227,f222,f239,f236,f133,f230,f233])).

fof(f227,plain,
    ( v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0),u1_struct_0(sK0))
    | ~ spl10_13 ),
    inference(trivial_inequality_removal,[],[f226])).

fof(f226,plain,
    ( k2_lattices(sK0,sK4(sK0),sK5(sK0)) != k2_lattices(sK0,sK4(sK0),sK5(sK0))
    | v6_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK4(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK5(sK0),u1_struct_0(sK0))
    | ~ spl10_13 ),
    inference(superposition,[],[f106,f223])).

fof(f106,plain,(
    ! [X0] :
      ( k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0))
      | v6_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f224,plain,
    ( ~ spl10_4
    | spl10_1
    | spl10_13
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f220,f136,f222,f133,f142])).

fof(f220,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1)
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl10_2 ),
    inference(resolution,[],[f219,f154])).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f218])).

fof(f218,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f202,f87])).

fof(f87,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f202,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f103,f85])).

fof(f103,plain,(
    ! [X4,X0,X3] :
      ( ~ l1_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v6_lattices(X0)
      | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f201,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_10
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f197,f151,f199,f142,f136,f133])).

fof(f151,plain,
    ( spl10_6
  <=> v4_lattice3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).

fof(f197,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK6(sK0,X0,X1),X0)
        | ~ l3_lattices(sK0)
        | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_6 ),
    inference(resolution,[],[f110,f152])).

fof(f152,plain,
    ( v4_lattice3(sK0)
    | ~ spl10_6 ),
    inference(avatar_component_clause,[],[f151])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattice3(X0)
      | r2_hidden(sK6(X0,X1,X2),X1)
      | ~ l3_lattices(X0)
      | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f68])).

fof(f68,plain,(
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

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).

fof(f193,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_4
    | spl10_9
    | ~ spl10_6 ),
    inference(avatar_split_clause,[],[f189,f151,f191,f142,f136,f133])).

fof(f189,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l3_lattices(sK0)
        | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl10_6 ),
    inference(resolution,[],[f107,f152])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ v4_lattice3(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v4_lattice3(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
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
         => ( k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).

fof(f157,plain,(
    ~ spl10_1 ),
    inference(avatar_split_clause,[],[f80,f133])).

fof(f80,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
      | ~ l3_lattices(sK0)
      | ~ v13_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(sK0)
    & v4_lattice3(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f51])).

fof(f51,plain,
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).

fof(f155,plain,(
    spl10_2 ),
    inference(avatar_split_clause,[],[f81,f136])).

fof(f81,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f153,plain,(
    spl10_6 ),
    inference(avatar_split_clause,[],[f82,f151])).

fof(f82,plain,(
    v4_lattice3(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f149,plain,(
    spl10_4 ),
    inference(avatar_split_clause,[],[f83,f142])).

fof(f83,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f147,plain,
    ( spl10_1
    | ~ spl10_2
    | ~ spl10_3
    | ~ spl10_4
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f84,f145,f142,f139,f136,f133])).

fof(f84,plain,
    ( k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0)
    | ~ l3_lattices(sK0)
    | ~ v13_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 09:56:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (22495)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (22518)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.51  % (22494)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (22495)Refutation not found, incomplete strategy% (22495)------------------------------
% 0.21/0.51  % (22495)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (22497)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (22502)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.52  % (22495)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22495)Memory used [KB]: 10746
% 0.21/0.52  % (22495)Time elapsed: 0.103 s
% 0.21/0.52  % (22495)------------------------------
% 0.21/0.52  % (22495)------------------------------
% 0.21/0.52  % (22496)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.52  % (22502)Refutation not found, incomplete strategy% (22502)------------------------------
% 0.21/0.52  % (22502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (22502)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (22502)Memory used [KB]: 10618
% 0.21/0.52  % (22502)Time elapsed: 0.003 s
% 0.21/0.52  % (22502)------------------------------
% 0.21/0.52  % (22502)------------------------------
% 0.21/0.52  % (22506)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.53  % (22509)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.53  % (22493)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (22493)Refutation not found, incomplete strategy% (22493)------------------------------
% 0.21/0.53  % (22493)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (22493)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (22493)Memory used [KB]: 1663
% 0.21/0.53  % (22493)Time elapsed: 0.001 s
% 0.21/0.53  % (22493)------------------------------
% 0.21/0.53  % (22493)------------------------------
% 0.21/0.53  % (22508)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.53  % (22498)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.53  % (22515)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (22501)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (22497)Refutation not found, incomplete strategy% (22497)------------------------------
% 0.21/0.54  % (22497)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (22497)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (22497)Memory used [KB]: 6268
% 0.21/0.54  % (22497)Time elapsed: 0.127 s
% 0.21/0.54  % (22497)------------------------------
% 0.21/0.54  % (22497)------------------------------
% 0.21/0.54  % (22520)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (22517)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (22521)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (22507)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.54  % (22519)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (22514)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.54  % (22516)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (22513)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (22510)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.55  % (22512)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (22510)Refutation not found, incomplete strategy% (22510)------------------------------
% 0.21/0.55  % (22510)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (22510)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (22510)Memory used [KB]: 10618
% 0.21/0.55  % (22510)Time elapsed: 0.138 s
% 0.21/0.55  % (22510)------------------------------
% 0.21/0.55  % (22510)------------------------------
% 0.21/0.55  % (22500)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.55  % (22499)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (22505)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (22522)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (22504)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (22503)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (22504)Refutation not found, incomplete strategy% (22504)------------------------------
% 0.21/0.56  % (22504)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22504)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22504)Memory used [KB]: 10746
% 0.21/0.56  % (22504)Time elapsed: 0.149 s
% 0.21/0.56  % (22504)------------------------------
% 0.21/0.56  % (22504)------------------------------
% 0.21/0.56  % (22503)Refutation not found, incomplete strategy% (22503)------------------------------
% 0.21/0.56  % (22503)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22503)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22503)Memory used [KB]: 10746
% 0.21/0.56  % (22503)Time elapsed: 0.134 s
% 0.21/0.56  % (22503)------------------------------
% 0.21/0.56  % (22503)------------------------------
% 0.21/0.56  % (22515)Refutation not found, incomplete strategy% (22515)------------------------------
% 0.21/0.56  % (22515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (22515)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (22515)Memory used [KB]: 10746
% 0.21/0.56  % (22515)Time elapsed: 0.094 s
% 0.21/0.56  % (22515)------------------------------
% 0.21/0.56  % (22515)------------------------------
% 0.21/0.56  % (22511)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.60  % (22512)Refutation found. Thanks to Tanya!
% 0.21/0.60  % SZS status Theorem for theBenchmark
% 0.21/0.60  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f972,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(avatar_sat_refutation,[],[f147,f149,f153,f155,f157,f193,f201,f224,f242,f245,f251,f254,f295,f307,f326,f448,f462,f464,f466,f500,f512,f552,f603,f607,f758,f969])).
% 0.21/0.60  fof(f969,plain,(
% 0.21/0.60    ~spl10_48 | ~spl10_27 | ~spl10_57),
% 0.21/0.60    inference(avatar_split_clause,[],[f968,f605,f324,f533])).
% 0.21/0.60  fof(f533,plain,(
% 0.21/0.60    spl10_48 <=> m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_48])])).
% 0.21/0.60  fof(f324,plain,(
% 0.21/0.60    spl10_27 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 0.21/0.60  fof(f605,plain,(
% 0.21/0.60    spl10_57 <=> ! [X2] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).
% 0.21/0.60  fof(f968,plain,(
% 0.21/0.60    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (~spl10_27 | ~spl10_57)),
% 0.21/0.60    inference(trivial_inequality_removal,[],[f967])).
% 0.21/0.60  fof(f967,plain,(
% 0.21/0.60    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (~spl10_27 | ~spl10_57)),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f963])).
% 0.21/0.60  fof(f963,plain,(
% 0.21/0.60    k15_lattice3(sK0,k1_xboole_0) != k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (~spl10_27 | ~spl10_57)),
% 0.21/0.60    inference(superposition,[],[f325,f606])).
% 0.21/0.60  fof(f606,plain,(
% 0.21/0.60    ( ! [X2] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl10_57),
% 0.21/0.60    inference(avatar_component_clause,[],[f605])).
% 0.21/0.60  fof(f325,plain,(
% 0.21/0.60    ( ! [X0] : (k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl10_27),
% 0.21/0.60    inference(avatar_component_clause,[],[f324])).
% 0.21/0.60  fof(f758,plain,(
% 0.21/0.60    ~spl10_48 | spl10_5 | ~spl10_24 | ~spl10_56),
% 0.21/0.60    inference(avatar_split_clause,[],[f748,f601,f305,f145,f533])).
% 0.21/0.60  fof(f145,plain,(
% 0.21/0.60    spl10_5 <=> k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).
% 0.21/0.60  fof(f305,plain,(
% 0.21/0.60    spl10_24 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 0.21/0.60  fof(f601,plain,(
% 0.21/0.60    spl10_56 <=> k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).
% 0.21/0.60  fof(f748,plain,(
% 0.21/0.60    k5_lattices(sK0) = k15_lattice3(sK0,k1_xboole_0) | ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | (~spl10_24 | ~spl10_56)),
% 0.21/0.60    inference(superposition,[],[f602,f306])).
% 0.21/0.60  fof(f306,plain,(
% 0.21/0.60    ( ! [X1] : (k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl10_24),
% 0.21/0.60    inference(avatar_component_clause,[],[f305])).
% 0.21/0.60  fof(f602,plain,(
% 0.21/0.60    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~spl10_56),
% 0.21/0.60    inference(avatar_component_clause,[],[f601])).
% 0.21/0.60  fof(f607,plain,(
% 0.21/0.60    spl10_1 | ~spl10_16 | spl10_3 | spl10_57 | ~spl10_9 | ~spl10_46),
% 0.21/0.60    inference(avatar_split_clause,[],[f592,f510,f191,f605,f139,f236,f133])).
% 0.21/0.60  fof(f133,plain,(
% 0.21/0.60    spl10_1 <=> v2_struct_0(sK0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 0.21/0.60  fof(f236,plain,(
% 0.21/0.60    spl10_16 <=> l1_lattices(sK0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 0.21/0.60  fof(f139,plain,(
% 0.21/0.60    spl10_3 <=> v13_lattices(sK0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 0.21/0.60  fof(f191,plain,(
% 0.21/0.60    spl10_9 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).
% 0.21/0.60  fof(f510,plain,(
% 0.21/0.60    spl10_46 <=> ! [X1,X0] : (r2_hidden(sK6(sK0,X0,X1),X0) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_46])])).
% 0.21/0.60  fof(f592,plain,(
% 0.21/0.60    ( ! [X2] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),sK2(sK0,X2)) | v13_lattices(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl10_9 | ~spl10_46)),
% 0.21/0.60    inference(resolution,[],[f524,f101])).
% 0.21/0.60  fof(f101,plain,(
% 0.21/0.60    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) | v13_lattices(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f62])).
% 0.21/0.60  fof(f62,plain,(
% 0.21/0.60    ! [X0] : (((v13_lattices(X0) | ! [X1] : (((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & ((! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f59,f61,f60])).
% 0.21/0.60  fof(f60,plain,(
% 0.21/0.60    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f61,plain,(
% 0.21/0.60    ! [X0] : (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : ((sK3(X0) = k2_lattices(X0,X4,sK3(X0)) & sK3(X0) = k2_lattices(X0,sK3(X0),X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f59,plain,(
% 0.21/0.60    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X3] : (! [X4] : ((k2_lattices(X0,X4,X3) = X3 & k2_lattices(X0,X3,X4) = X3) | ~m1_subset_1(X4,u1_struct_0(X0))) & m1_subset_1(X3,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(rectify,[],[f58])).
% 0.21/0.60  fof(f58,plain,(
% 0.21/0.60    ! [X0] : (((v13_lattices(X0) | ! [X1] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) & (? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(nnf_transformation,[],[f37])).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f36])).
% 0.21/0.60  fof(f36,plain,(
% 0.21/0.60    ! [X0] : ((v13_lattices(X0) <=> ? [X1] : (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f11])).
% 0.21/0.60  fof(f11,axiom,(
% 0.21/0.60    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) <=> ? [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1)) & m1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_lattices)).
% 0.21/0.60  fof(f524,plain,(
% 0.21/0.60    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),X0)) ) | (~spl10_9 | ~spl10_46)),
% 0.21/0.60    inference(superposition,[],[f517,f192])).
% 0.21/0.60  fof(f192,plain,(
% 0.21/0.60    ( ! [X0] : (k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl10_9),
% 0.21/0.60    inference(avatar_component_clause,[],[f191])).
% 0.21/0.60  fof(f517,plain,(
% 0.21/0.60    ( ! [X0] : (k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k15_lattice3(sK0,X0))) ) | ~spl10_46),
% 0.21/0.60    inference(resolution,[],[f511,f160])).
% 0.21/0.60  fof(f160,plain,(
% 0.21/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.60    inference(superposition,[],[f112,f129])).
% 0.21/0.60  fof(f129,plain,(
% 0.21/0.60    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 0.21/0.60    inference(equality_resolution,[],[f118])).
% 0.21/0.60  fof(f118,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 0.21/0.60    inference(cnf_transformation,[],[f73])).
% 0.21/0.60  fof(f73,plain,(
% 0.21/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.60    inference(flattening,[],[f72])).
% 0.21/0.60  fof(f72,plain,(
% 0.21/0.60    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 0.21/0.60    inference(nnf_transformation,[],[f3])).
% 0.21/0.60  fof(f3,axiom,(
% 0.21/0.60    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.21/0.60  fof(f112,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0,X1] : ~r2_hidden(X0,k2_zfmisc_1(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).
% 0.21/0.60  fof(f511,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,X1),X0) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))) ) | ~spl10_46),
% 0.21/0.60    inference(avatar_component_clause,[],[f510])).
% 0.21/0.60  fof(f603,plain,(
% 0.21/0.60    spl10_1 | ~spl10_16 | spl10_56 | ~spl10_9 | ~spl10_46),
% 0.21/0.60    inference(avatar_split_clause,[],[f589,f510,f191,f601,f236,f133])).
% 0.21/0.60  fof(f589,plain,(
% 0.21/0.60    k15_lattice3(sK0,k1_xboole_0) = k2_lattices(sK0,k15_lattice3(sK0,k1_xboole_0),k5_lattices(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl10_9 | ~spl10_46)),
% 0.21/0.60    inference(resolution,[],[f524,f93])).
% 0.21/0.60  fof(f93,plain,(
% 0.21/0.60    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f33])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f32])).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f7])).
% 0.21/0.60  fof(f7,axiom,(
% 0.21/0.60    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 0.21/0.60  fof(f552,plain,(
% 0.21/0.60    spl10_1 | ~spl10_4 | spl10_48),
% 0.21/0.60    inference(avatar_split_clause,[],[f550,f533,f142,f133])).
% 0.21/0.60  fof(f142,plain,(
% 0.21/0.60    spl10_4 <=> l3_lattices(sK0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).
% 0.21/0.60  fof(f550,plain,(
% 0.21/0.60    ~l3_lattices(sK0) | v2_struct_0(sK0) | spl10_48),
% 0.21/0.60    inference(resolution,[],[f534,f113])).
% 0.21/0.60  fof(f113,plain,(
% 0.21/0.60    ( ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f45])).
% 0.21/0.60  fof(f45,plain,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f44])).
% 0.21/0.60  fof(f44,plain,(
% 0.21/0.60    ! [X0,X1] : (m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f13])).
% 0.21/0.60  fof(f13,axiom,(
% 0.21/0.60    ! [X0,X1] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k15_lattice3(X0,X1),u1_struct_0(X0)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k15_lattice3)).
% 0.21/0.60  fof(f534,plain,(
% 0.21/0.60    ~m1_subset_1(k15_lattice3(sK0,k1_xboole_0),u1_struct_0(sK0)) | spl10_48),
% 0.21/0.60    inference(avatar_component_clause,[],[f533])).
% 0.21/0.60  fof(f512,plain,(
% 0.21/0.60    spl10_1 | ~spl10_4 | spl10_46 | ~spl10_44),
% 0.21/0.60    inference(avatar_split_clause,[],[f505,f498,f510,f142,f133])).
% 0.21/0.60  fof(f498,plain,(
% 0.21/0.60    spl10_44 <=> ! [X1,X0] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | r2_hidden(sK6(sK0,X0,X1),X0) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_44])])).
% 0.21/0.60  fof(f505,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,X1),X0) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl10_44),
% 0.21/0.60    inference(resolution,[],[f499,f113])).
% 0.21/0.60  fof(f499,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | r2_hidden(sK6(sK0,X0,X1),X0) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1))) ) | ~spl10_44),
% 0.21/0.60    inference(avatar_component_clause,[],[f498])).
% 0.21/0.60  fof(f500,plain,(
% 0.21/0.60    spl10_1 | ~spl10_4 | spl10_44 | ~spl10_10 | ~spl10_41),
% 0.21/0.60    inference(avatar_split_clause,[],[f493,f460,f199,f498,f142,f133])).
% 0.21/0.60  fof(f199,plain,(
% 0.21/0.60    spl10_10 <=> ! [X1,X0] : (r2_hidden(sK6(sK0,X0,X1),X0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_10])])).
% 0.21/0.60  fof(f460,plain,(
% 0.21/0.60    spl10_41 <=> ! [X3,X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).
% 0.21/0.60  fof(f493,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | r2_hidden(sK6(sK0,X0,X1),X0) | ~l3_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl10_10 | ~spl10_41)),
% 0.21/0.60    inference(resolution,[],[f467,f113])).
% 0.21/0.60  fof(f467,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~m1_subset_1(k15_lattice3(sK0,X0),u1_struct_0(sK0)) | k15_lattice3(sK0,X0) = k2_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | ~m1_subset_1(k15_lattice3(sK0,X1),u1_struct_0(sK0)) | r2_hidden(sK6(sK0,X0,X1),X0)) ) | (~spl10_10 | ~spl10_41)),
% 0.21/0.60    inference(resolution,[],[f461,f200])).
% 0.21/0.60  fof(f200,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | r2_hidden(sK6(sK0,X0,X1),X0)) ) | ~spl10_10),
% 0.21/0.60    inference(avatar_component_clause,[],[f199])).
% 0.21/0.60  fof(f461,plain,(
% 0.21/0.60    ( ! [X2,X3] : (~r3_lattices(sK0,X3,X2) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl10_41),
% 0.21/0.60    inference(avatar_component_clause,[],[f460])).
% 0.21/0.60  fof(f466,plain,(
% 0.21/0.60    ~spl10_4 | spl10_1 | ~spl10_2 | spl10_40),
% 0.21/0.60    inference(avatar_split_clause,[],[f465,f457,f136,f133,f142])).
% 0.21/0.60  fof(f136,plain,(
% 0.21/0.60    spl10_2 <=> v10_lattices(sK0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 0.21/0.60  fof(f457,plain,(
% 0.21/0.60    spl10_40 <=> v9_lattices(sK0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).
% 0.21/0.60  fof(f465,plain,(
% 0.21/0.60    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl10_40),
% 0.21/0.60    inference(resolution,[],[f458,f89])).
% 0.21/0.60  fof(f89,plain,(
% 0.21/0.60    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f28])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.60    inference(flattening,[],[f27])).
% 0.21/0.60  fof(f27,plain,(
% 0.21/0.60    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f23])).
% 0.21/0.60  fof(f23,plain,(
% 0.21/0.60    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.60    inference(pure_predicate_removal,[],[f22])).
% 0.21/0.60  fof(f22,plain,(
% 0.21/0.60    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.60    inference(pure_predicate_removal,[],[f21])).
% 0.21/0.60  fof(f21,plain,(
% 0.21/0.60    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.60    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.60  fof(f5,axiom,(
% 0.21/0.60    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.60  fof(f458,plain,(
% 0.21/0.60    ~v9_lattices(sK0) | spl10_40),
% 0.21/0.60    inference(avatar_component_clause,[],[f457])).
% 0.21/0.60  fof(f464,plain,(
% 0.21/0.60    ~spl10_4 | spl10_1 | ~spl10_2 | spl10_39),
% 0.21/0.60    inference(avatar_split_clause,[],[f463,f454,f136,f133,f142])).
% 0.21/0.60  fof(f454,plain,(
% 0.21/0.60    spl10_39 <=> v8_lattices(sK0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_39])])).
% 0.21/0.60  fof(f463,plain,(
% 0.21/0.60    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl10_39),
% 0.21/0.60    inference(resolution,[],[f455,f88])).
% 0.21/0.60  fof(f88,plain,(
% 0.21/0.60    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f28])).
% 0.21/0.60  fof(f455,plain,(
% 0.21/0.60    ~v8_lattices(sK0) | spl10_39),
% 0.21/0.60    inference(avatar_component_clause,[],[f454])).
% 0.21/0.60  fof(f462,plain,(
% 0.21/0.60    spl10_1 | ~spl10_39 | ~spl10_40 | ~spl10_4 | spl10_41 | ~spl10_38),
% 0.21/0.60    inference(avatar_split_clause,[],[f451,f446,f460,f142,f457,f454,f133])).
% 0.21/0.60  fof(f446,plain,(
% 0.21/0.60    spl10_38 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | r1_lattices(sK0,X0,X1))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_38])])).
% 0.21/0.60  fof(f451,plain,(
% 0.21/0.60    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl10_38),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f450])).
% 0.21/0.60  fof(f450,plain,(
% 0.21/0.60    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r3_lattices(sK0,X3,X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | k2_lattices(sK0,X3,X2) = X3 | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v9_lattices(sK0) | ~v8_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl10_38),
% 0.21/0.60    inference(resolution,[],[f447,f91])).
% 0.21/0.60  fof(f91,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) = X1 | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f53])).
% 0.21/0.60  fof(f53,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(nnf_transformation,[],[f31])).
% 0.21/0.60  fof(f31,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f30])).
% 0.21/0.60  fof(f30,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f10])).
% 0.21/0.60  fof(f10,axiom,(
% 0.21/0.60    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_lattices)).
% 0.21/0.60  fof(f447,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r1_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r3_lattices(sK0,X0,X1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl10_38),
% 0.21/0.60    inference(avatar_component_clause,[],[f446])).
% 0.21/0.60  fof(f448,plain,(
% 0.21/0.60    spl10_1 | ~spl10_17 | ~spl10_4 | spl10_38 | ~spl10_2),
% 0.21/0.60    inference(avatar_split_clause,[],[f443,f136,f446,f142,f239,f133])).
% 0.21/0.60  fof(f239,plain,(
% 0.21/0.60    spl10_17 <=> v6_lattices(sK0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 0.21/0.60  fof(f443,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | r1_lattices(sK0,X0,X1) | ~r3_lattices(sK0,X0,X1) | ~v6_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl10_2),
% 0.21/0.60    inference(resolution,[],[f442,f154])).
% 0.21/0.60  fof(f154,plain,(
% 0.21/0.60    v10_lattices(sK0) | ~spl10_2),
% 0.21/0.60    inference(avatar_component_clause,[],[f136])).
% 0.21/0.60  fof(f442,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X2,X0) | ~r3_lattices(X1,X2,X0) | ~v6_lattices(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f441])).
% 0.21/0.60  fof(f441,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | r1_lattices(X1,X2,X0) | ~r3_lattices(X1,X2,X0) | ~v6_lattices(X1) | v2_struct_0(X1) | ~v10_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.21/0.60    inference(resolution,[],[f264,f88])).
% 0.21/0.60  fof(f264,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~v8_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0)) )),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f263])).
% 0.21/0.60  fof(f263,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.60    inference(resolution,[],[f119,f89])).
% 0.21/0.60  fof(f119,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~v9_lattices(X0) | ~r3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | r1_lattices(X0,X1,X2) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f74])).
% 0.21/0.60  fof(f74,plain,(
% 0.21/0.60    ! [X0,X1,X2] : (((r3_lattices(X0,X1,X2) | ~r1_lattices(X0,X1,X2)) & (r1_lattices(X0,X1,X2) | ~r3_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(nnf_transformation,[],[f48])).
% 0.21/0.60  fof(f48,plain,(
% 0.21/0.60    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f47])).
% 0.21/0.60  fof(f47,plain,(
% 0.21/0.60    ! [X0,X1,X2] : ((r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f9])).
% 0.21/0.60  fof(f9,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => (r3_lattices(X0,X1,X2) <=> r1_lattices(X0,X1,X2)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r3_lattices)).
% 0.21/0.60  fof(f326,plain,(
% 0.21/0.60    spl10_1 | ~spl10_16 | spl10_3 | spl10_27 | ~spl10_13 | ~spl10_22),
% 0.21/0.60    inference(avatar_split_clause,[],[f322,f293,f222,f324,f139,f236,f133])).
% 0.21/0.60  fof(f222,plain,(
% 0.21/0.60    spl10_13 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 0.21/0.60  fof(f293,plain,(
% 0.21/0.60    spl10_22 <=> ! [X0] : (k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | k2_lattices(sK0,sK2(sK0,X0),X0) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 0.21/0.60  fof(f322,plain,(
% 0.21/0.60    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl10_13 | ~spl10_22)),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f320])).
% 0.21/0.60  fof(f320,plain,(
% 0.21/0.60    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | v13_lattices(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | (~spl10_13 | ~spl10_22)),
% 0.21/0.60    inference(resolution,[],[f319,f101])).
% 0.21/0.60  fof(f319,plain,(
% 0.21/0.60    ( ! [X0] : (~m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0) ) | (~spl10_13 | ~spl10_22)),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f316])).
% 0.21/0.60  fof(f316,plain,(
% 0.21/0.60    ( ! [X0] : (k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK2(sK0,X0),u1_struct_0(sK0))) ) | (~spl10_13 | ~spl10_22)),
% 0.21/0.60    inference(superposition,[],[f294,f223])).
% 0.21/0.60  fof(f223,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl10_13),
% 0.21/0.60    inference(avatar_component_clause,[],[f222])).
% 0.21/0.60  fof(f294,plain,(
% 0.21/0.60    ( ! [X0] : (k2_lattices(sK0,sK2(sK0,X0),X0) != X0 | k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl10_22),
% 0.21/0.60    inference(avatar_component_clause,[],[f293])).
% 0.21/0.60  fof(f307,plain,(
% 0.21/0.60    spl10_1 | ~spl10_16 | spl10_24 | ~spl10_3),
% 0.21/0.60    inference(avatar_split_clause,[],[f297,f139,f305,f236,f133])).
% 0.21/0.60  fof(f297,plain,(
% 0.21/0.60    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | k5_lattices(sK0) = k2_lattices(sK0,X1,k5_lattices(sK0)) | ~l1_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl10_3),
% 0.21/0.60    inference(resolution,[],[f291,f158])).
% 0.21/0.60  fof(f158,plain,(
% 0.21/0.60    ( ! [X0,X3] : (~v13_lattices(X0) | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(global_subsumption,[],[f93,f127])).
% 0.21/0.60  fof(f127,plain,(
% 0.21/0.60    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(equality_resolution,[],[f95])).
% 0.21/0.60  fof(f95,plain,(
% 0.21/0.60    ( ! [X0,X3,X1] : (k2_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f57])).
% 0.21/0.60  fof(f57,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f55,f56])).
% 0.21/0.60  fof(f56,plain,(
% 0.21/0.60    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK1(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK1(X0,X1)) != X1) & m1_subset_1(sK1(X0,X1),u1_struct_0(X0))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f55,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(rectify,[],[f54])).
% 0.21/0.60  fof(f54,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(nnf_transformation,[],[f35])).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f34])).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f6])).
% 0.21/0.60  fof(f6,axiom,(
% 0.21/0.60    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).
% 0.21/0.60  fof(f291,plain,(
% 0.21/0.60    v13_lattices(sK0) | ~spl10_3),
% 0.21/0.60    inference(avatar_component_clause,[],[f139])).
% 0.21/0.60  fof(f295,plain,(
% 0.21/0.60    ~spl10_4 | spl10_3 | spl10_22 | spl10_1),
% 0.21/0.60    inference(avatar_split_clause,[],[f290,f133,f293,f139,f142])).
% 0.21/0.60  fof(f290,plain,(
% 0.21/0.60    ( ! [X0] : (k2_lattices(sK0,X0,sK2(sK0,X0)) != X0 | ~m1_subset_1(X0,u1_struct_0(sK0)) | v13_lattices(sK0) | k2_lattices(sK0,sK2(sK0,X0),X0) != X0 | ~l3_lattices(sK0)) ) | spl10_1),
% 0.21/0.60    inference(resolution,[],[f262,f156])).
% 0.21/0.60  fof(f156,plain,(
% 0.21/0.60    ~v2_struct_0(sK0) | spl10_1),
% 0.21/0.60    inference(avatar_component_clause,[],[f133])).
% 0.21/0.60  fof(f262,plain,(
% 0.21/0.60    ( ! [X0,X1] : (v2_struct_0(X0) | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | v13_lattices(X0) | k2_lattices(X0,sK2(X0,X1),X1) != X1 | ~l3_lattices(X0)) )),
% 0.21/0.60    inference(resolution,[],[f102,f85])).
% 0.21/0.60  fof(f85,plain,(
% 0.21/0.60    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f26])).
% 0.21/0.60  fof(f26,plain,(
% 0.21/0.60    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 0.21/0.60    inference(ennf_transformation,[],[f20])).
% 0.21/0.60  fof(f20,plain,(
% 0.21/0.60    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 0.21/0.60    inference(pure_predicate_removal,[],[f8])).
% 0.21/0.60  fof(f8,axiom,(
% 0.21/0.60    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.60  fof(f102,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~l1_lattices(X0) | k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | v13_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f62])).
% 0.21/0.60  fof(f254,plain,(
% 0.21/0.60    spl10_1 | ~spl10_16 | spl10_17 | spl10_15),
% 0.21/0.60    inference(avatar_split_clause,[],[f252,f233,f239,f236,f133])).
% 0.21/0.60  fof(f233,plain,(
% 0.21/0.60    spl10_15 <=> m1_subset_1(sK5(sK0),u1_struct_0(sK0))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 0.21/0.60  fof(f252,plain,(
% 0.21/0.60    v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | spl10_15),
% 0.21/0.60    inference(resolution,[],[f234,f105])).
% 0.21/0.60  fof(f105,plain,(
% 0.21/0.60    ( ! [X0] : (m1_subset_1(sK5(X0),u1_struct_0(X0)) | v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f67])).
% 0.21/0.60  fof(f67,plain,(
% 0.21/0.60    ! [X0] : (((v6_lattices(X0) | ((k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f64,f66,f65])).
% 0.21/0.60  fof(f65,plain,(
% 0.21/0.60    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK4(X0),u1_struct_0(X0))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f66,plain,(
% 0.21/0.60    ! [X0] : (? [X2] : (k2_lattices(X0,sK4(X0),X2) != k2_lattices(X0,X2,sK4(X0)) & m1_subset_1(X2,u1_struct_0(X0))) => (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) & m1_subset_1(sK5(X0),u1_struct_0(X0))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f64,plain,(
% 0.21/0.60    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(rectify,[],[f63])).
% 0.21/0.60  fof(f63,plain,(
% 0.21/0.60    ! [X0] : (((v6_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,X2) != k2_lattices(X0,X2,X1) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v6_lattices(X0))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(nnf_transformation,[],[f39])).
% 0.21/0.60  fof(f39,plain,(
% 0.21/0.60    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f38])).
% 0.21/0.60  fof(f38,plain,(
% 0.21/0.60    ! [X0] : ((v6_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f12])).
% 0.21/0.60  fof(f12,axiom,(
% 0.21/0.60    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v6_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,X2) = k2_lattices(X0,X2,X1)))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_lattices)).
% 0.21/0.60  fof(f234,plain,(
% 0.21/0.60    ~m1_subset_1(sK5(sK0),u1_struct_0(sK0)) | spl10_15),
% 0.21/0.60    inference(avatar_component_clause,[],[f233])).
% 0.21/0.60  fof(f251,plain,(
% 0.21/0.60    ~spl10_4 | spl10_16),
% 0.21/0.60    inference(avatar_split_clause,[],[f250,f236,f142])).
% 0.21/0.60  fof(f250,plain,(
% 0.21/0.60    ~l3_lattices(sK0) | spl10_16),
% 0.21/0.60    inference(resolution,[],[f237,f85])).
% 0.21/0.60  fof(f237,plain,(
% 0.21/0.60    ~l1_lattices(sK0) | spl10_16),
% 0.21/0.60    inference(avatar_component_clause,[],[f236])).
% 0.21/0.60  fof(f245,plain,(
% 0.21/0.60    spl10_1 | ~spl10_16 | spl10_17 | spl10_14),
% 0.21/0.60    inference(avatar_split_clause,[],[f243,f230,f239,f236,f133])).
% 0.21/0.60  fof(f230,plain,(
% 0.21/0.60    spl10_14 <=> m1_subset_1(sK4(sK0),u1_struct_0(sK0))),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 0.21/0.60  fof(f243,plain,(
% 0.21/0.60    v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | spl10_14),
% 0.21/0.60    inference(resolution,[],[f231,f104])).
% 0.21/0.60  fof(f104,plain,(
% 0.21/0.60    ( ! [X0] : (m1_subset_1(sK4(X0),u1_struct_0(X0)) | v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f67])).
% 0.21/0.60  fof(f231,plain,(
% 0.21/0.60    ~m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | spl10_14),
% 0.21/0.60    inference(avatar_component_clause,[],[f230])).
% 0.21/0.60  fof(f242,plain,(
% 0.21/0.60    ~spl10_15 | ~spl10_14 | spl10_1 | ~spl10_16 | spl10_17 | ~spl10_13),
% 0.21/0.60    inference(avatar_split_clause,[],[f227,f222,f239,f236,f133,f230,f233])).
% 0.21/0.60  fof(f227,plain,(
% 0.21/0.60    v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0),u1_struct_0(sK0)) | ~spl10_13),
% 0.21/0.60    inference(trivial_inequality_removal,[],[f226])).
% 0.21/0.60  fof(f226,plain,(
% 0.21/0.60    k2_lattices(sK0,sK4(sK0),sK5(sK0)) != k2_lattices(sK0,sK4(sK0),sK5(sK0)) | v6_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK4(sK0),u1_struct_0(sK0)) | ~m1_subset_1(sK5(sK0),u1_struct_0(sK0)) | ~spl10_13),
% 0.21/0.60    inference(superposition,[],[f106,f223])).
% 0.21/0.60  fof(f106,plain,(
% 0.21/0.60    ( ! [X0] : (k2_lattices(X0,sK4(X0),sK5(X0)) != k2_lattices(X0,sK5(X0),sK4(X0)) | v6_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f67])).
% 0.21/0.60  fof(f224,plain,(
% 0.21/0.60    ~spl10_4 | spl10_1 | spl10_13 | ~spl10_2),
% 0.21/0.60    inference(avatar_split_clause,[],[f220,f136,f222,f133,f142])).
% 0.21/0.60  fof(f220,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k2_lattices(sK0,X1,X0) = k2_lattices(sK0,X0,X1) | v2_struct_0(sK0) | ~l3_lattices(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl10_2),
% 0.21/0.60    inference(resolution,[],[f219,f154])).
% 0.21/0.60  fof(f219,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~v10_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.21/0.60    inference(duplicate_literal_removal,[],[f218])).
% 0.21/0.60  fof(f218,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1) | ~v10_lattices(X1) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.21/0.60    inference(resolution,[],[f202,f87])).
% 0.21/0.60  fof(f87,plain,(
% 0.21/0.60    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f28])).
% 0.21/0.60  fof(f202,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~v6_lattices(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1)) | k2_lattices(X1,X0,X2) = k2_lattices(X1,X2,X0) | v2_struct_0(X1) | ~l3_lattices(X1)) )),
% 0.21/0.60    inference(resolution,[],[f103,f85])).
% 0.21/0.60  fof(f103,plain,(
% 0.21/0.60    ( ! [X4,X0,X3] : (~l1_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v6_lattices(X0) | k2_lattices(X0,X4,X3) = k2_lattices(X0,X3,X4) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f67])).
% 0.21/0.60  fof(f201,plain,(
% 0.21/0.60    spl10_1 | ~spl10_2 | ~spl10_4 | spl10_10 | ~spl10_6),
% 0.21/0.60    inference(avatar_split_clause,[],[f197,f151,f199,f142,f136,f133])).
% 0.21/0.60  fof(f151,plain,(
% 0.21/0.60    spl10_6 <=> v4_lattice3(sK0)),
% 0.21/0.60    introduced(avatar_definition,[new_symbols(naming,[spl10_6])])).
% 0.21/0.60  fof(f197,plain,(
% 0.21/0.60    ( ! [X0,X1] : (r2_hidden(sK6(sK0,X0,X1),X0) | ~l3_lattices(sK0) | r3_lattices(sK0,k15_lattice3(sK0,X0),k15_lattice3(sK0,X1)) | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl10_6),
% 0.21/0.60    inference(resolution,[],[f110,f152])).
% 0.21/0.60  fof(f152,plain,(
% 0.21/0.60    v4_lattice3(sK0) | ~spl10_6),
% 0.21/0.60    inference(avatar_component_clause,[],[f151])).
% 0.21/0.60  fof(f110,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (~v4_lattice3(X0) | r2_hidden(sK6(X0,X1,X2),X1) | ~l3_lattices(X0) | r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f69])).
% 0.21/0.60  fof(f69,plain,(
% 0.21/0.60    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK6(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f43,f68])).
% 0.21/0.60  fof(f68,plain,(
% 0.21/0.60    ! [X2,X1,X0] : (? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) => (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,sK6(X0,X1,X2),X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(sK6(X0,X1,X2),X1) & m1_subset_1(sK6(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f43,plain,(
% 0.21/0.60    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : (! [X4] : (~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f42])).
% 0.21/0.60  fof(f42,plain,(
% 0.21/0.60    ! [X0] : (! [X1,X2] : (r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2)) | ? [X3] : ((! [X4] : ((~r2_hidden(X4,X2) | ~r3_lattices(X0,X3,X4)) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_hidden(X3,X1)) & m1_subset_1(X3,u1_struct_0(X0)))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f16])).
% 0.21/0.60  fof(f16,axiom,(
% 0.21/0.60    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1,X2] : (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X0)) => ~(r2_hidden(X4,X2) & r3_lattices(X0,X3,X4))) & r2_hidden(X3,X1))) => r3_lattices(X0,k15_lattice3(X0,X1),k15_lattice3(X0,X2))))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_lattice3)).
% 0.21/0.60  fof(f193,plain,(
% 0.21/0.60    spl10_1 | ~spl10_2 | ~spl10_4 | spl10_9 | ~spl10_6),
% 0.21/0.60    inference(avatar_split_clause,[],[f189,f151,f191,f142,f136,f133])).
% 0.21/0.60  fof(f189,plain,(
% 0.21/0.60    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~l3_lattices(sK0) | k15_lattice3(sK0,k6_domain_1(u1_struct_0(sK0),X0)) = X0 | ~v10_lattices(sK0) | v2_struct_0(sK0)) ) | ~spl10_6),
% 0.21/0.60    inference(resolution,[],[f107,f152])).
% 0.21/0.60  fof(f107,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~v4_lattice3(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f41])).
% 0.21/0.60  fof(f41,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f40])).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    ! [X0] : (! [X1] : ((k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v4_lattice3(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f15])).
% 0.21/0.60  fof(f15,axiom,(
% 0.21/0.60    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k16_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 & k15_lattice3(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_lattice3)).
% 0.21/0.60  fof(f157,plain,(
% 0.21/0.60    ~spl10_1),
% 0.21/0.60    inference(avatar_split_clause,[],[f80,f133])).
% 0.21/0.60  fof(f80,plain,(
% 0.21/0.60    ~v2_struct_0(sK0)),
% 0.21/0.60    inference(cnf_transformation,[],[f52])).
% 0.21/0.60  fof(f52,plain,(
% 0.21/0.60    (k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f25,f51])).
% 0.21/0.60  fof(f51,plain,(
% 0.21/0.60    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ((k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)) & l3_lattices(sK0) & v4_lattice3(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.60    introduced(choice_axiom,[])).
% 0.21/0.60  fof(f25,plain,(
% 0.21/0.60    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.60    inference(flattening,[],[f24])).
% 0.21/0.60  fof(f24,plain,(
% 0.21/0.60    ? [X0] : ((k5_lattices(X0) != k15_lattice3(X0,k1_xboole_0) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) & (l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.60    inference(ennf_transformation,[],[f18])).
% 0.21/0.60  fof(f18,negated_conjecture,(
% 0.21/0.60    ~! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.60    inference(negated_conjecture,[],[f17])).
% 0.21/0.60  fof(f17,conjecture,(
% 0.21/0.60    ! [X0] : ((l3_lattices(X0) & v4_lattice3(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (k5_lattices(X0) = k15_lattice3(X0,k1_xboole_0) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_lattice3)).
% 0.21/0.60  fof(f155,plain,(
% 0.21/0.60    spl10_2),
% 0.21/0.60    inference(avatar_split_clause,[],[f81,f136])).
% 0.21/0.60  fof(f81,plain,(
% 0.21/0.60    v10_lattices(sK0)),
% 0.21/0.60    inference(cnf_transformation,[],[f52])).
% 0.21/0.60  fof(f153,plain,(
% 0.21/0.60    spl10_6),
% 0.21/0.60    inference(avatar_split_clause,[],[f82,f151])).
% 0.21/0.60  fof(f82,plain,(
% 0.21/0.60    v4_lattice3(sK0)),
% 0.21/0.60    inference(cnf_transformation,[],[f52])).
% 0.21/0.60  fof(f149,plain,(
% 0.21/0.60    spl10_4),
% 0.21/0.60    inference(avatar_split_clause,[],[f83,f142])).
% 0.21/0.60  fof(f83,plain,(
% 0.21/0.60    l3_lattices(sK0)),
% 0.21/0.60    inference(cnf_transformation,[],[f52])).
% 0.21/0.60  fof(f147,plain,(
% 0.21/0.60    spl10_1 | ~spl10_2 | ~spl10_3 | ~spl10_4 | ~spl10_5),
% 0.21/0.60    inference(avatar_split_clause,[],[f84,f145,f142,f139,f136,f133])).
% 0.21/0.60  fof(f84,plain,(
% 0.21/0.60    k5_lattices(sK0) != k15_lattice3(sK0,k1_xboole_0) | ~l3_lattices(sK0) | ~v13_lattices(sK0) | ~v10_lattices(sK0) | v2_struct_0(sK0)),
% 0.21/0.60    inference(cnf_transformation,[],[f52])).
% 0.21/0.60  % SZS output end Proof for theBenchmark
% 0.21/0.60  % (22512)------------------------------
% 0.21/0.60  % (22512)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.60  % (22512)Termination reason: Refutation
% 0.21/0.60  
% 0.21/0.60  % (22512)Memory used [KB]: 11385
% 0.21/0.60  % (22512)Time elapsed: 0.180 s
% 0.21/0.60  % (22512)------------------------------
% 0.21/0.60  % (22512)------------------------------
% 1.90/0.60  % (22492)Success in time 0.235 s
%------------------------------------------------------------------------------
