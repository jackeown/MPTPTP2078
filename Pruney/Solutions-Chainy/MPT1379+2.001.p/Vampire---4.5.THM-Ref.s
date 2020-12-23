%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  183 ( 585 expanded)
%              Number of leaves         :   35 ( 227 expanded)
%              Depth                    :   18
%              Number of atoms          :  754 (3944 expanded)
%              Number of equality atoms :   53 ( 309 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1580,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f68,f70,f74,f78,f82,f86,f90,f94,f102,f255,f274,f278,f283,f289,f316,f326,f449,f660,f1133,f1184,f1192,f1279,f1487,f1500,f1566,f1575,f1578])).

fof(f1578,plain,
    ( ~ spl5_4
    | spl5_2
    | ~ spl5_17
    | ~ spl5_6
    | ~ spl5_21
    | ~ spl5_113 ),
    inference(avatar_split_clause,[],[f1356,f1277,f324,f80,f292,f60,f72])).

fof(f72,plain,
    ( spl5_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f60,plain,
    ( spl5_2
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f292,plain,
    ( spl5_17
  <=> r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f80,plain,
    ( spl5_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f324,plain,
    ( spl5_21
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | m1_connsp_2(X1,sK0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f1277,plain,
    ( spl5_113
  <=> k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).

fof(f1356,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | m1_connsp_2(sK3,sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6
    | ~ spl5_21
    | ~ spl5_113 ),
    inference(resolution,[],[f1282,f361])).

fof(f361,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,k1_tops_1(sK0,X0))
        | m1_connsp_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_6
    | ~ spl5_21 ),
    inference(resolution,[],[f325,f81])).

fof(f81,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f80])).

fof(f325,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(X1,sK0,X0)
        | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f324])).

fof(f1282,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_tops_1(sK0,sK3))
        | ~ r2_hidden(X0,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) )
    | ~ spl5_113 ),
    inference(superposition,[],[f54,f1278])).

fof(f1278,plain,
    ( k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))
    | ~ spl5_113 ),
    inference(avatar_component_clause,[],[f1277])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f1575,plain,
    ( ~ spl5_14
    | spl5_10
    | ~ spl5_6
    | ~ spl5_17
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f363,f324,f292,f80,f100,f269])).

fof(f269,plain,
    ( spl5_14
  <=> m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f100,plain,
    ( spl5_10
  <=> m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f363,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6
    | ~ spl5_17
    | ~ spl5_21 ),
    inference(resolution,[],[f361,f293])).

fof(f293,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f292])).

fof(f1566,plain,
    ( spl5_17
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f393,f314,f292])).

fof(f314,plain,
    ( spl5_19
  <=> r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,k3_xboole_0(sK2,sK3)),k3_xboole_0(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)),k1_tops_1(sK0,k3_xboole_0(sK2,sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f393,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ spl5_19 ),
    inference(resolution,[],[f315,f55])).

fof(f55,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k3_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f315,plain,
    ( r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,k3_xboole_0(sK2,sK3)),k3_xboole_0(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)),k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))))
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f314])).

fof(f1500,plain,
    ( ~ spl5_5
    | spl5_1
    | ~ spl5_17
    | ~ spl5_6
    | ~ spl5_21
    | ~ spl5_113 ),
    inference(avatar_split_clause,[],[f1374,f1277,f324,f80,f292,f57,f76])).

fof(f76,plain,
    ( spl5_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f57,plain,
    ( spl5_1
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1374,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6
    | ~ spl5_21
    | ~ spl5_113 ),
    inference(resolution,[],[f1283,f361])).

fof(f1283,plain,
    ( ! [X1] :
        ( r2_hidden(X1,k1_tops_1(sK0,sK2))
        | ~ r2_hidden(X1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) )
    | ~ spl5_113 ),
    inference(superposition,[],[f55,f1278])).

fof(f1487,plain,
    ( ~ spl5_5
    | spl5_17
    | ~ spl5_1
    | ~ spl5_104
    | ~ spl5_113 ),
    inference(avatar_split_clause,[],[f1486,f1277,f1182,f57,f292,f76])).

fof(f1182,plain,
    ( spl5_104
  <=> ! [X0] :
        ( r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X0,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f1486,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_1
    | ~ spl5_104
    | ~ spl5_113 ),
    inference(forward_demodulation,[],[f1480,f1278])).

fof(f1480,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
    | ~ spl5_1
    | ~ spl5_104 ),
    inference(resolution,[],[f1183,f69])).

fof(f69,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f1183,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3))) )
    | ~ spl5_104 ),
    inference(avatar_component_clause,[],[f1182])).

fof(f1279,plain,
    ( spl5_113
    | ~ spl5_5
    | ~ spl5_92 ),
    inference(avatar_split_clause,[],[f1243,f1131,f76,f1277])).

fof(f1131,plain,
    ( spl5_92
  <=> ! [X0] :
        ( k3_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k3_xboole_0(X0,sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f1243,plain,
    ( k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))
    | ~ spl5_5
    | ~ spl5_92 ),
    inference(resolution,[],[f1132,f77])).

fof(f77,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f1132,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k3_xboole_0(X0,sK3)) )
    | ~ spl5_92 ),
    inference(avatar_component_clause,[],[f1131])).

fof(f1192,plain,
    ( ~ spl5_4
    | ~ spl5_10
    | spl5_3 ),
    inference(avatar_split_clause,[],[f1190,f63,f100,f72])).

fof(f63,plain,
    ( spl5_3
  <=> m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1190,plain,
    ( ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_3 ),
    inference(superposition,[],[f64,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f64,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f1184,plain,
    ( ~ spl5_4
    | spl5_104
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f1176,f253,f80,f60,f1182,f72])).

fof(f253,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1176,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(resolution,[],[f66,f258])).

fof(f258,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X0,sK0,sK1)
        | r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X1,sK0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(resolution,[],[f257,f256])).

fof(f256,plain,
    ( ! [X0] :
        ( r2_hidden(sK1,k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(resolution,[],[f254,f81])).

fof(f254,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ m1_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f253])).

fof(f257,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK1,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK1,k3_xboole_0(X1,k1_tops_1(sK0,X0)))
        | ~ m1_connsp_2(X0,sK0,sK1) )
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(resolution,[],[f256,f53])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | r2_hidden(X4,k3_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X0)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f1133,plain,
    ( ~ spl5_4
    | spl5_92
    | ~ spl5_4
    | ~ spl5_33
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f1111,f658,f447,f72,f1131,f72])).

fof(f447,plain,
    ( spl5_33
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f658,plain,
    ( spl5_60
  <=> ! [X1,X0] :
        ( m1_subset_1(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f1111,plain,
    ( ! [X0] :
        ( k3_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k3_xboole_0(X0,sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_4
    | ~ spl5_33
    | ~ spl5_60 ),
    inference(superposition,[],[f698,f46])).

fof(f698,plain,
    ( ! [X20] :
        ( k3_xboole_0(k1_tops_1(sK0,X20),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X20,sK3))
        | ~ m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_4
    | ~ spl5_33
    | ~ spl5_60 ),
    inference(resolution,[],[f689,f73])).

fof(f73,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f689,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(k1_tops_1(sK0,X2),k1_tops_1(sK0,X3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X2,X3))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_33
    | ~ spl5_60 ),
    inference(subsumption_resolution,[],[f574,f686])).

fof(f686,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_60 ),
    inference(duplicate_literal_removal,[],[f682])).

fof(f682,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_60 ),
    inference(superposition,[],[f680,f149])).

fof(f149,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,X0) = X0
      | k3_xboole_0(X0,X0) = X0 ) ),
    inference(resolution,[],[f134,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(factoring,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f134,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X0),X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(global_subsumption,[],[f106,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X0),X1)
      | ~ r2_hidden(sK4(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X0),X1)
      | ~ r2_hidden(sK4(X0,X1,X0),X0)
      | k3_xboole_0(X0,X1) = X0
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(resolution,[],[f52,f106])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f680,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k1_tops_1(sK0,k3_xboole_0(X2,X3)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_60 ),
    inference(duplicate_literal_removal,[],[f679])).

fof(f679,plain,
    ( ! [X2,X3] :
        ( m1_subset_1(k1_tops_1(sK0,k3_xboole_0(X2,X3)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_60 ),
    inference(superposition,[],[f659,f46])).

fof(f659,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f658])).

fof(f574,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(k1_tops_1(sK0,X2),k1_tops_1(sK0,X3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X2,X3))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(k1_tops_1(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_33 ),
    inference(superposition,[],[f448,f46])).

fof(f448,plain,
    ( ! [X0,X1] :
        ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f447])).

fof(f660,plain,
    ( ~ spl5_7
    | spl5_60
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f656,f447,f658,f84])).

fof(f84,plain,
    ( spl5_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f656,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_33 ),
    inference(duplicate_literal_removal,[],[f655])).

fof(f655,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl5_33 ),
    inference(resolution,[],[f576,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f576,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(k1_tops_1(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X2,X3)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_33 ),
    inference(superposition,[],[f45,f448])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f449,plain,
    ( ~ spl5_7
    | spl5_33
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f445,f88,f447,f84])).

fof(f88,plain,
    ( spl5_8
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f445,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)) )
    | ~ spl5_8 ),
    inference(resolution,[],[f43,f89])).

fof(f89,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tops_1)).

fof(f326,plain,
    ( ~ spl5_8
    | ~ spl5_7
    | spl5_21
    | spl5_9 ),
    inference(avatar_split_clause,[],[f322,f92,f324,f84,f88])).

fof(f92,plain,
    ( spl5_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f322,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | m1_connsp_2(X1,sK0,X0) )
    | spl5_9 ),
    inference(resolution,[],[f42,f93])).

fof(f93,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_connsp_2(X2,X0,X1)
                  | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
                & ( r2_hidden(X1,k1_tops_1(X0,X2))
                  | ~ m1_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f316,plain,
    ( spl5_19
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f303,f287,f314])).

fof(f287,plain,
    ( spl5_16
  <=> r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)),k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f303,plain,
    ( r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,k3_xboole_0(sK2,sK3)),k3_xboole_0(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)),k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))))
    | ~ spl5_16 ),
    inference(resolution,[],[f288,f209])).

fof(f209,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | r2_hidden(X2,k3_xboole_0(X1,k3_xboole_0(X0,X1))) ) ),
    inference(superposition,[],[f54,f194])).

fof(f194,plain,(
    ! [X8,X7] : k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X8,k3_xboole_0(X7,X8))) ),
    inference(duplicate_literal_removal,[],[f190])).

fof(f190,plain,(
    ! [X8,X7] :
      ( k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X8,k3_xboole_0(X7,X8)))
      | k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X8,k3_xboole_0(X7,X8))) ) ),
    inference(resolution,[],[f145,f108])).

fof(f108,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(sK4(k3_xboole_0(X3,X4),X5,k3_xboole_0(X3,X4)),X4)
      | k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X5) ) ),
    inference(resolution,[],[f106,f54])).

fof(f145,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(sK4(X4,k3_xboole_0(X5,X4),X4),X5)
      | k3_xboole_0(X4,k3_xboole_0(X5,X4)) = X4 ) ),
    inference(duplicate_literal_removal,[],[f140])).

fof(f140,plain,(
    ! [X4,X5] :
      ( k3_xboole_0(X4,k3_xboole_0(X5,X4)) = X4
      | k3_xboole_0(X4,k3_xboole_0(X5,X4)) = X4
      | ~ r2_hidden(sK4(X4,k3_xboole_0(X5,X4),X4),X5) ) ),
    inference(resolution,[],[f134,f109])).

fof(f109,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(sK4(X6,X7,X6),k3_xboole_0(X8,X6))
      | k3_xboole_0(X6,X7) = X6
      | ~ r2_hidden(sK4(X6,X7,X6),X8) ) ),
    inference(resolution,[],[f106,f53])).

fof(f288,plain,
    ( r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)),k1_tops_1(sK0,k3_xboole_0(sK2,sK3))))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f287])).

fof(f289,plain,
    ( spl5_16
    | ~ spl5_12
    | ~ spl5_3
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f284,f272,f63,f262,f287])).

fof(f262,plain,
    ( spl5_12
  <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f272,plain,
    ( spl5_15
  <=> ! [X1] :
        ( r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,X1),k1_tops_1(sK0,k3_xboole_0(sK2,sK3))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X1,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f284,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)),k1_tops_1(sK0,k3_xboole_0(sK2,sK3))))
    | ~ spl5_3
    | ~ spl5_15 ),
    inference(resolution,[],[f273,f67])).

fof(f67,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f273,plain,
    ( ! [X1] :
        ( ~ m1_connsp_2(X1,sK0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,X1),k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f272])).

fof(f283,plain,
    ( ~ spl5_4
    | ~ spl5_14
    | spl5_12 ),
    inference(avatar_split_clause,[],[f281,f262,f269,f72])).

fof(f281,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_12 ),
    inference(superposition,[],[f263,f46])).

fof(f263,plain,
    ( ~ m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_12 ),
    inference(avatar_component_clause,[],[f262])).

fof(f278,plain,
    ( ~ spl5_5
    | spl5_14 ),
    inference(avatar_split_clause,[],[f275,f269,f76])).

fof(f275,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_14 ),
    inference(resolution,[],[f270,f169])).

fof(f169,plain,(
    ! [X8,X7,X9] :
      ( m1_subset_1(k3_xboole_0(X7,X8),k1_zfmisc_1(X9))
      | ~ m1_subset_1(X7,k1_zfmisc_1(X9)) ) ),
    inference(superposition,[],[f97,f144])).

fof(f144,plain,(
    ! [X6,X7] : k3_xboole_0(X6,X7) = k3_xboole_0(k3_xboole_0(X6,X7),X6) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
    ! [X6,X7] :
      ( k3_xboole_0(X6,X7) = k3_xboole_0(k3_xboole_0(X6,X7),X6)
      | k3_xboole_0(X6,X7) = k3_xboole_0(k3_xboole_0(X6,X7),X6) ) ),
    inference(resolution,[],[f134,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(k3_xboole_0(X0,X1),X2,k3_xboole_0(X0,X1)),X0)
      | k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X2) ) ),
    inference(resolution,[],[f106,f55])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f45,f46])).

fof(f270,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_14 ),
    inference(avatar_component_clause,[],[f269])).

fof(f274,plain,
    ( ~ spl5_14
    | spl5_15
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f260,f253,f100,f80,f272,f269])).

fof(f260,plain,
    ( ! [X1] :
        ( r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,X1),k1_tops_1(sK0,k3_xboole_0(sK2,sK3))))
        | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(X1,sK0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(resolution,[],[f258,f101])).

fof(f101,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f255,plain,
    ( ~ spl5_8
    | ~ spl5_7
    | spl5_11
    | spl5_9 ),
    inference(avatar_split_clause,[],[f249,f92,f253,f84,f88])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | r2_hidden(X1,k1_tops_1(sK0,X0)) )
    | spl5_9 ),
    inference(resolution,[],[f41,f93])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f102,plain,
    ( ~ spl5_4
    | spl5_10
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f95,f63,f100,f72])).

fof(f95,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_3 ),
    inference(superposition,[],[f67,f46])).

fof(f94,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f32,f92])).

fof(f32,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
      | ~ m1_connsp_2(sK3,sK0,sK1)
      | ~ m1_connsp_2(sK2,sK0,sK1) )
    & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
      | ( m1_connsp_2(sK3,sK0,sK1)
        & m1_connsp_2(sK2,sK0,sK1) ) )
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f24,f23,f22,f21])).

fof(f21,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                      | ~ m1_connsp_2(X3,X0,X1)
                      | ~ m1_connsp_2(X2,X0,X1) )
                    & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                      | ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) ) )
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                    | ~ m1_connsp_2(X3,sK0,X1)
                    | ~ m1_connsp_2(X2,sK0,X1) )
                  & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                    | ( m1_connsp_2(X3,sK0,X1)
                      & m1_connsp_2(X2,sK0,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                  | ~ m1_connsp_2(X3,sK0,X1)
                  | ~ m1_connsp_2(X2,sK0,X1) )
                & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1)
                  | ( m1_connsp_2(X3,sK0,X1)
                    & m1_connsp_2(X2,sK0,X1) ) )
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
                | ~ m1_connsp_2(X3,sK0,sK1)
                | ~ m1_connsp_2(X2,sK0,sK1) )
              & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
                | ( m1_connsp_2(X3,sK0,sK1)
                  & m1_connsp_2(X2,sK0,sK1) ) )
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
              | ~ m1_connsp_2(X3,sK0,sK1)
              | ~ m1_connsp_2(X2,sK0,sK1) )
            & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1)
              | ( m1_connsp_2(X3,sK0,sK1)
                & m1_connsp_2(X2,sK0,sK1) ) )
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
            | ~ m1_connsp_2(X3,sK0,sK1)
            | ~ m1_connsp_2(sK2,sK0,sK1) )
          & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
            | ( m1_connsp_2(X3,sK0,sK1)
              & m1_connsp_2(sK2,sK0,sK1) ) )
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X3] :
        ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
          | ~ m1_connsp_2(X3,sK0,sK1)
          | ~ m1_connsp_2(sK2,sK0,sK1) )
        & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1)
          | ( m1_connsp_2(X3,sK0,sK1)
            & m1_connsp_2(sK2,sK0,sK1) ) )
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
        | ~ m1_connsp_2(sK3,sK0,sK1)
        | ~ m1_connsp_2(sK2,sK0,sK1) )
      & ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
        | ( m1_connsp_2(sK3,sK0,sK1)
          & m1_connsp_2(sK2,sK0,sK1) ) )
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_connsp_2(X2,X0,X1) )
                  & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ~ m1_connsp_2(X3,X0,X1)
                    | ~ m1_connsp_2(X2,X0,X1) )
                  & ( m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)
                    | ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) ) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                    <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_connsp_2)).

fof(f90,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f33,f88])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f34,f84])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f35,f80])).

fof(f35,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f36,f76])).

fof(f36,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f37,f72])).

fof(f37,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f70,plain,
    ( spl5_1
    | spl5_3 ),
    inference(avatar_split_clause,[],[f38,f63,f57])).

fof(f38,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,
    ( spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f39,f63,f60])).

fof(f39,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | m1_connsp_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f65,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f40,f63,f60,f57])).

fof(f40,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | ~ m1_connsp_2(sK3,sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 15:15:45 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.21/0.46  % (16186)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.46  % (16178)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (16176)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (16185)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (16193)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (16194)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (16177)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (16172)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (16181)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (16172)Refutation not found, incomplete strategy% (16172)------------------------------
% 0.21/0.49  % (16172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (16172)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (16172)Memory used [KB]: 10618
% 0.21/0.49  % (16172)Time elapsed: 0.083 s
% 0.21/0.49  % (16172)------------------------------
% 0.21/0.49  % (16172)------------------------------
% 0.21/0.49  % (16183)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (16194)Refutation not found, incomplete strategy% (16194)------------------------------
% 0.21/0.49  % (16194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (16175)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (16189)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (16194)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (16194)Memory used [KB]: 10618
% 0.21/0.50  % (16194)Time elapsed: 0.083 s
% 0.21/0.50  % (16194)------------------------------
% 0.21/0.50  % (16194)------------------------------
% 0.21/0.50  % (16173)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (16171)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (16174)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (16180)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (16182)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (16179)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (16190)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (16187)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  % (16192)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.53  % (16177)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f1580,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f65,f68,f70,f74,f78,f82,f86,f90,f94,f102,f255,f274,f278,f283,f289,f316,f326,f449,f660,f1133,f1184,f1192,f1279,f1487,f1500,f1566,f1575,f1578])).
% 0.21/0.53  fof(f1578,plain,(
% 0.21/0.53    ~spl5_4 | spl5_2 | ~spl5_17 | ~spl5_6 | ~spl5_21 | ~spl5_113),
% 0.21/0.53    inference(avatar_split_clause,[],[f1356,f1277,f324,f80,f292,f60,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    spl5_4 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    spl5_2 <=> m1_connsp_2(sK3,sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    spl5_17 <=> r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    spl5_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    spl5_21 <=> ! [X1,X0] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | m1_connsp_2(X1,sK0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.53  fof(f1277,plain,(
% 0.21/0.53    spl5_113 <=> k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_113])])).
% 0.21/0.53  fof(f1356,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) | m1_connsp_2(sK3,sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_6 | ~spl5_21 | ~spl5_113)),
% 0.21/0.53    inference(resolution,[],[f1282,f361])).
% 0.21/0.53  fof(f361,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(sK1,k1_tops_1(sK0,X0)) | m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_6 | ~spl5_21)),
% 0.21/0.53    inference(resolution,[],[f325,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl5_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f80])).
% 0.21/0.53  fof(f325,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(X1,sK0,X0) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f324])).
% 0.21/0.53  fof(f1282,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(X0,k1_tops_1(sK0,sK3)) | ~r2_hidden(X0,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))) ) | ~spl5_113),
% 0.21/0.53    inference(superposition,[],[f54,f1278])).
% 0.21/0.53  fof(f1278,plain,(
% 0.21/0.53    k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) | ~spl5_113),
% 0.21/0.53    inference(avatar_component_clause,[],[f1277])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X1) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f29,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | ~r2_hidden(sK4(X0,X1,X2),X2)) & ((r2_hidden(sK4(X0,X1,X2),X1) & r2_hidden(sK4(X0,X1,X2),X0)) | r2_hidden(sK4(X0,X1,X2),X2))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(rectify,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : ((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(flattening,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((k3_xboole_0(X0,X1) = X2 | ? [X3] : (((~r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k3_xboole_0(X0,X1) != X2))),
% 0.21/0.53    inference(nnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.53  fof(f1575,plain,(
% 0.21/0.53    ~spl5_14 | spl5_10 | ~spl5_6 | ~spl5_17 | ~spl5_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f363,f324,f292,f80,f100,f269])).
% 0.21/0.53  fof(f269,plain,(
% 0.21/0.53    spl5_14 <=> m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    spl5_10 <=> m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.53  fof(f363,plain,(
% 0.21/0.53    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_6 | ~spl5_17 | ~spl5_21)),
% 0.21/0.53    inference(resolution,[],[f361,f293])).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) | ~spl5_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f292])).
% 0.21/0.53  fof(f1566,plain,(
% 0.21/0.53    spl5_17 | ~spl5_19),
% 0.21/0.53    inference(avatar_split_clause,[],[f393,f314,f292])).
% 0.21/0.53  fof(f314,plain,(
% 0.21/0.53    spl5_19 <=> r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,k3_xboole_0(sK2,sK3)),k3_xboole_0(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)),k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.53  fof(f393,plain,(
% 0.21/0.53    r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) | ~spl5_19),
% 0.21/0.53    inference(resolution,[],[f315,f55])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,k3_xboole_0(X0,X1)) | r2_hidden(X4,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X0) | ~r2_hidden(X4,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f315,plain,(
% 0.21/0.53    r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,k3_xboole_0(sK2,sK3)),k3_xboole_0(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)),k1_tops_1(sK0,k3_xboole_0(sK2,sK3))))) | ~spl5_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f314])).
% 0.21/0.53  fof(f1500,plain,(
% 0.21/0.53    ~spl5_5 | spl5_1 | ~spl5_17 | ~spl5_6 | ~spl5_21 | ~spl5_113),
% 0.21/0.53    inference(avatar_split_clause,[],[f1374,f1277,f324,f80,f292,f57,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    spl5_5 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    spl5_1 <=> m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.53  fof(f1374,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) | m1_connsp_2(sK2,sK0,sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_6 | ~spl5_21 | ~spl5_113)),
% 0.21/0.53    inference(resolution,[],[f1283,f361])).
% 0.21/0.53  fof(f1283,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(X1,k1_tops_1(sK0,sK2)) | ~r2_hidden(X1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))) ) | ~spl5_113),
% 0.21/0.53    inference(superposition,[],[f55,f1278])).
% 0.21/0.53  fof(f1487,plain,(
% 0.21/0.53    ~spl5_5 | spl5_17 | ~spl5_1 | ~spl5_104 | ~spl5_113),
% 0.21/0.53    inference(avatar_split_clause,[],[f1486,f1277,f1182,f57,f292,f76])).
% 0.21/0.53  fof(f1182,plain,(
% 0.21/0.53    spl5_104 <=> ! [X0] : (r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).
% 0.21/0.53  fof(f1486,plain,(
% 0.21/0.53    r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl5_1 | ~spl5_104 | ~spl5_113)),
% 0.21/0.53    inference(forward_demodulation,[],[f1480,f1278])).
% 0.21/0.53  fof(f1480,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))) | (~spl5_1 | ~spl5_104)),
% 0.21/0.53    inference(resolution,[],[f1183,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    m1_connsp_2(sK2,sK0,sK1) | ~spl5_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f57])).
% 0.21/0.53  fof(f1183,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3)))) ) | ~spl5_104),
% 0.21/0.53    inference(avatar_component_clause,[],[f1182])).
% 0.21/0.53  fof(f1279,plain,(
% 0.21/0.53    spl5_113 | ~spl5_5 | ~spl5_92),
% 0.21/0.53    inference(avatar_split_clause,[],[f1243,f1131,f76,f1277])).
% 0.21/0.53  fof(f1131,plain,(
% 0.21/0.53    spl5_92 <=> ! [X0] : (k3_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k3_xboole_0(X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).
% 0.21/0.53  fof(f1243,plain,(
% 0.21/0.53    k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) | (~spl5_5 | ~spl5_92)),
% 0.21/0.53    inference(resolution,[],[f1132,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f76])).
% 0.21/0.53  fof(f1132,plain,(
% 0.21/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k3_xboole_0(X0,sK3))) ) | ~spl5_92),
% 0.21/0.53    inference(avatar_component_clause,[],[f1131])).
% 0.21/0.53  fof(f1192,plain,(
% 0.21/0.53    ~spl5_4 | ~spl5_10 | spl5_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f1190,f63,f100,f72])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl5_3 <=> m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.53  fof(f1190,plain,(
% 0.21/0.53    ~m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_3),
% 0.21/0.53    inference(superposition,[],[f64,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | spl5_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f63])).
% 0.21/0.53  fof(f1184,plain,(
% 0.21/0.53    ~spl5_4 | spl5_104 | ~spl5_2 | ~spl5_6 | ~spl5_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f1176,f253,f80,f60,f1182,f72])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    spl5_11 <=> ! [X1,X0] : (~m1_connsp_2(X0,sK0,X1) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.53  fof(f1176,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_6 | ~spl5_11)),
% 0.21/0.53    inference(resolution,[],[f66,f258])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,sK1) | r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,X1),k1_tops_1(sK0,X0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_6 | ~spl5_11)),
% 0.21/0.53    inference(resolution,[],[f257,f256])).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    ( ! [X0] : (r2_hidden(sK1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_6 | ~spl5_11)),
% 0.21/0.53    inference(resolution,[],[f254,f81])).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f253])).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK1,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k3_xboole_0(X1,k1_tops_1(sK0,X0))) | ~m1_connsp_2(X0,sK0,sK1)) ) | (~spl5_6 | ~spl5_11)),
% 0.21/0.53    inference(resolution,[],[f256,f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X4,X0,X1] : (~r2_hidden(X4,X1) | r2_hidden(X4,k3_xboole_0(X0,X1)) | ~r2_hidden(X4,X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,X0) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    m1_connsp_2(sK3,sK0,sK1) | ~spl5_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f60])).
% 0.21/0.53  fof(f1133,plain,(
% 0.21/0.53    ~spl5_4 | spl5_92 | ~spl5_4 | ~spl5_33 | ~spl5_60),
% 0.21/0.53    inference(avatar_split_clause,[],[f1111,f658,f447,f72,f1131,f72])).
% 0.21/0.53  fof(f447,plain,(
% 0.21/0.53    spl5_33 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 0.21/0.53  fof(f658,plain,(
% 0.21/0.53    spl5_60 <=> ! [X1,X0] : (m1_subset_1(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 0.21/0.53  fof(f1111,plain,(
% 0.21/0.53    ( ! [X0] : (k3_xboole_0(k1_tops_1(sK0,X0),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k3_xboole_0(X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_4 | ~spl5_33 | ~spl5_60)),
% 0.21/0.53    inference(superposition,[],[f698,f46])).
% 0.21/0.53  fof(f698,plain,(
% 0.21/0.53    ( ! [X20] : (k3_xboole_0(k1_tops_1(sK0,X20),k1_tops_1(sK0,sK3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X20,sK3)) | ~m1_subset_1(X20,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_4 | ~spl5_33 | ~spl5_60)),
% 0.21/0.53    inference(resolution,[],[f689,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f72])).
% 0.21/0.53  fof(f689,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k3_xboole_0(k1_tops_1(sK0,X2),k1_tops_1(sK0,X3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X2,X3)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_33 | ~spl5_60)),
% 0.21/0.53    inference(subsumption_resolution,[],[f574,f686])).
% 0.21/0.53  fof(f686,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_60),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f682])).
% 0.21/0.53  fof(f682,plain,(
% 0.21/0.53    ( ! [X0] : (m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_60),
% 0.21/0.53    inference(superposition,[],[f680,f149])).
% 0.21/0.53  fof(f149,plain,(
% 0.21/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0 | k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.53    inference(resolution,[],[f134,f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.53    inference(factoring,[],[f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,X0),X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.53    inference(global_subsumption,[],[f106,f133])).
% 0.21/0.53  fof(f133,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,X0),X1) | ~r2_hidden(sK4(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f126])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1,X0),X1) | ~r2_hidden(sK4(X0,X1,X0),X0) | k3_xboole_0(X0,X1) = X0 | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.53    inference(resolution,[],[f52,f106])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f680,plain,(
% 0.21/0.53    ( ! [X2,X3] : (m1_subset_1(k1_tops_1(sK0,k3_xboole_0(X2,X3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_60),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f679])).
% 0.21/0.53  fof(f679,plain,(
% 0.21/0.53    ( ! [X2,X3] : (m1_subset_1(k1_tops_1(sK0,k3_xboole_0(X2,X3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_60),
% 0.21/0.53    inference(superposition,[],[f659,f46])).
% 0.21/0.53  fof(f659,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_60),
% 0.21/0.53    inference(avatar_component_clause,[],[f658])).
% 0.21/0.53  fof(f574,plain,(
% 0.21/0.53    ( ! [X2,X3] : (k3_xboole_0(k1_tops_1(sK0,X2),k1_tops_1(sK0,X3)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_tops_1(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_33),
% 0.21/0.53    inference(superposition,[],[f448,f46])).
% 0.21/0.53  fof(f448,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_33),
% 0.21/0.53    inference(avatar_component_clause,[],[f447])).
% 0.21/0.53  fof(f660,plain,(
% 0.21/0.53    ~spl5_7 | spl5_60 | ~spl5_33),
% 0.21/0.53    inference(avatar_split_clause,[],[f656,f447,f658,f84])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    spl5_7 <=> l1_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.53  fof(f656,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl5_33),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f655])).
% 0.21/0.53  fof(f655,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X0,X1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl5_33),
% 0.21/0.53    inference(resolution,[],[f576,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.21/0.53  fof(f576,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~m1_subset_1(k1_tops_1(sK0,X3),k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X2,X3)),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl5_33),
% 0.21/0.53    inference(superposition,[],[f45,f448])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 0.21/0.53  fof(f449,plain,(
% 0.21/0.53    ~spl5_7 | spl5_33 | ~spl5_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f445,f88,f447,f84])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    spl5_8 <=> v2_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.53  fof(f445,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,X1),k1_tops_1(sK0,X0)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),X1,X0))) ) | ~spl5_8),
% 0.21/0.53    inference(resolution,[],[f43,f89])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    v2_pre_topc(sK0) | ~spl5_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f88])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tops_1)).
% 0.21/0.53  fof(f326,plain,(
% 0.21/0.53    ~spl5_8 | ~spl5_7 | spl5_21 | spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f322,f92,f324,f84,f88])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    spl5_9 <=> v2_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.53  fof(f322,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | m1_connsp_2(X1,sK0,X0)) ) | spl5_9),
% 0.21/0.53    inference(resolution,[],[f42,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    ~v2_struct_0(sK0) | spl5_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f92])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_connsp_2(X2,X0,X1) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f11])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.53  fof(f316,plain,(
% 0.21/0.53    spl5_19 | ~spl5_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f303,f287,f314])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    spl5_16 <=> r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)),k1_tops_1(sK0,k3_xboole_0(sK2,sK3))))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.53  fof(f303,plain,(
% 0.21/0.53    r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,k3_xboole_0(sK2,sK3)),k3_xboole_0(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)),k1_tops_1(sK0,k3_xboole_0(sK2,sK3))))) | ~spl5_16),
% 0.21/0.53    inference(resolution,[],[f288,f209])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | r2_hidden(X2,k3_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 0.21/0.53    inference(superposition,[],[f54,f194])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X8,k3_xboole_0(X7,X8)))) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f190])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X8,k3_xboole_0(X7,X8))) | k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X8,k3_xboole_0(X7,X8)))) )),
% 0.21/0.53    inference(resolution,[],[f145,f108])).
% 0.21/0.53  fof(f108,plain,(
% 0.21/0.53    ( ! [X4,X5,X3] : (r2_hidden(sK4(k3_xboole_0(X3,X4),X5,k3_xboole_0(X3,X4)),X4) | k3_xboole_0(X3,X4) = k3_xboole_0(k3_xboole_0(X3,X4),X5)) )),
% 0.21/0.53    inference(resolution,[],[f106,f54])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~r2_hidden(sK4(X4,k3_xboole_0(X5,X4),X4),X5) | k3_xboole_0(X4,k3_xboole_0(X5,X4)) = X4) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f140])).
% 0.21/0.53  fof(f140,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k3_xboole_0(X4,k3_xboole_0(X5,X4)) = X4 | k3_xboole_0(X4,k3_xboole_0(X5,X4)) = X4 | ~r2_hidden(sK4(X4,k3_xboole_0(X5,X4),X4),X5)) )),
% 0.21/0.53    inference(resolution,[],[f134,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    ( ! [X6,X8,X7] : (r2_hidden(sK4(X6,X7,X6),k3_xboole_0(X8,X6)) | k3_xboole_0(X6,X7) = X6 | ~r2_hidden(sK4(X6,X7,X6),X8)) )),
% 0.21/0.53    inference(resolution,[],[f106,f53])).
% 0.21/0.53  fof(f288,plain,(
% 0.21/0.53    r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)),k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))) | ~spl5_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f287])).
% 0.21/0.53  fof(f289,plain,(
% 0.21/0.53    spl5_16 | ~spl5_12 | ~spl5_3 | ~spl5_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f284,f272,f63,f262,f287])).
% 0.21/0.53  fof(f262,plain,(
% 0.21/0.53    spl5_12 <=> m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    spl5_15 <=> ! [X1] : (r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,X1),k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X1,sK0,sK1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.53  fof(f284,plain,(
% 0.21/0.53    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK2,sK3)),k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))) | (~spl5_3 | ~spl5_15)),
% 0.21/0.53    inference(resolution,[],[f273,f67])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | ~spl5_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f63])).
% 0.21/0.53  fof(f273,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_connsp_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,X1),k1_tops_1(sK0,k3_xboole_0(sK2,sK3))))) ) | ~spl5_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f272])).
% 0.21/0.53  fof(f283,plain,(
% 0.21/0.53    ~spl5_4 | ~spl5_14 | spl5_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f281,f262,f269,f72])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_12),
% 0.21/0.53    inference(superposition,[],[f263,f46])).
% 0.21/0.53  fof(f263,plain,(
% 0.21/0.53    ~m1_subset_1(k9_subset_1(u1_struct_0(sK0),sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f262])).
% 0.21/0.53  fof(f278,plain,(
% 0.21/0.53    ~spl5_5 | spl5_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f275,f269,f76])).
% 0.21/0.53  fof(f275,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_14),
% 0.21/0.53    inference(resolution,[],[f270,f169])).
% 0.21/0.53  fof(f169,plain,(
% 0.21/0.53    ( ! [X8,X7,X9] : (m1_subset_1(k3_xboole_0(X7,X8),k1_zfmisc_1(X9)) | ~m1_subset_1(X7,k1_zfmisc_1(X9))) )),
% 0.21/0.53    inference(superposition,[],[f97,f144])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ( ! [X6,X7] : (k3_xboole_0(X6,X7) = k3_xboole_0(k3_xboole_0(X6,X7),X6)) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f141])).
% 0.21/0.53  fof(f141,plain,(
% 0.21/0.53    ( ! [X6,X7] : (k3_xboole_0(X6,X7) = k3_xboole_0(k3_xboole_0(X6,X7),X6) | k3_xboole_0(X6,X7) = k3_xboole_0(k3_xboole_0(X6,X7),X6)) )),
% 0.21/0.53    inference(resolution,[],[f134,f107])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(sK4(k3_xboole_0(X0,X1),X2,k3_xboole_0(X0,X1)),X0) | k3_xboole_0(X0,X1) = k3_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.53    inference(resolution,[],[f106,f55])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f96])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k3_xboole_0(X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.21/0.53    inference(superposition,[],[f45,f46])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | spl5_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f269])).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    ~spl5_14 | spl5_15 | ~spl5_6 | ~spl5_10 | ~spl5_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f260,f253,f100,f80,f272,f269])).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,X1),k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))) | ~m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_6 | ~spl5_10 | ~spl5_11)),
% 0.21/0.53    inference(resolution,[],[f258,f101])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~spl5_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f100])).
% 0.21/0.53  fof(f255,plain,(
% 0.21/0.53    ~spl5_8 | ~spl5_7 | spl5_11 | spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f249,f92,f253,f84,f88])).
% 0.21/0.53  fof(f249,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_connsp_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | r2_hidden(X1,k1_tops_1(sK0,X0))) ) | spl5_9),
% 0.21/0.53    inference(resolution,[],[f41,f93])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ~spl5_4 | spl5_10 | ~spl5_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f95,f63,f100,f72])).
% 0.21/0.53  fof(f95,plain,(
% 0.21/0.53    m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_3),
% 0.21/0.53    inference(superposition,[],[f67,f46])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    ~spl5_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f32,f92])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ((((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | ~m1_connsp_2(sK3,sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | (m1_connsp_2(sK3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f24,f23,f22,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | ~m1_connsp_2(X3,X0,X1) | ~m1_connsp_2(X2,X0,X1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) | ~m1_connsp_2(X3,sK0,X1) | ~m1_connsp_2(X2,sK0,X1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) | (m1_connsp_2(X3,sK0,X1) & m1_connsp_2(X2,sK0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) | ~m1_connsp_2(X3,sK0,X1) | ~m1_connsp_2(X2,sK0,X1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,X1) | (m1_connsp_2(X3,sK0,X1) & m1_connsp_2(X2,sK0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,u1_struct_0(sK0))) => (? [X2] : (? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_connsp_2(X2,sK0,sK1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) | (m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(X2,sK0,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ? [X2] : (? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_connsp_2(X2,sK0,sK1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),X2,X3),sK0,sK1) | (m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(X2,sK0,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) | (m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) | ~m1_connsp_2(X3,sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,X3),sK0,sK1) | (m1_connsp_2(X3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) => ((~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | ~m1_connsp_2(sK3,sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | (m1_connsp_2(sK3,sK0,sK1) & m1_connsp_2(sK2,sK0,sK1))) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | ~m1_connsp_2(X3,X0,X1) | ~m1_connsp_2(X2,X0,X1)) & (m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | (~m1_connsp_2(X3,X0,X1) | ~m1_connsp_2(X2,X0,X1))) & (m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) | (m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)))) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f9])).
% 0.21/0.53  fof(f9,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f7])).
% 0.21/0.53  fof(f7,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((m1_connsp_2(X3,X0,X1) & m1_connsp_2(X2,X0,X1)) <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_connsp_2)).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    spl5_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f88])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl5_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f34,f84])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl5_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f35,f80])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    spl5_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f36,f76])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    spl5_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f37,f72])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    spl5_1 | spl5_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f38,f63,f57])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    spl5_2 | spl5_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f39,f63,f60])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | m1_connsp_2(sK3,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ~spl5_1 | ~spl5_2 | ~spl5_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f40,f63,f60,f57])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ~m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) | ~m1_connsp_2(sK3,sK0,sK1) | ~m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (16177)------------------------------
% 0.21/0.53  % (16177)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (16177)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (16177)Memory used [KB]: 12025
% 0.21/0.53  % (16177)Time elapsed: 0.114 s
% 0.21/0.53  % (16177)------------------------------
% 0.21/0.53  % (16177)------------------------------
% 0.21/0.53  % (16165)Success in time 0.179 s
%------------------------------------------------------------------------------
