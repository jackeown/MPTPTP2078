%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1465+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:57 EST 2020

% Result     : Theorem 2.31s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 468 expanded)
%              Number of leaves         :   46 ( 262 expanded)
%              Depth                    :   11
%              Number of atoms          :  981 (3754 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :   28 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f283,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f136,f141,f146,f152,f158,f164,f170,f176,f182,f188,f194,f200,f217,f222,f237,f239,f265,f278,f280,f282])).

fof(f282,plain,
    ( ~ spl5_20
    | ~ spl5_22
    | ~ spl5_23
    | spl5_15
    | ~ spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_26
    | ~ spl5_25
    | spl5_30 ),
    inference(avatar_split_clause,[],[f281,f275,f214,f219,f98,f93,f103,f108,f113,f118,f123,f128,f133,f138,f143,f191,f185,f173])).

fof(f173,plain,
    ( spl5_20
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f185,plain,
    ( spl5_22
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f191,plain,
    ( spl5_23
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f143,plain,
    ( spl5_15
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f138,plain,
    ( spl5_14
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f133,plain,
    ( spl5_13
  <=> v3_filter_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f128,plain,
    ( spl5_12
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f123,plain,
    ( spl5_11
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f118,plain,
    ( spl5_10
  <=> v19_lattices(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f113,plain,
    ( spl5_9
  <=> v20_lattices(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f108,plain,
    ( spl5_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f103,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f93,plain,
    ( spl5_5
  <=> m1_subset_1(sK4,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f98,plain,
    ( spl5_6
  <=> m1_subset_1(sK3,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f219,plain,
    ( spl5_26
  <=> r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f214,plain,
    ( spl5_25
  <=> r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f275,plain,
    ( spl5_30
  <=> r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f281,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | ~ r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | spl5_30 ),
    inference(resolution,[],[f277,f250])).

fof(f250,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X3),X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X3,X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X2,X1),X4)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X4,X0)
      | ~ v19_lattices(X4,X0)
      | v1_xboole_0(X4)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X3),X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X3,X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X2,X1),X4)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X4,X0)
      | ~ v19_lattices(X4,X0)
      | v1_xboole_0(X4)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f68,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k4_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k4_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_lattices)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X4),k4_lattices(X0,X3,X5)),X1)
      | ~ r2_hidden(k7_filter_0(X0,X4,X5),X1)
      | ~ r2_hidden(k7_filter_0(X0,X2,X3),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X4),k4_lattices(X0,X3,X5)),X1)
                            & r2_hidden(k7_filter_0(X0,k3_lattices(X0,X2,X4),k3_lattices(X0,X3,X5)),X1) )
                          | ~ r2_hidden(k7_filter_0(X0,X4,X5),X1)
                          | ~ r2_hidden(k7_filter_0(X0,X2,X3),X1)
                          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v20_lattices(X1,X0)
          | ~ v19_lattices(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X4),k4_lattices(X0,X3,X5)),X1)
                            & r2_hidden(k7_filter_0(X0,k3_lattices(X0,X2,X4),k3_lattices(X0,X3,X5)),X1) )
                          | ~ r2_hidden(k7_filter_0(X0,X4,X5),X1)
                          | ~ r2_hidden(k7_filter_0(X0,X2,X3),X1)
                          | ~ m1_subset_1(X5,u1_struct_0(X0)) )
                      | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v20_lattices(X1,X0)
          | ~ v19_lattices(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v3_filter_0(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v20_lattices(X1,X0)
            & v19_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ! [X5] :
                          ( m1_subset_1(X5,u1_struct_0(X0))
                         => ( ( r2_hidden(k7_filter_0(X0,X4,X5),X1)
                              & r2_hidden(k7_filter_0(X0,X2,X3),X1) )
                           => ( r2_hidden(k7_filter_0(X0,k4_lattices(X0,X2,X4),k4_lattices(X0,X3,X5)),X1)
                              & r2_hidden(k7_filter_0(X0,k3_lattices(X0,X2,X4),k3_lattices(X0,X3,X5)),X1) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_filter_1)).

fof(f277,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f275])).

fof(f280,plain,
    ( spl5_15
    | ~ spl5_20
    | ~ spl5_16
    | ~ spl5_7
    | ~ spl5_5
    | spl5_29 ),
    inference(avatar_split_clause,[],[f279,f271,f93,f103,f149,f173,f143])).

fof(f149,plain,
    ( spl5_16
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f271,plain,
    ( spl5_29
  <=> m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f279,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | spl5_29 ),
    inference(resolution,[],[f273,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f273,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | spl5_29 ),
    inference(avatar_component_clause,[],[f271])).

fof(f278,plain,
    ( spl5_15
    | ~ spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_29
    | ~ spl5_6
    | ~ spl5_30
    | spl5_2 ),
    inference(avatar_split_clause,[],[f269,f78,f275,f98,f271,f108,f113,f118,f123,f128,f133,f138,f143])).

fof(f78,plain,
    ( spl5_2
  <=> r2_hidden(k4_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f269,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k4_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(k4_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl5_2 ),
    inference(resolution,[],[f80,f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
      | ~ r2_hidden(k7_filter_0(X0,X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                      | ~ r2_hidden(k7_filter_0(X0,X2,X3),X1) )
                    & ( r2_hidden(k7_filter_0(X0,X2,X3),X1)
                      | ~ r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) ) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v20_lattices(X1,X0)
          | ~ v19_lattices(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                  <=> r2_hidden(k7_filter_0(X0,X2,X3),X1) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v20_lattices(X1,X0)
          | ~ v19_lattices(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                  <=> r2_hidden(k7_filter_0(X0,X2,X3),X1) )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v20_lattices(X1,X0)
          | ~ v19_lattices(X1,X0)
          | v1_xboole_0(X1) )
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v3_filter_0(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v20_lattices(X1,X0)
            & v19_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ( r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                  <=> r2_hidden(k7_filter_0(X0,X2,X3),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l72_filter_1)).

fof(f80,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f265,plain,
    ( ~ spl5_20
    | ~ spl5_22
    | ~ spl5_23
    | ~ spl5_18
    | spl5_15
    | ~ spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_5
    | ~ spl5_6
    | ~ spl5_26
    | ~ spl5_25
    | spl5_28 ),
    inference(avatar_split_clause,[],[f260,f234,f214,f219,f98,f93,f103,f108,f113,f118,f123,f128,f133,f138,f143,f161,f191,f185,f173])).

fof(f161,plain,
    ( spl5_18
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f234,plain,
    ( spl5_28
  <=> r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f260,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | ~ r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ v4_lattices(sK0)
    | ~ v9_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | spl5_28 ),
    inference(resolution,[],[f244,f236])).

fof(f236,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | spl5_28 ),
    inference(avatar_component_clause,[],[f234])).

fof(f244,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k7_filter_0(X0,k3_lattices(X0,X2,X3),X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X3,X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X2,X1),X4)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X4,X0)
      | ~ v19_lattices(X4,X0)
      | v1_xboole_0(X4)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ v4_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f243])).

fof(f243,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k7_filter_0(X0,k3_lattices(X0,X2,X3),X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X3,X1),X4)
      | ~ r2_hidden(k7_filter_0(X0,X2,X1),X4)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X4,X0)
      | ~ v19_lattices(X4,X0)
      | v1_xboole_0(X4)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0) ) ),
    inference(superposition,[],[f67,f208])).

fof(f208,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0) ) ),
    inference(global_subsumption,[],[f55,f207])).

fof(f207,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f71,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_lattices(X0,X1,X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_lattices(X0,X1,X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k1_lattices(X0,X1,X1) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattices)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f55,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( r2_hidden(k7_filter_0(X0,k3_lattices(X0,X2,X4),k3_lattices(X0,X3,X5)),X1)
      | ~ r2_hidden(k7_filter_0(X0,X4,X5),X1)
      | ~ r2_hidden(k7_filter_0(X0,X2,X3),X1)
      | ~ m1_subset_1(X5,u1_struct_0(X0))
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f239,plain,
    ( spl5_15
    | ~ spl5_18
    | ~ spl5_17
    | ~ spl5_7
    | ~ spl5_5
    | spl5_27 ),
    inference(avatar_split_clause,[],[f238,f230,f93,f103,f155,f161,f143])).

fof(f155,plain,
    ( spl5_17
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f230,plain,
    ( spl5_27
  <=> m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f238,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ l2_lattices(sK0)
    | ~ v4_lattices(sK0)
    | v2_struct_0(sK0)
    | spl5_27 ),
    inference(resolution,[],[f232,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k3_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_lattices)).

fof(f232,plain,
    ( ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | spl5_27 ),
    inference(avatar_component_clause,[],[f230])).

fof(f237,plain,
    ( spl5_15
    | ~ spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_27
    | ~ spl5_6
    | ~ spl5_28
    | spl5_1 ),
    inference(avatar_split_clause,[],[f227,f74,f234,f98,f230,f108,f113,f118,f123,f128,f133,f138,f143])).

fof(f74,plain,
    ( spl5_1
  <=> r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f227,plain,
    ( ~ r2_hidden(k7_filter_0(sK0,k3_lattices(sK0,sK2,sK4),sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_lattices(sK0,sK2,sK4),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | spl5_1 ),
    inference(resolution,[],[f66,f76])).

fof(f76,plain,
    ( ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f222,plain,
    ( spl5_15
    | ~ spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_6
    | spl5_26
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f212,f88,f219,f98,f103,f108,f113,f118,f123,f128,f133,f138,f143])).

fof(f88,plain,
    ( spl5_4
  <=> r2_hidden(sK2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f212,plain,
    ( r2_hidden(k7_filter_0(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4 ),
    inference(resolution,[],[f65,f90])).

fof(f90,plain,
    ( r2_hidden(sK2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
      | r2_hidden(k7_filter_0(X0,X2,X3),X1)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v20_lattices(X1,X0)
      | ~ v19_lattices(X1,X0)
      | v1_xboole_0(X1)
      | ~ l3_lattices(X0)
      | ~ v3_filter_0(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f217,plain,
    ( spl5_15
    | ~ spl5_14
    | ~ spl5_13
    | ~ spl5_12
    | spl5_11
    | ~ spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_5
    | ~ spl5_6
    | spl5_25
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f211,f83,f214,f98,f93,f108,f113,f118,f123,f128,f133,f138,f143])).

fof(f83,plain,
    ( spl5_3
  <=> r2_hidden(sK4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f211,plain,
    ( r2_hidden(k7_filter_0(sK0,sK4,sK3),sK1)
    | ~ m1_subset_1(sK3,u1_struct_0(sK0))
    | ~ m1_subset_1(sK4,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v20_lattices(sK1,sK0)
    | ~ v19_lattices(sK1,sK0)
    | v1_xboole_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v3_filter_0(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3 ),
    inference(resolution,[],[f65,f85])).

fof(f85,plain,
    ( r2_hidden(sK4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f200,plain,
    ( ~ spl5_24
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f195,f83,f197])).

fof(f197,plain,
    ( spl5_24
  <=> v1_xboole_0(k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f195,plain,
    ( ~ v1_xboole_0(k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
    | ~ spl5_3 ),
    inference(resolution,[],[f85,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

fof(f194,plain,
    ( ~ spl5_12
    | spl5_15
    | spl5_23
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f189,f138,f191,f143,f128])).

fof(f189,plain,
    ( v9_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl5_14 ),
    inference(resolution,[],[f62,f140])).

fof(f140,plain,
    ( v10_lattices(sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v9_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f188,plain,
    ( ~ spl5_12
    | spl5_15
    | spl5_22
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f183,f138,f185,f143,f128])).

fof(f183,plain,
    ( v8_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl5_14 ),
    inference(resolution,[],[f61,f140])).

fof(f61,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v8_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f182,plain,
    ( ~ spl5_12
    | spl5_15
    | spl5_21
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f177,f138,f179,f143,f128])).

fof(f179,plain,
    ( spl5_21
  <=> v7_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f177,plain,
    ( v7_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl5_14 ),
    inference(resolution,[],[f60,f140])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v7_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f176,plain,
    ( ~ spl5_12
    | spl5_15
    | spl5_20
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f171,f138,f173,f143,f128])).

fof(f171,plain,
    ( v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl5_14 ),
    inference(resolution,[],[f59,f140])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v6_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f170,plain,
    ( ~ spl5_12
    | spl5_15
    | spl5_19
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f165,f138,f167,f143,f128])).

fof(f167,plain,
    ( spl5_19
  <=> v5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f165,plain,
    ( v5_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl5_14 ),
    inference(resolution,[],[f58,f140])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v5_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f164,plain,
    ( ~ spl5_12
    | spl5_15
    | spl5_18
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f159,f138,f161,f143,f128])).

fof(f159,plain,
    ( v4_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | ~ spl5_14 ),
    inference(resolution,[],[f57,f140])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v10_lattices(X0)
      | v4_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f158,plain,
    ( spl5_17
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f153,f128,f155])).

fof(f153,plain,
    ( l2_lattices(sK0)
    | ~ spl5_12 ),
    inference(resolution,[],[f55,f130])).

fof(f130,plain,
    ( l3_lattices(sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f128])).

fof(f152,plain,
    ( spl5_16
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f147,f128,f149])).

fof(f147,plain,
    ( l1_lattices(sK0)
    | ~ spl5_12 ),
    inference(resolution,[],[f54,f130])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l3_lattices(X0)
      | l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f146,plain,(
    ~ spl5_15 ),
    inference(avatar_split_clause,[],[f40,f143])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

% (1582)Refutation not found, incomplete strategy% (1582)------------------------------
% (1582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (1582)Termination reason: Refutation not found, incomplete strategy

% (1582)Memory used [KB]: 6268
% (1582)Time elapsed: 0.259 s
% (1582)------------------------------
% (1582)------------------------------
fof(f38,plain,
    ( ( ~ r2_hidden(k4_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
      | ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) )
    & r2_hidden(sK4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
    & r2_hidden(sK2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
    & m1_subset_1(sK4,u1_struct_0(sK0))
    & m1_subset_1(sK3,u1_struct_0(sK0))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & v20_lattices(sK1,sK0)
    & v19_lattices(sK1,sK0)
    & ~ v1_xboole_0(sK1)
    & l3_lattices(sK0)
    & v3_filter_0(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f14,f37,f36,f35,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ( ~ r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                          | ~ r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
                        & r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                        & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                        & m1_subset_1(X4,u1_struct_0(X0)) )
                    & m1_subset_1(X3,u1_struct_0(X0)) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v20_lattices(X1,X0)
            & v19_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
        & l3_lattices(X0)
        & v3_filter_0(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r2_hidden(k4_lattices(sK0,X2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,X1),X3))
                        | ~ r2_hidden(k3_lattices(sK0,X2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,X1),X3)) )
                      & r2_hidden(X4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,X1),X3))
                      & r2_hidden(X2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,X1),X3))
                      & m1_subset_1(X4,u1_struct_0(sK0)) )
                  & m1_subset_1(X3,u1_struct_0(sK0)) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & v20_lattices(X1,sK0)
          & v19_lattices(X1,sK0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(sK0)
      & v3_filter_0(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ( ~ r2_hidden(k4_lattices(sK0,X2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,X1),X3))
                      | ~ r2_hidden(k3_lattices(sK0,X2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,X1),X3)) )
                    & r2_hidden(X4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,X1),X3))
                    & r2_hidden(X2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,X1),X3))
                    & m1_subset_1(X4,u1_struct_0(sK0)) )
                & m1_subset_1(X3,u1_struct_0(sK0)) )
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & v20_lattices(X1,sK0)
        & v19_lattices(X1,sK0)
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ( ~ r2_hidden(k4_lattices(sK0,X2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3))
                    | ~ r2_hidden(k3_lattices(sK0,X2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3)) )
                  & r2_hidden(X4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3))
                  & r2_hidden(X2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3))
                  & m1_subset_1(X4,u1_struct_0(sK0)) )
              & m1_subset_1(X3,u1_struct_0(sK0)) )
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & v20_lattices(sK1,sK0)
      & v19_lattices(sK1,sK0)
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ( ~ r2_hidden(k4_lattices(sK0,X2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3))
                  | ~ r2_hidden(k3_lattices(sK0,X2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3)) )
                & r2_hidden(X4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3))
                & r2_hidden(X2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3))
                & m1_subset_1(X4,u1_struct_0(sK0)) )
            & m1_subset_1(X3,u1_struct_0(sK0)) )
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ( ~ r2_hidden(k4_lattices(sK0,sK2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3))
                | ~ r2_hidden(k3_lattices(sK0,sK2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3)) )
              & r2_hidden(X4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3))
              & r2_hidden(sK2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3))
              & m1_subset_1(X4,u1_struct_0(sK0)) )
          & m1_subset_1(X3,u1_struct_0(sK0)) )
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ( ~ r2_hidden(k4_lattices(sK0,sK2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3))
              | ~ r2_hidden(k3_lattices(sK0,sK2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3)) )
            & r2_hidden(X4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3))
            & r2_hidden(sK2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),X3))
            & m1_subset_1(X4,u1_struct_0(sK0)) )
        & m1_subset_1(X3,u1_struct_0(sK0)) )
   => ( ? [X4] :
          ( ( ~ r2_hidden(k4_lattices(sK0,sK2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
            | ~ r2_hidden(k3_lattices(sK0,sK2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) )
          & r2_hidden(X4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
          & r2_hidden(sK2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
          & m1_subset_1(X4,u1_struct_0(sK0)) )
      & m1_subset_1(sK3,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X4] :
        ( ( ~ r2_hidden(k4_lattices(sK0,sK2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
          | ~ r2_hidden(k3_lattices(sK0,sK2,X4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) )
        & r2_hidden(X4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
        & r2_hidden(sK2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
        & m1_subset_1(X4,u1_struct_0(sK0)) )
   => ( ( ~ r2_hidden(k4_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
        | ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) )
      & r2_hidden(sK4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
      & r2_hidden(sK2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
      & m1_subset_1(sK4,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                        | ~ r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
                      & r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                      & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v20_lattices(X1,X0)
          & v19_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(X0)
      & v3_filter_0(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ( ~ r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                        | ~ r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
                      & r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                      & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                      & m1_subset_1(X4,u1_struct_0(X0)) )
                  & m1_subset_1(X3,u1_struct_0(X0)) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v20_lattices(X1,X0)
          & v19_lattices(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l3_lattices(X0)
      & v3_filter_0(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v3_filter_0(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v20_lattices(X1,X0)
              & v19_lattices(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ! [X4] :
                        ( m1_subset_1(X4,u1_struct_0(X0))
                       => ( ( r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                            & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
                         => ( r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                            & r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v3_filter_0(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v20_lattices(X1,X0)
            & v19_lattices(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,u1_struct_0(X0))
                 => ! [X4] :
                      ( m1_subset_1(X4,u1_struct_0(X0))
                     => ( ( r2_hidden(X4,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                          & r2_hidden(X2,k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) )
                       => ( r2_hidden(k4_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3))
                          & r2_hidden(k3_lattices(X0,X2,X4),k6_eqrel_1(u1_struct_0(X0),u1_struct_0(X0),k9_filter_0(X0,X1),X3)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_filter_1)).

fof(f141,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f41,f138])).

fof(f41,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f136,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f42,f133])).

fof(f42,plain,(
    v3_filter_0(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f131,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f43,f128])).

fof(f43,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f126,plain,(
    ~ spl5_11 ),
    inference(avatar_split_clause,[],[f44,f123])).

fof(f44,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f38])).

fof(f121,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f45,f118])).

fof(f45,plain,(
    v19_lattices(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f116,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f46,f113])).

fof(f46,plain,(
    v20_lattices(sK1,sK0) ),
    inference(cnf_transformation,[],[f38])).

fof(f111,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f47,f108])).

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f38])).

fof(f106,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f48,f103])).

fof(f48,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f101,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f49,f98])).

fof(f49,plain,(
    m1_subset_1(sK3,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f96,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f50,f93])).

fof(f50,plain,(
    m1_subset_1(sK4,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f38])).

fof(f91,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f51,f88])).

fof(f51,plain,(
    r2_hidden(sK2,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f86,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f52,f83])).

fof(f52,plain,(
    r2_hidden(sK4,k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(cnf_transformation,[],[f38])).

fof(f81,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f53,f78,f74])).

fof(f53,plain,
    ( ~ r2_hidden(k4_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3))
    | ~ r2_hidden(k3_lattices(sK0,sK2,sK4),k6_eqrel_1(u1_struct_0(sK0),u1_struct_0(sK0),k9_filter_0(sK0,sK1),sK3)) ),
    inference(cnf_transformation,[],[f38])).

%------------------------------------------------------------------------------
