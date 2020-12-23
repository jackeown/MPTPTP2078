%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 396 expanded)
%              Number of leaves         :   44 ( 211 expanded)
%              Depth                    :   10
%              Number of atoms          :  810 (2367 expanded)
%              Number of equality atoms :   85 ( 313 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f574,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f76,f80,f84,f88,f97,f106,f111,f117,f125,f133,f139,f150,f165,f175,f181,f196,f212,f277,f281,f286,f316,f320,f381,f428,f522,f531,f563,f572,f573])).

fof(f573,plain,
    ( sK1 != k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))
    | r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)),sK3(sK0,sK1,sK2)))
    | ~ r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f572,plain,
    ( spl4_10
    | ~ spl4_9
    | ~ spl4_8
    | ~ spl4_7
    | ~ spl4_6
    | ~ spl4_4
    | ~ spl4_5
    | spl4_12
    | ~ spl4_2
    | spl4_85 ),
    inference(avatar_split_clause,[],[f569,f561,f54,f101,f66,f62,f70,f74,f78,f82,f86])).

fof(f86,plain,
    ( spl4_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f82,plain,
    ( spl4_9
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f78,plain,
    ( spl4_8
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f74,plain,
    ( spl4_7
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f70,plain,
    ( spl4_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f62,plain,
    ( spl4_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f66,plain,
    ( spl4_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f101,plain,
    ( spl4_12
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f54,plain,
    ( spl4_2
  <=> m1_orders_2(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f561,plain,
    ( spl4_85
  <=> r2_hidden(sK3(sK0,sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).

fof(f569,plain,
    ( ~ m1_orders_2(sK1,sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl4_85 ),
    inference(resolution,[],[f562,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ( k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
                        & r2_hidden(sK3(X0,X1,X2),X1)
                        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).

fof(f22,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
        & r2_hidden(sK3(X0,X1,X2),X1)
        & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X4] :
                          ( k3_orders_2(X0,X1,X4) = X2
                          & r2_hidden(X4,X1)
                          & m1_subset_1(X4,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( ( m1_orders_2(X2,X0,X1)
                      | k1_xboole_0 != X2 )
                    & ( k1_xboole_0 = X2
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 != X1 )
                & ( ( ( m1_orders_2(X2,X0,X1)
                      | ! [X3] :
                          ( k3_orders_2(X0,X1,X3) != X2
                          | ~ r2_hidden(X3,X1)
                          | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
                    & ( ? [X3] :
                          ( k3_orders_2(X0,X1,X3) = X2
                          & r2_hidden(X3,X1)
                          & m1_subset_1(X3,u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 )
                  | k1_xboole_0 != X1 )
                & ( ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( k1_xboole_0 = X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> k1_xboole_0 = X2 ) )
                & ( k1_xboole_0 != X1
                 => ( m1_orders_2(X2,X0,X1)
                  <=> ? [X3] :
                        ( k3_orders_2(X0,X1,X3) = X2
                        & r2_hidden(X3,X1)
                        & m1_subset_1(X3,u1_struct_0(X0)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).

fof(f562,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | spl4_85 ),
    inference(avatar_component_clause,[],[f561])).

fof(f563,plain,
    ( ~ spl4_85
    | spl4_40
    | ~ spl4_80 ),
    inference(avatar_split_clause,[],[f556,f529,f251,f561])).

fof(f251,plain,
    ( spl4_40
  <=> r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f529,plain,
    ( spl4_80
  <=> sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).

fof(f556,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),sK2)
    | spl4_40
    | ~ spl4_80 ),
    inference(superposition,[],[f252,f530])).

fof(f530,plain,
    ( sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl4_80 ),
    inference(avatar_component_clause,[],[f529])).

fof(f252,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)))
    | spl4_40 ),
    inference(avatar_component_clause,[],[f251])).

fof(f531,plain,
    ( spl4_80
    | ~ spl4_4
    | ~ spl4_1
    | ~ spl4_45 ),
    inference(avatar_split_clause,[],[f469,f279,f50,f62,f529])).

fof(f50,plain,
    ( spl4_1
  <=> m1_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f279,plain,
    ( spl4_45
  <=> ! [X1] :
        ( k3_orders_2(sK0,sK1,sK3(sK0,sK1,X1)) = X1
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f469,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))
    | ~ spl4_1
    | ~ spl4_45 ),
    inference(resolution,[],[f280,f51])).

fof(f51,plain,
    ( m1_orders_2(sK2,sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f280,plain,
    ( ! [X1] :
        ( ~ m1_orders_2(X1,sK0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,sK1,sK3(sK0,sK1,X1)) = X1 )
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f279])).

fof(f522,plain,
    ( ~ spl4_5
    | spl4_3
    | ~ spl4_48
    | ~ spl4_68 ),
    inference(avatar_split_clause,[],[f520,f426,f314,f58,f66])).

fof(f58,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f314,plain,
    ( spl4_48
  <=> m1_orders_2(sK1,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f426,plain,
    ( spl4_68
  <=> ! [X0] :
        ( ~ m1_orders_2(X0,sK0,k1_xboole_0)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).

fof(f520,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_48
    | ~ spl4_68 ),
    inference(resolution,[],[f427,f315])).

fof(f315,plain,
    ( m1_orders_2(sK1,sK0,k1_xboole_0)
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f314])).

fof(f427,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,k1_xboole_0)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_68 ),
    inference(avatar_component_clause,[],[f426])).

fof(f428,plain,
    ( spl4_10
    | ~ spl4_9
    | ~ spl4_8
    | ~ spl4_7
    | ~ spl4_6
    | spl4_68
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f419,f318,f426,f70,f74,f78,f82,f86])).

fof(f318,plain,
    ( spl4_49
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f419,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_49 ),
    inference(resolution,[],[f319,f46])).

fof(f46,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X2
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f319,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f318])).

fof(f381,plain,
    ( sK1 != k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f320,plain,
    ( spl4_49
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f289,f101,f62,f318])).

fof(f289,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4
    | ~ spl4_12 ),
    inference(superposition,[],[f63,f102])).

fof(f102,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f316,plain,
    ( spl4_48
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f288,f101,f54,f314])).

fof(f288,plain,
    ( m1_orders_2(sK1,sK0,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(superposition,[],[f55,f102])).

fof(f55,plain,
    ( m1_orders_2(sK1,sK0,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f286,plain,
    ( spl4_46
    | ~ spl4_5
    | ~ spl4_2
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f282,f275,f54,f66,f284])).

fof(f284,plain,
    ( spl4_46
  <=> sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f275,plain,
    ( spl4_44
  <=> ! [X0] :
        ( k3_orders_2(sK0,sK2,sK3(sK0,sK2,X0)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X0,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f282,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))
    | ~ spl4_2
    | ~ spl4_44 ),
    inference(resolution,[],[f276,f55])).

fof(f276,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,sK2,sK3(sK0,sK2,X0)) = X0 )
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f275])).

fof(f281,plain,
    ( spl4_3
    | spl4_45
    | ~ spl4_5
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f273,f210,f66,f279,f58])).

fof(f210,plain,
    ( spl4_33
  <=> ! [X1,X0] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k3_orders_2(sK0,X1,sK3(sK0,X1,X0)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f273,plain,
    ( ! [X1] :
        ( k3_orders_2(sK0,sK1,sK3(sK0,sK1,X1)) = X1
        | ~ m1_orders_2(X1,sK0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK1 )
    | ~ spl4_5
    | ~ spl4_33 ),
    inference(resolution,[],[f211,f67])).

fof(f67,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f211,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X1,sK3(sK0,X1,X0)) = X0
        | ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1 )
    | ~ spl4_33 ),
    inference(avatar_component_clause,[],[f210])).

fof(f277,plain,
    ( spl4_12
    | spl4_44
    | ~ spl4_4
    | ~ spl4_33 ),
    inference(avatar_split_clause,[],[f272,f210,f62,f275,f101])).

fof(f272,plain,
    ( ! [X0] :
        ( k3_orders_2(sK0,sK2,sK3(sK0,sK2,X0)) = X0
        | ~ m1_orders_2(X0,sK0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK2 )
    | ~ spl4_4
    | ~ spl4_33 ),
    inference(resolution,[],[f211,f63])).

fof(f212,plain,
    ( spl4_10
    | ~ spl4_9
    | ~ spl4_8
    | ~ spl4_7
    | spl4_33
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f208,f70,f210,f74,f78,f82,f86])).

fof(f208,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X1,sK3(sK0,X1,X0)) = X0
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f39,f71])).

fof(f71,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f70])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f196,plain,
    ( ~ spl4_29
    | ~ spl4_30
    | ~ spl4_15
    | ~ spl4_21
    | spl4_27 ),
    inference(avatar_split_clause,[],[f187,f179,f148,f114,f194,f191])).

fof(f191,plain,
    ( spl4_29
  <=> m1_subset_1(k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).

fof(f194,plain,
    ( spl4_30
  <=> r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)),sK3(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f114,plain,
    ( spl4_15
  <=> m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f148,plain,
    ( spl4_21
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X2,k3_orders_2(sK0,X3,sK3(sK0,sK1,sK2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r2_hidden(X2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f179,plain,
    ( spl4_27
  <=> r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f187,plain,
    ( ~ m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)),sK3(sK0,sK1,sK2)))
    | ~ m1_subset_1(k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_21
    | spl4_27 ),
    inference(resolution,[],[f180,f149])).

fof(f149,plain,
    ( ! [X2,X3] :
        ( r2_hidden(X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k3_orders_2(sK0,X3,sK3(sK0,sK1,sK2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f148])).

fof(f180,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)))
    | spl4_27 ),
    inference(avatar_component_clause,[],[f179])).

fof(f181,plain,
    ( ~ spl4_27
    | ~ spl4_4
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f176,f162,f62,f179])).

fof(f162,plain,
    ( spl4_24
  <=> ! [X0] :
        ( ~ r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,X0,sK3(sK0,sK2,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f176,plain,
    ( ~ r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)))
    | ~ spl4_4
    | ~ spl4_24 ),
    inference(resolution,[],[f163,f63])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,X0,sK3(sK0,sK2,sK1))) )
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f162])).

fof(f175,plain,
    ( spl4_24
    | ~ spl4_15
    | ~ spl4_16
    | spl4_23 ),
    inference(avatar_split_clause,[],[f174,f159,f123,f114,f162])).

fof(f123,plain,
    ( spl4_16
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,sK3(sK0,sK2,sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,X0,sK3(sK0,sK2,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f159,plain,
    ( spl4_23
  <=> r2_orders_2(sK0,sK3(sK0,sK2,sK1),sK3(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))
        | ~ r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,X0,sK3(sK0,sK2,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_16
    | spl4_23 ),
    inference(resolution,[],[f160,f124])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( r2_orders_2(sK0,X0,sK3(sK0,sK2,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,X1,sK3(sK0,sK2,sK1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f123])).

fof(f160,plain,
    ( ~ r2_orders_2(sK0,sK3(sK0,sK2,sK1),sK3(sK0,sK2,sK1))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f159])).

fof(f165,plain,
    ( ~ spl4_23
    | spl4_24
    | ~ spl4_15
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f157,f131,f123,f114,f162,f159])).

fof(f131,plain,
    ( spl4_18
  <=> ! [X4] :
        ( ~ r2_orders_2(sK0,X4,sK3(sK0,sK2,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,sK3(sK0,sK2,sK1),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))
        | ~ r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,X0,sK3(sK0,sK2,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,sK3(sK0,sK2,sK1),sK3(sK0,sK2,sK1)) )
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))
        | ~ r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,X0,sK3(sK0,sK2,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,sK3(sK0,sK2,sK1),sK3(sK0,sK2,sK1)) )
    | ~ spl4_16
    | ~ spl4_18 ),
    inference(resolution,[],[f124,f132])).

fof(f132,plain,
    ( ! [X4] :
        ( ~ r2_orders_2(sK0,sK3(sK0,sK2,sK1),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,X4,sK3(sK0,sK2,sK1)) )
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f131])).

fof(f150,plain,
    ( spl4_10
    | ~ spl4_9
    | ~ spl4_8
    | ~ spl4_7
    | ~ spl4_6
    | spl4_21
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f141,f136,f148,f70,f74,f78,f82,f86])).

fof(f136,plain,
    ( spl4_19
  <=> m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f141,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,k3_orders_2(sK0,X3,sK3(sK0,sK1,sK2)))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X2,X3)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_19 ),
    inference(resolution,[],[f137,f35])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,X3)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                      | ~ r2_hidden(X1,X3)
                      | ~ r2_orders_2(X0,X1,X2) )
                    & ( ( r2_hidden(X1,X3)
                        & r2_orders_2(X0,X1,X2) )
                      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2)) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( r2_hidden(X1,k3_orders_2(X0,X3,X2))
                  <=> ( r2_hidden(X1,X3)
                      & r2_orders_2(X0,X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).

fof(f137,plain,
    ( m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f136])).

fof(f139,plain,
    ( spl4_19
    | ~ spl4_4
    | ~ spl4_1
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f134,f109,f50,f62,f136])).

fof(f109,plain,
    ( spl4_14
  <=> ! [X1] :
        ( m1_subset_1(sK3(sK0,sK1,X1),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X1,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f134,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))
    | ~ spl4_1
    | ~ spl4_14 ),
    inference(resolution,[],[f110,f51])).

fof(f110,plain,
    ( ! [X1] :
        ( ~ m1_orders_2(X1,sK0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK3(sK0,sK1,X1),u1_struct_0(sK0)) )
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f109])).

fof(f133,plain,
    ( ~ spl4_7
    | ~ spl4_6
    | spl4_18
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f120,f114,f131,f70,f74])).

fof(f120,plain,
    ( ! [X4] :
        ( ~ r2_orders_2(sK0,X4,sK3(sK0,sK2,sK1))
        | ~ r2_orders_2(sK0,sK3(sK0,sK2,sK1),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl4_15 ),
    inference(resolution,[],[f115,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r2_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r2_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_orders_2)).

fof(f115,plain,
    ( m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f125,plain,
    ( spl4_10
    | ~ spl4_9
    | ~ spl4_8
    | ~ spl4_7
    | ~ spl4_6
    | spl4_16
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f118,f114,f123,f70,f74,f78,f82,f86])).

fof(f118,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,sK3(sK0,sK2,sK1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,sK3(sK0,sK2,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_15 ),
    inference(resolution,[],[f115,f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r2_hidden(X1,k3_orders_2(X0,X3,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f117,plain,
    ( spl4_15
    | ~ spl4_5
    | ~ spl4_2
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f112,f104,f54,f66,f114])).

fof(f104,plain,
    ( spl4_13
  <=> ! [X0] :
        ( m1_subset_1(sK3(sK0,sK2,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X0,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f112,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))
    | ~ spl4_2
    | ~ spl4_13 ),
    inference(resolution,[],[f105,f55])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK3(sK0,sK2,X0),u1_struct_0(sK0)) )
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f104])).

fof(f111,plain,
    ( spl4_3
    | spl4_14
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f99,f95,f66,f109,f58])).

fof(f95,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | m1_subset_1(sK3(sK0,X1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f99,plain,
    ( ! [X1] :
        ( m1_subset_1(sK3(sK0,sK1,X1),u1_struct_0(sK0))
        | ~ m1_orders_2(X1,sK0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK1 )
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(resolution,[],[f96,f67])).

fof(f96,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK3(sK0,X1,X0),u1_struct_0(sK0))
        | ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1 )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f95])).

fof(f106,plain,
    ( spl4_12
    | spl4_13
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f98,f95,f62,f104,f101])).

fof(f98,plain,
    ( ! [X0] :
        ( m1_subset_1(sK3(sK0,sK2,X0),u1_struct_0(sK0))
        | ~ m1_orders_2(X0,sK0,sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK2 )
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(resolution,[],[f96,f63])).

fof(f97,plain,
    ( spl4_10
    | ~ spl4_9
    | ~ spl4_8
    | ~ spl4_7
    | spl4_11
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f89,f70,f95,f74,f78,f82,f86])).

fof(f89,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK3(sK0,X1,X0),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f37,f71])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f88,plain,(
    ~ spl4_10 ),
    inference(avatar_split_clause,[],[f24,f86])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( m1_orders_2(sK2,sK0,sK1)
    & m1_orders_2(sK1,sK0,sK2)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f16,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( m1_orders_2(X2,X0,X1)
                & m1_orders_2(X1,X0,X2)
                & k1_xboole_0 != X1
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,sK0,X1)
              & m1_orders_2(X1,sK0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( m1_orders_2(X2,sK0,X1)
            & m1_orders_2(X1,sK0,X2)
            & k1_xboole_0 != X1
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( m1_orders_2(X2,sK0,sK1)
          & m1_orders_2(sK1,sK0,X2)
          & k1_xboole_0 != sK1
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,
    ( ? [X2] :
        ( m1_orders_2(X2,sK0,sK1)
        & m1_orders_2(sK1,sK0,X2)
        & k1_xboole_0 != sK1
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( m1_orders_2(sK2,sK0,sK1)
      & m1_orders_2(sK1,sK0,sK2)
      & k1_xboole_0 != sK1
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( m1_orders_2(X2,X0,X1)
              & m1_orders_2(X1,X0,X2)
              & k1_xboole_0 != X1
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( m1_orders_2(X2,X0,X1)
                    & m1_orders_2(X1,X0,X2)
                    & k1_xboole_0 != X1 ) ) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( m1_orders_2(X2,X0,X1)
                  & m1_orders_2(X1,X0,X2)
                  & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).

fof(f84,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f25,f82])).

fof(f25,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f80,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f26,f78])).

fof(f26,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f76,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f27,f74])).

fof(f27,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f72,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f28,f70])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f68,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f29,f66])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f64,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f60,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f31,f58])).

fof(f31,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f17])).

fof(f56,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f32,f54])).

fof(f32,plain,(
    m1_orders_2(sK1,sK0,sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f52,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f33,f50])).

fof(f33,plain,(
    m1_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (27708)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (27711)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (27703)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (27708)Refutation not found, incomplete strategy% (27708)------------------------------
% 0.21/0.48  % (27708)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (27708)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (27708)Memory used [KB]: 10618
% 0.21/0.48  % (27708)Time elapsed: 0.010 s
% 0.21/0.48  % (27708)------------------------------
% 0.21/0.48  % (27708)------------------------------
% 0.21/0.49  % (27699)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (27703)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f574,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f52,f56,f60,f64,f68,f72,f76,f80,f84,f88,f97,f106,f111,f117,f125,f133,f139,f150,f165,f175,f181,f196,f212,f277,f281,f286,f316,f320,f381,f428,f522,f531,f563,f572,f573])).
% 0.21/0.49  fof(f573,plain,(
% 0.21/0.49    sK1 != k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) | r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)),sK3(sK0,sK1,sK2))) | ~r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f572,plain,(
% 0.21/0.49    spl4_10 | ~spl4_9 | ~spl4_8 | ~spl4_7 | ~spl4_6 | ~spl4_4 | ~spl4_5 | spl4_12 | ~spl4_2 | spl4_85),
% 0.21/0.49    inference(avatar_split_clause,[],[f569,f561,f54,f101,f66,f62,f70,f74,f78,f82,f86])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    spl4_10 <=> v2_struct_0(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    spl4_9 <=> v3_orders_2(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    spl4_8 <=> v4_orders_2(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    spl4_7 <=> v5_orders_2(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    spl4_6 <=> l1_orders_2(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    spl4_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl4_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.49  fof(f101,plain,(
% 0.21/0.49    spl4_12 <=> k1_xboole_0 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    spl4_2 <=> m1_orders_2(sK1,sK0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.49  fof(f561,plain,(
% 0.21/0.49    spl4_85 <=> r2_hidden(sK3(sK0,sK2,sK1),sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_85])])).
% 0.21/0.49  fof(f569,plain,(
% 0.21/0.49    ~m1_orders_2(sK1,sK0,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl4_85),
% 0.21/0.49    inference(resolution,[],[f562,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2 & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f21,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2 & r2_hidden(sK3(X0,X1,X2),X1) & m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(rectify,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).
% 0.21/0.49  fof(f562,plain,(
% 0.21/0.49    ~r2_hidden(sK3(sK0,sK2,sK1),sK2) | spl4_85),
% 0.21/0.49    inference(avatar_component_clause,[],[f561])).
% 0.21/0.49  fof(f563,plain,(
% 0.21/0.49    ~spl4_85 | spl4_40 | ~spl4_80),
% 0.21/0.49    inference(avatar_split_clause,[],[f556,f529,f251,f561])).
% 0.21/0.49  fof(f251,plain,(
% 0.21/0.49    spl4_40 <=> r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.21/0.49  fof(f529,plain,(
% 0.21/0.49    spl4_80 <=> sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_80])])).
% 0.21/0.49  fof(f556,plain,(
% 0.21/0.49    ~r2_hidden(sK3(sK0,sK2,sK1),sK2) | (spl4_40 | ~spl4_80)),
% 0.21/0.49    inference(superposition,[],[f252,f530])).
% 0.21/0.49  fof(f530,plain,(
% 0.21/0.49    sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) | ~spl4_80),
% 0.21/0.49    inference(avatar_component_clause,[],[f529])).
% 0.21/0.49  fof(f252,plain,(
% 0.21/0.49    ~r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2))) | spl4_40),
% 0.21/0.49    inference(avatar_component_clause,[],[f251])).
% 0.21/0.49  fof(f531,plain,(
% 0.21/0.49    spl4_80 | ~spl4_4 | ~spl4_1 | ~spl4_45),
% 0.21/0.49    inference(avatar_split_clause,[],[f469,f279,f50,f62,f529])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    spl4_1 <=> m1_orders_2(sK2,sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f279,plain,(
% 0.21/0.49    spl4_45 <=> ! [X1] : (k3_orders_2(sK0,sK1,sK3(sK0,sK1,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).
% 0.21/0.49  fof(f469,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | sK2 = k3_orders_2(sK0,sK1,sK3(sK0,sK1,sK2)) | (~spl4_1 | ~spl4_45)),
% 0.21/0.49    inference(resolution,[],[f280,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    m1_orders_2(sK2,sK0,sK1) | ~spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f50])).
% 0.21/0.49  fof(f280,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_orders_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,sK1,sK3(sK0,sK1,X1)) = X1) ) | ~spl4_45),
% 0.21/0.49    inference(avatar_component_clause,[],[f279])).
% 0.21/0.49  fof(f522,plain,(
% 0.21/0.49    ~spl4_5 | spl4_3 | ~spl4_48 | ~spl4_68),
% 0.21/0.49    inference(avatar_split_clause,[],[f520,f426,f314,f58,f66])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    spl4_3 <=> k1_xboole_0 = sK1),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.49  fof(f314,plain,(
% 0.21/0.49    spl4_48 <=> m1_orders_2(sK1,sK0,k1_xboole_0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).
% 0.21/0.49  fof(f426,plain,(
% 0.21/0.49    spl4_68 <=> ! [X0] : (~m1_orders_2(X0,sK0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_68])])).
% 0.21/0.49  fof(f520,plain,(
% 0.21/0.49    k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_48 | ~spl4_68)),
% 0.21/0.49    inference(resolution,[],[f427,f315])).
% 0.21/0.49  fof(f315,plain,(
% 0.21/0.49    m1_orders_2(sK1,sK0,k1_xboole_0) | ~spl4_48),
% 0.21/0.49    inference(avatar_component_clause,[],[f314])).
% 0.21/0.49  fof(f427,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_orders_2(X0,sK0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_68),
% 0.21/0.49    inference(avatar_component_clause,[],[f426])).
% 0.21/0.49  fof(f428,plain,(
% 0.21/0.49    spl4_10 | ~spl4_9 | ~spl4_8 | ~spl4_7 | ~spl4_6 | spl4_68 | ~spl4_49),
% 0.21/0.49    inference(avatar_split_clause,[],[f419,f318,f426,f70,f74,f78,f82,f86])).
% 0.21/0.49  fof(f318,plain,(
% 0.21/0.49    spl4_49 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 0.21/0.49  fof(f419,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_orders_2(X0,sK0,k1_xboole_0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X0 | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_49),
% 0.21/0.49    inference(resolution,[],[f319,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X2,X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k1_xboole_0 = X2 | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f319,plain,(
% 0.21/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_49),
% 0.21/0.49    inference(avatar_component_clause,[],[f318])).
% 0.21/0.49  fof(f381,plain,(
% 0.21/0.49    sK1 != k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f320,plain,(
% 0.21/0.49    spl4_49 | ~spl4_4 | ~spl4_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f289,f101,f62,f318])).
% 0.21/0.49  fof(f289,plain,(
% 0.21/0.49    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_4 | ~spl4_12)),
% 0.21/0.49    inference(superposition,[],[f63,f102])).
% 0.21/0.49  fof(f102,plain,(
% 0.21/0.49    k1_xboole_0 = sK2 | ~spl4_12),
% 0.21/0.49    inference(avatar_component_clause,[],[f101])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f62])).
% 0.21/0.49  fof(f316,plain,(
% 0.21/0.49    spl4_48 | ~spl4_2 | ~spl4_12),
% 0.21/0.49    inference(avatar_split_clause,[],[f288,f101,f54,f314])).
% 0.21/0.49  fof(f288,plain,(
% 0.21/0.49    m1_orders_2(sK1,sK0,k1_xboole_0) | (~spl4_2 | ~spl4_12)),
% 0.21/0.49    inference(superposition,[],[f55,f102])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    m1_orders_2(sK1,sK0,sK2) | ~spl4_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f54])).
% 0.21/0.49  fof(f286,plain,(
% 0.21/0.49    spl4_46 | ~spl4_5 | ~spl4_2 | ~spl4_44),
% 0.21/0.49    inference(avatar_split_clause,[],[f282,f275,f54,f66,f284])).
% 0.21/0.49  fof(f284,plain,(
% 0.21/0.49    spl4_46 <=> sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.21/0.49  fof(f275,plain,(
% 0.21/0.49    spl4_44 <=> ! [X0] : (k3_orders_2(sK0,sK2,sK3(sK0,sK2,X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X0,sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).
% 0.21/0.49  fof(f282,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)) | (~spl4_2 | ~spl4_44)),
% 0.21/0.49    inference(resolution,[],[f276,f55])).
% 0.21/0.49  fof(f276,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,sK2,sK3(sK0,sK2,X0)) = X0) ) | ~spl4_44),
% 0.21/0.49    inference(avatar_component_clause,[],[f275])).
% 0.21/0.49  fof(f281,plain,(
% 0.21/0.49    spl4_3 | spl4_45 | ~spl4_5 | ~spl4_33),
% 0.21/0.49    inference(avatar_split_clause,[],[f273,f210,f66,f279,f58])).
% 0.21/0.49  fof(f210,plain,(
% 0.21/0.49    spl4_33 <=> ! [X1,X0] : (~m1_orders_2(X0,sK0,X1) | k3_orders_2(sK0,X1,sK3(sK0,X1,X0)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    ( ! [X1] : (k3_orders_2(sK0,sK1,sK3(sK0,sK1,X1)) = X1 | ~m1_orders_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1) ) | (~spl4_5 | ~spl4_33)),
% 0.21/0.49    inference(resolution,[],[f211,f67])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_5),
% 0.21/0.49    inference(avatar_component_clause,[],[f66])).
% 0.21/0.49  fof(f211,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,X1,sK3(sK0,X1,X0)) = X0 | ~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1) ) | ~spl4_33),
% 0.21/0.49    inference(avatar_component_clause,[],[f210])).
% 0.21/0.49  fof(f277,plain,(
% 0.21/0.49    spl4_12 | spl4_44 | ~spl4_4 | ~spl4_33),
% 0.21/0.49    inference(avatar_split_clause,[],[f272,f210,f62,f275,f101])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    ( ! [X0] : (k3_orders_2(sK0,sK2,sK3(sK0,sK2,X0)) = X0 | ~m1_orders_2(X0,sK0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2) ) | (~spl4_4 | ~spl4_33)),
% 0.21/0.49    inference(resolution,[],[f211,f63])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    spl4_10 | ~spl4_9 | ~spl4_8 | ~spl4_7 | spl4_33 | ~spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f208,f70,f210,f74,f78,f82,f86])).
% 0.21/0.49  fof(f208,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,X1,sK3(sK0,X1,X0)) = X0 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_6),
% 0.21/0.49    inference(resolution,[],[f39,f71])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    l1_orders_2(sK0) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f70])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k3_orders_2(X0,X1,sK3(X0,X1,X2)) = X2 | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f196,plain,(
% 0.21/0.49    ~spl4_29 | ~spl4_30 | ~spl4_15 | ~spl4_21 | spl4_27),
% 0.21/0.49    inference(avatar_split_clause,[],[f187,f179,f148,f114,f194,f191])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    spl4_29 <=> m1_subset_1(k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_29])])).
% 0.21/0.49  fof(f194,plain,(
% 0.21/0.49    spl4_30 <=> r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)),sK3(sK0,sK1,sK2)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.49  fof(f114,plain,(
% 0.21/0.49    spl4_15 <=> m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    spl4_21 <=> ! [X3,X2] : (~r2_hidden(X2,k3_orders_2(sK0,X3,sK3(sK0,sK1,sK2))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | r2_hidden(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    spl4_27 <=> r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.49  fof(f187,plain,(
% 0.21/0.49    ~m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)),sK3(sK0,sK1,sK2))) | ~m1_subset_1(k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_21 | spl4_27)),
% 0.21/0.49    inference(resolution,[],[f180,f149])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    ( ! [X2,X3] : (r2_hidden(X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k3_orders_2(sK0,X3,sK3(sK0,sK1,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_21),
% 0.21/0.49    inference(avatar_component_clause,[],[f148])).
% 0.21/0.49  fof(f180,plain,(
% 0.21/0.49    ~r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))) | spl4_27),
% 0.21/0.49    inference(avatar_component_clause,[],[f179])).
% 0.21/0.49  fof(f181,plain,(
% 0.21/0.49    ~spl4_27 | ~spl4_4 | ~spl4_24),
% 0.21/0.49    inference(avatar_split_clause,[],[f176,f162,f62,f179])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    spl4_24 <=> ! [X0] : (~r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,X0,sK3(sK0,sK2,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    ~r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,sK2,sK3(sK0,sK2,sK1))) | (~spl4_4 | ~spl4_24)),
% 0.21/0.49    inference(resolution,[],[f163,f63])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,X0,sK3(sK0,sK2,sK1)))) ) | ~spl4_24),
% 0.21/0.49    inference(avatar_component_clause,[],[f162])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    spl4_24 | ~spl4_15 | ~spl4_16 | spl4_23),
% 0.21/0.49    inference(avatar_split_clause,[],[f174,f159,f123,f114,f162])).
% 0.21/0.49  fof(f123,plain,(
% 0.21/0.49    spl4_16 <=> ! [X1,X0] : (~r2_hidden(X0,k3_orders_2(sK0,X1,sK3(sK0,sK2,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,sK3(sK0,sK2,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.49  fof(f159,plain,(
% 0.21/0.49    spl4_23 <=> r2_orders_2(sK0,sK3(sK0,sK2,sK1),sK3(sK0,sK2,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,X0,sK3(sK0,sK2,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl4_16 | spl4_23)),
% 0.21/0.49    inference(resolution,[],[f160,f124])).
% 0.21/0.49  fof(f124,plain,(
% 0.21/0.49    ( ! [X0,X1] : (r2_orders_2(sK0,X0,sK3(sK0,sK2,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,X1,sK3(sK0,sK2,sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_16),
% 0.21/0.49    inference(avatar_component_clause,[],[f123])).
% 0.21/0.49  fof(f160,plain,(
% 0.21/0.49    ~r2_orders_2(sK0,sK3(sK0,sK2,sK1),sK3(sK0,sK2,sK1)) | spl4_23),
% 0.21/0.49    inference(avatar_component_clause,[],[f159])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ~spl4_23 | spl4_24 | ~spl4_15 | ~spl4_16 | ~spl4_18),
% 0.21/0.49    inference(avatar_split_clause,[],[f157,f131,f123,f114,f162,f159])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    spl4_18 <=> ! [X4] : (~r2_orders_2(sK0,X4,sK3(sK0,sK2,sK1)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK3(sK0,sK2,sK1),X4))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,X0,sK3(sK0,sK2,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,sK3(sK0,sK2,sK1),sK3(sK0,sK2,sK1))) ) | (~spl4_16 | ~spl4_18)),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f155])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~r2_hidden(sK3(sK0,sK2,sK1),k3_orders_2(sK0,X0,sK3(sK0,sK2,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK3(sK0,sK2,sK1),sK3(sK0,sK2,sK1))) ) | (~spl4_16 | ~spl4_18)),
% 0.21/0.49    inference(resolution,[],[f124,f132])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    ( ! [X4] : (~r2_orders_2(sK0,sK3(sK0,sK2,sK1),X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X4,sK3(sK0,sK2,sK1))) ) | ~spl4_18),
% 0.21/0.49    inference(avatar_component_clause,[],[f131])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    spl4_10 | ~spl4_9 | ~spl4_8 | ~spl4_7 | ~spl4_6 | spl4_21 | ~spl4_19),
% 0.21/0.49    inference(avatar_split_clause,[],[f141,f136,f148,f70,f74,f78,f82,f86])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    spl4_19 <=> m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    ( ! [X2,X3] : (~r2_hidden(X2,k3_orders_2(sK0,X3,sK3(sK0,sK1,sK2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X2,X3) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_19),
% 0.21/0.49    inference(resolution,[],[f137,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,X3) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f8])).
% 0.21/0.49  fof(f8,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | ~spl4_19),
% 0.21/0.49    inference(avatar_component_clause,[],[f136])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    spl4_19 | ~spl4_4 | ~spl4_1 | ~spl4_14),
% 0.21/0.49    inference(avatar_split_clause,[],[f134,f109,f50,f62,f136])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    spl4_14 <=> ! [X1] : (m1_subset_1(sK3(sK0,sK1,X1),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X1,sK0,sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(sK0,sK1,sK2),u1_struct_0(sK0)) | (~spl4_1 | ~spl4_14)),
% 0.21/0.49    inference(resolution,[],[f110,f51])).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ( ! [X1] : (~m1_orders_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(sK0,sK1,X1),u1_struct_0(sK0))) ) | ~spl4_14),
% 0.21/0.49    inference(avatar_component_clause,[],[f109])).
% 0.21/0.49  fof(f133,plain,(
% 0.21/0.49    ~spl4_7 | ~spl4_6 | spl4_18 | ~spl4_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f120,f114,f131,f70,f74])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    ( ! [X4] : (~r2_orders_2(sK0,X4,sK3(sK0,sK2,sK1)) | ~r2_orders_2(sK0,sK3(sK0,sK2,sK1),X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl4_15),
% 0.21/0.49    inference(resolution,[],[f115,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r2_orders_2(X0,X1,X2)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_orders_2)).
% 0.21/0.49  fof(f115,plain,(
% 0.21/0.49    m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) | ~spl4_15),
% 0.21/0.49    inference(avatar_component_clause,[],[f114])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    spl4_10 | ~spl4_9 | ~spl4_8 | ~spl4_7 | ~spl4_6 | spl4_16 | ~spl4_15),
% 0.21/0.49    inference(avatar_split_clause,[],[f118,f114,f123,f70,f74,f78,f82,f86])).
% 0.21/0.49  fof(f118,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,sK3(sK0,sK2,sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,sK3(sK0,sK2,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_15),
% 0.21/0.49    inference(resolution,[],[f115,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    spl4_15 | ~spl4_5 | ~spl4_2 | ~spl4_13),
% 0.21/0.49    inference(avatar_split_clause,[],[f112,f104,f54,f66,f114])).
% 0.21/0.49  fof(f104,plain,(
% 0.21/0.49    spl4_13 <=> ! [X0] : (m1_subset_1(sK3(sK0,sK2,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X0,sK0,sK2))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.21/0.49  fof(f112,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(sK0,sK2,sK1),u1_struct_0(sK0)) | (~spl4_2 | ~spl4_13)),
% 0.21/0.49    inference(resolution,[],[f105,f55])).
% 0.21/0.49  fof(f105,plain,(
% 0.21/0.49    ( ! [X0] : (~m1_orders_2(X0,sK0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(sK0,sK2,X0),u1_struct_0(sK0))) ) | ~spl4_13),
% 0.21/0.49    inference(avatar_component_clause,[],[f104])).
% 0.21/0.49  fof(f111,plain,(
% 0.21/0.49    spl4_3 | spl4_14 | ~spl4_5 | ~spl4_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f99,f95,f66,f109,f58])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl4_11 <=> ! [X1,X0] : (~m1_orders_2(X0,sK0,X1) | m1_subset_1(sK3(sK0,X1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    ( ! [X1] : (m1_subset_1(sK3(sK0,sK1,X1),u1_struct_0(sK0)) | ~m1_orders_2(X1,sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1) ) | (~spl4_5 | ~spl4_11)),
% 0.21/0.49    inference(resolution,[],[f96,f67])).
% 0.21/0.49  fof(f96,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(sK0,X1,X0),u1_struct_0(sK0)) | ~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1) ) | ~spl4_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f95])).
% 0.21/0.49  fof(f106,plain,(
% 0.21/0.49    spl4_12 | spl4_13 | ~spl4_4 | ~spl4_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f98,f95,f62,f104,f101])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(sK3(sK0,sK2,X0),u1_struct_0(sK0)) | ~m1_orders_2(X0,sK0,sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK2) ) | (~spl4_4 | ~spl4_11)),
% 0.21/0.49    inference(resolution,[],[f96,f63])).
% 0.21/0.49  fof(f97,plain,(
% 0.21/0.49    spl4_10 | ~spl4_9 | ~spl4_8 | ~spl4_7 | spl4_11 | ~spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f89,f70,f95,f74,f78,f82,f86])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK3(sK0,X1,X0),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl4_6),
% 0.21/0.49    inference(resolution,[],[f37,f71])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK3(X0,X1,X2),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ~spl4_10),
% 0.21/0.49    inference(avatar_split_clause,[],[f24,f86])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ((m1_orders_2(sK2,sK0,sK1) & m1_orders_2(sK1,sK0,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f16,f15,f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (m1_orders_2(X2,sK0,X1) & m1_orders_2(X1,sK0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X1] : (? [X2] : (m1_orders_2(X2,sK0,X1) & m1_orders_2(X1,sK0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (m1_orders_2(X2,sK0,sK1) & m1_orders_2(sK1,sK0,X2) & k1_xboole_0 != sK1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ? [X2] : (m1_orders_2(X2,sK0,sK1) & m1_orders_2(sK1,sK0,X2) & k1_xboole_0 != sK1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (m1_orders_2(sK2,sK0,sK1) & m1_orders_2(sK1,sK0,sK2) & k1_xboole_0 != sK1 & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f7,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : (m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f6])).
% 0.21/0.49  fof(f6,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (? [X2] : ((m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f5])).
% 0.21/0.49  fof(f5,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f4])).
% 0.21/0.49  fof(f4,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_orders_2)).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    spl4_9),
% 0.21/0.49    inference(avatar_split_clause,[],[f25,f82])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    v3_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl4_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f26,f78])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    v4_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f27,f74])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v5_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl4_6),
% 0.21/0.49    inference(avatar_split_clause,[],[f28,f70])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    l1_orders_2(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl4_5),
% 0.21/0.49    inference(avatar_split_clause,[],[f29,f66])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f30,f62])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ~spl4_3),
% 0.21/0.49    inference(avatar_split_clause,[],[f31,f58])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    k1_xboole_0 != sK1),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    spl4_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f32,f54])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    m1_orders_2(sK1,sK0,sK2)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f52,plain,(
% 0.21/0.49    spl4_1),
% 0.21/0.49    inference(avatar_split_clause,[],[f33,f50])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    m1_orders_2(sK2,sK0,sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (27703)------------------------------
% 0.21/0.49  % (27703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (27703)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (27703)Memory used [KB]: 11129
% 0.21/0.49  % (27703)Time elapsed: 0.015 s
% 0.21/0.49  % (27703)------------------------------
% 0.21/0.49  % (27703)------------------------------
% 0.21/0.49  % (27705)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (27695)Success in time 0.132 s
%------------------------------------------------------------------------------
