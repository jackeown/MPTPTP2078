%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 282 expanded)
%              Number of leaves         :   29 ( 141 expanded)
%              Depth                    :   12
%              Number of atoms          :  672 (1804 expanded)
%              Number of equality atoms :   81 ( 319 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f60,f64,f68,f72,f76,f80,f84,f89,f98,f103,f114,f121,f128,f136,f146,f148,f153,f161,f166,f171,f177,f184])).

fof(f184,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_4
    | spl3_2
    | ~ spl3_1
    | spl3_24 ),
    inference(avatar_split_clause,[],[f182,f175,f49,f52,f62,f66,f70,f74,f78,f82])).

fof(f82,plain,
    ( spl3_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f78,plain,
    ( spl3_8
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f74,plain,
    ( spl3_7
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f70,plain,
    ( spl3_6
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f66,plain,
    ( spl3_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f62,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f52,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f49,plain,
    ( spl3_1
  <=> m1_orders_2(sK1,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f175,plain,
    ( spl3_24
  <=> r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f182,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl3_24 ),
    inference(duplicate_literal_removal,[],[f180])).

fof(f180,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl3_24 ),
    inference(resolution,[],[f176,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
                    & ( ( k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
                        & r2_hidden(sK2(X0,X1,X2),X1)
                        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) )
                      | ~ m1_orders_2(X2,X0,X1) ) )
                  | k1_xboole_0 = X1 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).

fof(f21,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

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
    inference(rectify,[],[f19])).

fof(f19,plain,(
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

fof(f176,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl3_24 ),
    inference(avatar_component_clause,[],[f175])).

fof(f177,plain,
    ( ~ spl3_24
    | spl3_20
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f172,f169,f151,f175])).

fof(f151,plain,
    ( spl3_20
  <=> r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f169,plain,
    ( spl3_23
  <=> sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f172,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl3_20
    | ~ spl3_23 ),
    inference(superposition,[],[f152,f170])).

fof(f170,plain,
    ( sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f169])).

fof(f152,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f151])).

fof(f171,plain,
    ( spl3_23
    | ~ spl3_4
    | ~ spl3_1
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f167,f164,f49,f62,f169])).

fof(f164,plain,
    ( spl3_22
  <=> ! [X0] :
        ( k3_orders_2(sK0,sK1,sK2(sK0,sK1,X0)) = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X0,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f167,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))
    | ~ spl3_1
    | ~ spl3_22 ),
    inference(resolution,[],[f165,f50])).

fof(f50,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,sK1,sK2(sK0,sK1,X0)) = X0 )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f164])).

fof(f166,plain,
    ( spl3_2
    | spl3_22
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f162,f159,f62,f164,f52])).

fof(f159,plain,
    ( spl3_21
  <=> ! [X1,X0] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k3_orders_2(sK0,X1,sK2(sK0,X1,X0)) = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f162,plain,
    ( ! [X0] :
        ( k3_orders_2(sK0,sK1,sK2(sK0,sK1,X0)) = X0
        | ~ m1_orders_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK1 )
    | ~ spl3_4
    | ~ spl3_21 ),
    inference(resolution,[],[f160,f63])).

fof(f63,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X1,sK2(sK0,X1,X0)) = X0
        | ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1 )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f159])).

fof(f161,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | spl3_21
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f157,f66,f159,f70,f74,f78,f82])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_orders_2(sK0,X1,sK2(sK0,X1,X0)) = X0
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_5 ),
    inference(resolution,[],[f38,f67])).

fof(f67,plain,
    ( l1_orders_2(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f66])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f153,plain,
    ( ~ spl3_20
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f149,f143,f62,f151])).

fof(f143,plain,
    ( spl3_19
  <=> ! [X0] :
        ( ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f149,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)))
    | ~ spl3_4
    | ~ spl3_19 ),
    inference(resolution,[],[f144,f63])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1))) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f143])).

fof(f148,plain,
    ( spl3_19
    | ~ spl3_14
    | ~ spl3_15
    | spl3_18 ),
    inference(avatar_split_clause,[],[f147,f140,f126,f118,f143])).

fof(f118,plain,
    ( spl3_14
  <=> m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f126,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,sK2(sK0,sK1,sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,X0,sK2(sK0,sK1,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f140,plain,
    ( spl3_18
  <=> r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f147,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_15
    | spl3_18 ),
    inference(resolution,[],[f141,f127])).

fof(f127,plain,
    ( ! [X0,X1] :
        ( r2_orders_2(sK0,X0,sK2(sK0,sK1,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,X1,sK2(sK0,sK1,sK1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f126])).

fof(f141,plain,
    ( ~ r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f140])).

fof(f146,plain,
    ( ~ spl3_18
    | spl3_19
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f138,f134,f126,f118,f143,f140])).

fof(f134,plain,
    ( spl3_17
  <=> ! [X4] :
        ( ~ r2_orders_2(sK0,X4,sK2(sK0,sK1,sK1))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) )
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(duplicate_literal_removal,[],[f137])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) )
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(resolution,[],[f127,f135])).

fof(f135,plain,
    ( ! [X4] :
        ( ~ r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,X4,sK2(sK0,sK1,sK1)) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_17
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f124,f118,f134,f66,f70])).

fof(f124,plain,
    ( ! [X4] :
        ( ~ r2_orders_2(sK0,X4,sK2(sK0,sK1,sK1))
        | ~ r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl3_14 ),
    inference(resolution,[],[f119,f42])).

fof(f42,plain,(
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

fof(f119,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f118])).

fof(f128,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | spl3_15
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f122,f118,f126,f66,f70,f74,f78,f82])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,sK2(sK0,sK1,sK1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_orders_2(sK0,X0,sK2(sK0,sK1,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_14 ),
    inference(resolution,[],[f119,f33])).

fof(f33,plain,(
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
    inference(cnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f121,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f116,f101,f49,f62,f118])).

fof(f101,plain,
    ( spl3_12
  <=> ! [X0] :
        ( m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X0,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f116,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(resolution,[],[f102,f50])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f114,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f106,f87,f58,f66,f70,f74,f78,f82])).

fof(f58,plain,
    ( spl3_3
  <=> m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f87,plain,
    ( spl3_10
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f106,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f88,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_orders_2(k1_xboole_0,X0,X1)
      | k1_xboole_0 != X1
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_orders_2(X2,X0,X1)
      | k1_xboole_0 != X2
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f88,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f103,plain,
    ( spl3_2
    | spl3_12
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f99,f96,f62,f101,f52])).

fof(f96,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | m1_subset_1(sK2(sK0,X1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f99,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ m1_orders_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK1 )
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(resolution,[],[f97,f63])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK2(sK0,X1,X0),u1_struct_0(sK0))
        | ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1 )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | spl3_11
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f90,f66,f96,f70,f74,f78,f82])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK2(sK0,X1,X0),u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_5 ),
    inference(resolution,[],[f36,f67])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f89,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f85,f62,f52,f87])).

fof(f85,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(superposition,[],[f63,f53])).

fof(f53,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f84,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f23,f82])).

fof(f23,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ( k1_xboole_0 = sK1
        & ~ m1_orders_2(sK1,sK0,sK1) )
      | ( m1_orders_2(sK1,sK0,sK1)
        & k1_xboole_0 != sK1 ) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f15,f14])).

fof(f14,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
              | ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,sK0,X1) )
            | ( m1_orders_2(X1,sK0,X1)
              & k1_xboole_0 != X1 ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,
    ( ? [X1] :
        ( ( ( k1_xboole_0 = X1
            & ~ m1_orders_2(X1,sK0,X1) )
          | ( m1_orders_2(X1,sK0,X1)
            & k1_xboole_0 != X1 ) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ( k1_xboole_0 = sK1
          & ~ m1_orders_2(sK1,sK0,sK1) )
        | ( m1_orders_2(sK1,sK0,sK1)
          & k1_xboole_0 != sK1 ) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
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
          ( ( ( k1_xboole_0 = X1
              & ~ m1_orders_2(X1,X0,X1) )
            | ( m1_orders_2(X1,X0,X1)
              & k1_xboole_0 != X1 ) )
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
           => ( ~ ( k1_xboole_0 = X1
                  & ~ m1_orders_2(X1,X0,X1) )
              & ~ ( m1_orders_2(X1,X0,X1)
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
         => ( ~ ( k1_xboole_0 = X1
                & ~ m1_orders_2(X1,X0,X1) )
            & ~ ( m1_orders_2(X1,X0,X1)
                & k1_xboole_0 != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).

fof(f80,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f24,f78])).

fof(f24,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f76,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f25,f74])).

fof(f25,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f70])).

fof(f26,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f27,f66])).

fof(f27,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f62])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f55,f58,f52])).

fof(f55,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | k1_xboole_0 != sK1 ),
    inference(inner_rewriting,[],[f29])).

fof(f29,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f16])).

fof(f54,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f32,f52,f49])).

fof(f32,plain,
    ( k1_xboole_0 = sK1
    | m1_orders_2(sK1,sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:17:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (28236)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.50  % (28233)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (28233)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (28228)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (28229)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (28243)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.51  % (28228)Refutation not found, incomplete strategy% (28228)------------------------------
% 0.22/0.51  % (28228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28228)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28228)Memory used [KB]: 10618
% 0.22/0.51  % (28228)Time elapsed: 0.073 s
% 0.22/0.51  % (28228)------------------------------
% 0.22/0.51  % (28228)------------------------------
% 0.22/0.52  % (28237)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (28242)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f54,f60,f64,f68,f72,f76,f80,f84,f89,f98,f103,f114,f121,f128,f136,f146,f148,f153,f161,f166,f171,f177,f184])).
% 0.22/0.52  fof(f184,plain,(
% 0.22/0.52    spl3_9 | ~spl3_8 | ~spl3_7 | ~spl3_6 | ~spl3_5 | ~spl3_4 | spl3_2 | ~spl3_1 | spl3_24),
% 0.22/0.52    inference(avatar_split_clause,[],[f182,f175,f49,f52,f62,f66,f70,f74,f78,f82])).
% 0.22/0.52  fof(f82,plain,(
% 0.22/0.52    spl3_9 <=> v2_struct_0(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.52  fof(f78,plain,(
% 0.22/0.52    spl3_8 <=> v3_orders_2(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.52  fof(f74,plain,(
% 0.22/0.52    spl3_7 <=> v4_orders_2(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    spl3_6 <=> v5_orders_2(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    spl3_5 <=> l1_orders_2(sK0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    spl3_2 <=> k1_xboole_0 = sK1),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    spl3_1 <=> m1_orders_2(sK1,sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    spl3_24 <=> r2_hidden(sK2(sK0,sK1,sK1),sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl3_24),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f180])).
% 0.22/0.52  fof(f180,plain,(
% 0.22/0.52    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl3_24),
% 0.22/0.52    inference(resolution,[],[f176,f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f20,f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(rectify,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f10])).
% 0.22/0.52  fof(f10,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d15_orders_2)).
% 0.22/0.52  fof(f176,plain,(
% 0.22/0.52    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | spl3_24),
% 0.22/0.52    inference(avatar_component_clause,[],[f175])).
% 0.22/0.52  fof(f177,plain,(
% 0.22/0.52    ~spl3_24 | spl3_20 | ~spl3_23),
% 0.22/0.52    inference(avatar_split_clause,[],[f172,f169,f151,f175])).
% 0.22/0.52  fof(f151,plain,(
% 0.22/0.52    spl3_20 <=> r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    spl3_23 <=> sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.52  fof(f172,plain,(
% 0.22/0.52    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | (spl3_20 | ~spl3_23)),
% 0.22/0.52    inference(superposition,[],[f152,f170])).
% 0.22/0.52  fof(f170,plain,(
% 0.22/0.52    sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | ~spl3_23),
% 0.22/0.52    inference(avatar_component_clause,[],[f169])).
% 0.22/0.52  fof(f152,plain,(
% 0.22/0.52    ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))) | spl3_20),
% 0.22/0.52    inference(avatar_component_clause,[],[f151])).
% 0.22/0.52  fof(f171,plain,(
% 0.22/0.52    spl3_23 | ~spl3_4 | ~spl3_1 | ~spl3_22),
% 0.22/0.52    inference(avatar_split_clause,[],[f167,f164,f49,f62,f169])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    spl3_22 <=> ! [X0] : (k3_orders_2(sK0,sK1,sK2(sK0,sK1,X0)) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X0,sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)) | (~spl3_1 | ~spl3_22)),
% 0.22/0.52    inference(resolution,[],[f165,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    m1_orders_2(sK1,sK0,sK1) | ~spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f49])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_orders_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,sK1,sK2(sK0,sK1,X0)) = X0) ) | ~spl3_22),
% 0.22/0.52    inference(avatar_component_clause,[],[f164])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    spl3_2 | spl3_22 | ~spl3_4 | ~spl3_21),
% 0.22/0.52    inference(avatar_split_clause,[],[f162,f159,f62,f164,f52])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    spl3_21 <=> ! [X1,X0] : (~m1_orders_2(X0,sK0,X1) | k3_orders_2(sK0,X1,sK2(sK0,X1,X0)) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    ( ! [X0] : (k3_orders_2(sK0,sK1,sK2(sK0,sK1,X0)) = X0 | ~m1_orders_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1) ) | (~spl3_4 | ~spl3_21)),
% 0.22/0.52    inference(resolution,[],[f160,f63])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.22/0.52    inference(avatar_component_clause,[],[f62])).
% 0.22/0.52  fof(f160,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,X1,sK2(sK0,X1,X0)) = X0 | ~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1) ) | ~spl3_21),
% 0.22/0.52    inference(avatar_component_clause,[],[f159])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    spl3_9 | ~spl3_8 | ~spl3_7 | ~spl3_6 | spl3_21 | ~spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f157,f66,f159,f70,f74,f78,f82])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k3_orders_2(sK0,X1,sK2(sK0,X1,X0)) = X0 | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl3_5),
% 0.22/0.52    inference(resolution,[],[f38,f67])).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    l1_orders_2(sK0) | ~spl3_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f66])).
% 0.22/0.52  fof(f38,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f153,plain,(
% 0.22/0.52    ~spl3_20 | ~spl3_4 | ~spl3_19),
% 0.22/0.52    inference(avatar_split_clause,[],[f149,f143,f62,f151])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    spl3_19 <=> ! [X0] : (~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))) | (~spl3_4 | ~spl3_19)),
% 0.22/0.52    inference(resolution,[],[f144,f63])).
% 0.22/0.52  fof(f144,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)))) ) | ~spl3_19),
% 0.22/0.52    inference(avatar_component_clause,[],[f143])).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    spl3_19 | ~spl3_14 | ~spl3_15 | spl3_18),
% 0.22/0.52    inference(avatar_split_clause,[],[f147,f140,f126,f118,f143])).
% 0.22/0.52  fof(f118,plain,(
% 0.22/0.52    spl3_14 <=> m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.52  fof(f126,plain,(
% 0.22/0.52    spl3_15 <=> ! [X1,X0] : (~r2_hidden(X0,k3_orders_2(sK0,X1,sK2(sK0,sK1,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,sK2(sK0,sK1,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    spl3_18 <=> r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.22/0.52  fof(f147,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl3_15 | spl3_18)),
% 0.22/0.52    inference(resolution,[],[f141,f127])).
% 0.22/0.52  fof(f127,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r2_orders_2(sK0,X0,sK2(sK0,sK1,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,X1,sK2(sK0,sK1,sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f126])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ~r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) | spl3_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f140])).
% 0.22/0.52  fof(f146,plain,(
% 0.22/0.52    ~spl3_18 | spl3_19 | ~spl3_14 | ~spl3_15 | ~spl3_17),
% 0.22/0.52    inference(avatar_split_clause,[],[f138,f134,f126,f118,f143,f140])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    spl3_17 <=> ! [X4] : (~r2_orders_2(sK0,X4,sK2(sK0,sK1,sK1)) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))) ) | (~spl3_15 | ~spl3_17)),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f137])).
% 0.22/0.52  fof(f137,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))) ) | (~spl3_15 | ~spl3_17)),
% 0.22/0.52    inference(resolution,[],[f127,f135])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    ( ! [X4] : (~r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~r2_orders_2(sK0,X4,sK2(sK0,sK1,sK1))) ) | ~spl3_17),
% 0.22/0.52    inference(avatar_component_clause,[],[f134])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    ~spl3_6 | ~spl3_5 | spl3_17 | ~spl3_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f124,f118,f134,f66,f70])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    ( ! [X4] : (~r2_orders_2(sK0,X4,sK2(sK0,sK1,sK1)) | ~r2_orders_2(sK0,sK2(sK0,sK1,sK1),X4) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl3_14),
% 0.22/0.52    inference(resolution,[],[f119,f42])).
% 0.22/0.52  fof(f42,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.22/0.52    inference(flattening,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r2_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f2])).
% 0.22/0.52  fof(f2,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r2_orders_2(X0,X1,X2)))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_orders_2)).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~spl3_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f118])).
% 0.22/0.52  fof(f128,plain,(
% 0.22/0.52    spl3_9 | ~spl3_8 | ~spl3_7 | ~spl3_6 | ~spl3_5 | spl3_15 | ~spl3_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f122,f118,f126,f66,f70,f74,f78,f82])).
% 0.22/0.52  fof(f122,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,sK2(sK0,sK1,sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,sK2(sK0,sK1,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl3_14),
% 0.22/0.52    inference(resolution,[],[f119,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f8])).
% 0.22/0.52  fof(f8,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_orders_2)).
% 0.22/0.52  fof(f121,plain,(
% 0.22/0.52    spl3_14 | ~spl3_4 | ~spl3_1 | ~spl3_12),
% 0.22/0.52    inference(avatar_split_clause,[],[f116,f101,f49,f62,f118])).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    spl3_12 <=> ! [X0] : (m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X0,sK0,sK1))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | (~spl3_1 | ~spl3_12)),
% 0.22/0.52    inference(resolution,[],[f102,f50])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_orders_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))) ) | ~spl3_12),
% 0.22/0.52    inference(avatar_component_clause,[],[f101])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    spl3_9 | ~spl3_8 | ~spl3_7 | ~spl3_6 | ~spl3_5 | spl3_3 | ~spl3_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f106,f87,f58,f66,f70,f74,f78,f82])).
% 0.22/0.52  fof(f58,plain,(
% 0.22/0.52    spl3_3 <=> m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.52  fof(f87,plain,(
% 0.22/0.52    spl3_10 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.52  fof(f106,plain,(
% 0.22/0.52    m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl3_10),
% 0.22/0.52    inference(resolution,[],[f88,f47])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | m1_orders_2(k1_xboole_0,X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(duplicate_literal_removal,[],[f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    ( ! [X0] : (m1_orders_2(k1_xboole_0,X0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f43])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_orders_2(k1_xboole_0,X0,X1) | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(equality_resolution,[],[f41])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f87])).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    spl3_2 | spl3_12 | ~spl3_4 | ~spl3_11),
% 0.22/0.52    inference(avatar_split_clause,[],[f99,f96,f62,f101,f52])).
% 0.22/0.52  fof(f96,plain,(
% 0.22/0.52    spl3_11 <=> ! [X1,X0] : (~m1_orders_2(X0,sK0,X1) | m1_subset_1(sK2(sK0,X1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.52  fof(f99,plain,(
% 0.22/0.52    ( ! [X0] : (m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) | ~m1_orders_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1) ) | (~spl3_4 | ~spl3_11)),
% 0.22/0.52    inference(resolution,[],[f97,f63])).
% 0.22/0.52  fof(f97,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,X1,X0),u1_struct_0(sK0)) | ~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1) ) | ~spl3_11),
% 0.22/0.52    inference(avatar_component_clause,[],[f96])).
% 0.22/0.52  fof(f98,plain,(
% 0.22/0.52    spl3_9 | ~spl3_8 | ~spl3_7 | ~spl3_6 | spl3_11 | ~spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f90,f66,f96,f70,f74,f78,f82])).
% 0.22/0.52  fof(f90,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,X1,X0),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl3_5),
% 0.22/0.52    inference(resolution,[],[f36,f67])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    spl3_10 | ~spl3_2 | ~spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f85,f62,f52,f87])).
% 0.22/0.52  fof(f85,plain,(
% 0.22/0.52    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_4)),
% 0.22/0.52    inference(superposition,[],[f63,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | ~spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f52])).
% 0.22/0.52  fof(f84,plain,(
% 0.22/0.52    ~spl3_9),
% 0.22/0.52    inference(avatar_split_clause,[],[f23,f82])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    (((k1_xboole_0 = sK1 & ~m1_orders_2(sK1,sK0,sK1)) | (m1_orders_2(sK1,sK0,sK1) & k1_xboole_0 != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f7,f15,f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,sK0,X1)) | (m1_orders_2(X1,sK0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,sK0,X1)) | (m1_orders_2(X1,sK0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (((k1_xboole_0 = sK1 & ~m1_orders_2(sK1,sK0,sK1)) | (m1_orders_2(sK1,sK0,sK1) & k1_xboole_0 != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f7,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f6])).
% 0.22/0.52  fof(f6,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.22/0.52    inference(negated_conjecture,[],[f4])).
% 0.22/0.52  fof(f4,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.22/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_orders_2)).
% 0.22/0.52  fof(f80,plain,(
% 0.22/0.52    spl3_8),
% 0.22/0.52    inference(avatar_split_clause,[],[f24,f78])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    v3_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    spl3_7),
% 0.22/0.52    inference(avatar_split_clause,[],[f25,f74])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    v4_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    spl3_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f26,f70])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    v5_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f27,f66])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    l1_orders_2(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    spl3_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f28,f62])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ~spl3_2 | ~spl3_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f55,f58,f52])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | k1_xboole_0 != sK1),
% 0.22/0.52    inference(inner_rewriting,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 != sK1),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    spl3_1 | spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f32,f52,f49])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    k1_xboole_0 = sK1 | m1_orders_2(sK1,sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (28233)------------------------------
% 0.22/0.52  % (28233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28233)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (28233)Memory used [KB]: 10746
% 0.22/0.52  % (28233)Time elapsed: 0.070 s
% 0.22/0.52  % (28233)------------------------------
% 0.22/0.52  % (28233)------------------------------
% 0.22/0.52  % (28226)Success in time 0.156 s
%------------------------------------------------------------------------------
