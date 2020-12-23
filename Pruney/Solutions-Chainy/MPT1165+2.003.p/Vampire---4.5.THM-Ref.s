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
% DateTime   : Thu Dec  3 13:10:11 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  130 ( 294 expanded)
%              Number of leaves         :   31 ( 147 expanded)
%              Depth                    :   12
%              Number of atoms          :  746 (1866 expanded)
%              Number of equality atoms :   70 ( 300 expanded)
%              Maximal formula depth    :   15 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f214,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f74,f78,f82,f86,f90,f94,f98,f104,f120,f125,f137,f143,f154,f166,f170,f174,f188,f193,f196,f201,f209,f213])).

fof(f213,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_4
    | spl3_2
    | ~ spl3_1
    | spl3_27 ),
    inference(avatar_split_clause,[],[f212,f207,f63,f66,f76,f80,f84,f88,f92,f96])).

fof(f96,plain,
    ( spl3_9
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f92,plain,
    ( spl3_8
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f88,plain,
    ( spl3_7
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f84,plain,
    ( spl3_6
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f80,plain,
    ( spl3_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f76,plain,
    ( spl3_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f66,plain,
    ( spl3_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f63,plain,
    ( spl3_1
  <=> m1_orders_2(sK1,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f207,plain,
    ( spl3_27
  <=> r2_hidden(sK2(sK0,sK1,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f212,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl3_27 ),
    inference(duplicate_literal_removal,[],[f210])).

fof(f210,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl3_27 ),
    inference(resolution,[],[f208,f47])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k3_orders_2(X0,X1,X4) = X2
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
        & r2_hidden(sK2(X0,X1,X2),X1)
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).

fof(f208,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | spl3_27 ),
    inference(avatar_component_clause,[],[f207])).

fof(f209,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | ~ spl3_4
    | spl3_2
    | ~ spl3_1
    | ~ spl3_27
    | spl3_26 ),
    inference(avatar_split_clause,[],[f204,f199,f207,f63,f66,f76,f80,f84,f88,f92,f96])).

fof(f199,plain,
    ( spl3_26
  <=> r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f204,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl3_26 ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),sK1)
    | ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 = sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | spl3_26 ),
    inference(superposition,[],[f200,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2
      | ~ m1_orders_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f200,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f199])).

fof(f201,plain,
    ( ~ spl3_26
    | ~ spl3_4
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f197,f185,f76,f199])).

fof(f185,plain,
    ( spl3_24
  <=> ! [X0] :
        ( ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f197,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)))
    | ~ spl3_4
    | ~ spl3_24 ),
    inference(resolution,[],[f186,f77])).

fof(f77,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1))) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f185])).

fof(f196,plain,
    ( ~ spl3_15
    | ~ spl3_20
    | spl3_25 ),
    inference(avatar_split_clause,[],[f195,f191,f168,f140])).

fof(f140,plain,
    ( spl3_15
  <=> m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f168,plain,
    ( spl3_20
  <=> ! [X7] :
        ( r3_orders_2(sK0,X7,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f191,plain,
    ( spl3_25
  <=> r3_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f195,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl3_20
    | spl3_25 ),
    inference(resolution,[],[f192,f169])).

fof(f169,plain,
    ( ! [X7] :
        ( r3_orders_2(sK0,X7,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0)) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f168])).

fof(f192,plain,
    ( ~ r3_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f191])).

fof(f193,plain,
    ( ~ spl3_25
    | ~ spl3_15
    | ~ spl3_21
    | spl3_23 ),
    inference(avatar_split_clause,[],[f189,f182,f172,f140,f191])).

fof(f172,plain,
    ( spl3_21
  <=> ! [X8] :
        ( ~ r3_orders_2(sK0,X8,sK2(sK0,sK1,sK1))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r1_orders_2(sK0,X8,sK2(sK0,sK1,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f182,plain,
    ( spl3_23
  <=> r1_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f189,plain,
    ( ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ r3_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))
    | ~ spl3_21
    | spl3_23 ),
    inference(resolution,[],[f183,f173])).

fof(f173,plain,
    ( ! [X8] :
        ( r1_orders_2(sK0,X8,sK2(sK0,sK1,sK1))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ r3_orders_2(sK0,X8,sK2(sK0,sK1,sK1)) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f172])).

fof(f183,plain,
    ( ~ r1_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f182])).

fof(f188,plain,
    ( ~ spl3_23
    | spl3_24
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(avatar_split_clause,[],[f180,f164,f152,f140,f185,f182])).

fof(f152,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k3_orders_2(sK0,X1,sK2(sK0,sK1,sK1)))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_orders_2(sK0,X0,sK2(sK0,sK1,sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f164,plain,
    ( spl3_19
  <=> ! [X6] :
        ( ~ r1_orders_2(sK0,X6,sK2(sK0,sK1,sK1))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r2_orders_2(sK0,sK2(sK0,sK1,sK1),X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f180,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) )
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
        | ~ r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) )
    | ~ spl3_16
    | ~ spl3_19 ),
    inference(resolution,[],[f153,f165])).

fof(f165,plain,
    ( ! [X6] :
        ( ~ r2_orders_2(sK0,sK2(sK0,sK1,sK1),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ r1_orders_2(sK0,X6,sK2(sK0,sK1,sK1)) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f164])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( r2_orders_2(sK0,X0,sK2(sK0,sK1,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k3_orders_2(sK0,X1,sK2(sK0,sK1,sK1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f152])).

fof(f174,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_5
    | spl3_21
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f149,f140,f172,f80,f92,f96])).

fof(f149,plain,
    ( ! [X8] :
        ( ~ r3_orders_2(sK0,X8,sK2(sK0,sK1,sK1))
        | r1_orders_2(sK0,X8,sK2(sK0,sK1,sK1))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_15 ),
    inference(resolution,[],[f141,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r3_orders_2(X0,X1,X2)
      | r1_orders_2(X0,X1,X2)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_orders_2(X0,X1,X2)
          | ~ r1_orders_2(X0,X1,X2) )
        & ( r1_orders_2(X0,X1,X2)
          | ~ r3_orders_2(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_orders_2(X0,X1,X2)
      <=> r1_orders_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).

fof(f141,plain,
    ( m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f140])).

fof(f170,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_5
    | spl3_20
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f148,f140,f168,f80,f92,f96])).

fof(f148,plain,
    ( ! [X7] :
        ( r3_orders_2(sK0,X7,X7)
        | ~ m1_subset_1(X7,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl3_15 ),
    inference(resolution,[],[f141,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r3_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => r3_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).

fof(f166,plain,
    ( ~ spl3_6
    | ~ spl3_5
    | spl3_19
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f147,f140,f164,f80,f84])).

fof(f147,plain,
    ( ! [X6] :
        ( ~ r1_orders_2(sK0,X6,sK2(sK0,sK1,sK1))
        | ~ r2_orders_2(sK0,sK2(sK0,sK1,sK1),X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0) )
    | ~ spl3_15 ),
    inference(resolution,[],[f141,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_orders_2(X0,X1,X2)
      | ~ r2_orders_2(X0,X2,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_orders_2(X0,X2,X1)
              | ~ r1_orders_2(X0,X1,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ~ ( r2_orders_2(X0,X2,X1)
                  & r1_orders_2(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).

fof(f154,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | spl3_16
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f144,f140,f152,f80,f84,f88,f92,f96])).

fof(f144,plain,
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
    | ~ spl3_15 ),
    inference(resolution,[],[f141,f43])).

fof(f43,plain,(
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
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).

fof(f143,plain,
    ( spl3_15
    | ~ spl3_4
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f138,f123,f63,f76,f140])).

fof(f123,plain,
    ( spl3_13
  <=> ! [X0] :
        ( m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X0,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f138,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))
    | ~ spl3_1
    | ~ spl3_13 ),
    inference(resolution,[],[f124,f64])).

fof(f64,plain,
    ( m1_orders_2(sK1,sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_orders_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f123])).

fof(f137,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | ~ spl3_5
    | spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f128,f102,f72,f80,f84,f88,f92,f96])).

fof(f72,plain,
    ( spl3_3
  <=> m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f102,plain,
    ( spl3_10
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f128,plain,
    ( m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f103,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( m1_orders_2(k1_xboole_0,X0,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
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
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f103,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f125,plain,
    ( spl3_2
    | spl3_13
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f121,f118,f76,f123,f66])).

fof(f118,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | m1_subset_1(sK2(sK0,X1,X0),u1_struct_0(sK0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f121,plain,
    ( ! [X0] :
        ( m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))
        | ~ m1_orders_2(X0,sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK1 )
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(resolution,[],[f119,f77])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(sK2(sK0,X1,X0),u1_struct_0(sK0))
        | ~ m1_orders_2(X0,sK0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X1 )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_7
    | ~ spl3_6
    | spl3_12
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f116,f80,f118,f84,f88,f92,f96])).

fof(f116,plain,
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
    inference(resolution,[],[f46,f81])).

fof(f81,plain,
    ( l1_orders_2(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f46,plain,(
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
    inference(cnf_transformation,[],[f31])).

fof(f104,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f100,f76,f66,f102])).

fof(f100,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(superposition,[],[f77,f67])).

fof(f67,plain,
    ( k1_xboole_0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f98,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f33,f96])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f24,f23])).

fof(f23,plain,
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

fof(f24,plain,
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

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
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
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).

fof(f94,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f34,f92])).

fof(f34,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f90,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f35,f88])).

fof(f35,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f86,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f36,f84])).

fof(f36,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f37,f80])).

fof(f37,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f78,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f38,f76])).

fof(f38,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f69,f72,f66])).

fof(f69,plain,
    ( ~ m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)
    | k1_xboole_0 != sK1 ),
    inference(inner_rewriting,[],[f39])).

fof(f39,plain,
    ( ~ m1_orders_2(sK1,sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f68,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f42,f66,f63])).

fof(f42,plain,
    ( k1_xboole_0 = sK1
    | m1_orders_2(sK1,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:45:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (25704)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  % (25709)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  % (25715)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (25704)Refutation not found, incomplete strategy% (25704)------------------------------
% 0.20/0.48  % (25704)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (25704)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (25704)Memory used [KB]: 6140
% 0.20/0.48  % (25704)Time elapsed: 0.061 s
% 0.20/0.48  % (25704)------------------------------
% 0.20/0.48  % (25704)------------------------------
% 0.20/0.48  % (25715)Refutation not found, incomplete strategy% (25715)------------------------------
% 0.20/0.48  % (25715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (25724)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (25715)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (25715)Memory used [KB]: 10618
% 0.20/0.48  % (25715)Time elapsed: 0.059 s
% 0.20/0.48  % (25715)------------------------------
% 0.20/0.48  % (25715)------------------------------
% 0.20/0.48  % (25716)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (25710)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (25716)Refutation not found, incomplete strategy% (25716)------------------------------
% 0.20/0.49  % (25716)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (25716)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (25716)Memory used [KB]: 6140
% 0.20/0.49  % (25716)Time elapsed: 0.004 s
% 0.20/0.49  % (25716)------------------------------
% 0.20/0.49  % (25716)------------------------------
% 0.20/0.49  % (25710)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f68,f74,f78,f82,f86,f90,f94,f98,f104,f120,f125,f137,f143,f154,f166,f170,f174,f188,f193,f196,f201,f209,f213])).
% 0.20/0.49  fof(f213,plain,(
% 0.20/0.49    spl3_9 | ~spl3_8 | ~spl3_7 | ~spl3_6 | ~spl3_5 | ~spl3_4 | spl3_2 | ~spl3_1 | spl3_27),
% 0.20/0.49    inference(avatar_split_clause,[],[f212,f207,f63,f66,f76,f80,f84,f88,f92,f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    spl3_9 <=> v2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    spl3_8 <=> v3_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl3_7 <=> v4_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    spl3_6 <=> v5_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl3_5 <=> l1_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    spl3_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    spl3_2 <=> k1_xboole_0 = sK1),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    spl3_1 <=> m1_orders_2(sK1,sK0,sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f207,plain,(
% 0.20/0.49    spl3_27 <=> r2_hidden(sK2(sK0,sK1,sK1),sK1)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl3_27),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f210])).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl3_27),
% 0.20/0.49    inference(resolution,[],[f208,f47])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f29,f30])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ! [X2,X1,X0] : (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 & r2_hidden(sK2(X0,X1,X2),X1) & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0))))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X4] : (k3_orders_2(X0,X1,X4) = X2 & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(rectify,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (((((m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 != X1) & (((m1_orders_2(X2,X0,X1) | ! [X3] : (k3_orders_2(X0,X1,X3) != X2 | ~r2_hidden(X3,X1) | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(nnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : ((((m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 != X1) & ((m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))) | k1_xboole_0 = X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((k1_xboole_0 = X1 => (m1_orders_2(X2,X0,X1) <=> k1_xboole_0 = X2)) & (k1_xboole_0 != X1 => (m1_orders_2(X2,X0,X1) <=> ? [X3] : (k3_orders_2(X0,X1,X3) = X2 & r2_hidden(X3,X1) & m1_subset_1(X3,u1_struct_0(X0)))))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d15_orders_2)).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | spl3_27),
% 0.20/0.49    inference(avatar_component_clause,[],[f207])).
% 0.20/0.49  fof(f209,plain,(
% 0.20/0.49    spl3_9 | ~spl3_8 | ~spl3_7 | ~spl3_6 | ~spl3_5 | ~spl3_4 | spl3_2 | ~spl3_1 | ~spl3_27 | spl3_26),
% 0.20/0.49    inference(avatar_split_clause,[],[f204,f199,f207,f63,f66,f76,f80,f84,f88,f92,f96])).
% 0.20/0.49  fof(f199,plain,(
% 0.20/0.49    spl3_26 <=> r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.49  fof(f204,plain,(
% 0.20/0.49    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl3_26),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f203])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    ~r2_hidden(sK2(sK0,sK1,sK1),sK1) | ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 = sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | spl3_26),
% 0.20/0.49    inference(superposition,[],[f200,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k3_orders_2(X0,X1,sK2(X0,X1,X2)) = X2 | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f31])).
% 0.20/0.49  fof(f200,plain,(
% 0.20/0.49    ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))) | spl3_26),
% 0.20/0.49    inference(avatar_component_clause,[],[f199])).
% 0.20/0.49  fof(f201,plain,(
% 0.20/0.49    ~spl3_26 | ~spl3_4 | ~spl3_24),
% 0.20/0.49    inference(avatar_split_clause,[],[f197,f185,f76,f199])).
% 0.20/0.49  fof(f185,plain,(
% 0.20/0.49    spl3_24 <=> ! [X0] : (~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.49  fof(f197,plain,(
% 0.20/0.49    ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,sK1,sK2(sK0,sK1,sK1))) | (~spl3_4 | ~spl3_24)),
% 0.20/0.49    inference(resolution,[],[f186,f77])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f76])).
% 0.20/0.49  fof(f186,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1)))) ) | ~spl3_24),
% 0.20/0.49    inference(avatar_component_clause,[],[f185])).
% 0.20/0.49  fof(f196,plain,(
% 0.20/0.49    ~spl3_15 | ~spl3_20 | spl3_25),
% 0.20/0.49    inference(avatar_split_clause,[],[f195,f191,f168,f140])).
% 0.20/0.49  fof(f140,plain,(
% 0.20/0.49    spl3_15 <=> m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.20/0.49  fof(f168,plain,(
% 0.20/0.49    spl3_20 <=> ! [X7] : (r3_orders_2(sK0,X7,X7) | ~m1_subset_1(X7,u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.49  fof(f191,plain,(
% 0.20/0.49    spl3_25 <=> r3_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.49  fof(f195,plain,(
% 0.20/0.49    ~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | (~spl3_20 | spl3_25)),
% 0.20/0.49    inference(resolution,[],[f192,f169])).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    ( ! [X7] : (r3_orders_2(sK0,X7,X7) | ~m1_subset_1(X7,u1_struct_0(sK0))) ) | ~spl3_20),
% 0.20/0.49    inference(avatar_component_clause,[],[f168])).
% 0.20/0.49  fof(f192,plain,(
% 0.20/0.49    ~r3_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) | spl3_25),
% 0.20/0.49    inference(avatar_component_clause,[],[f191])).
% 0.20/0.49  fof(f193,plain,(
% 0.20/0.49    ~spl3_25 | ~spl3_15 | ~spl3_21 | spl3_23),
% 0.20/0.49    inference(avatar_split_clause,[],[f189,f182,f172,f140,f191])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    spl3_21 <=> ! [X8] : (~r3_orders_2(sK0,X8,sK2(sK0,sK1,sK1)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | r1_orders_2(sK0,X8,sK2(sK0,sK1,sK1)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    spl3_23 <=> r1_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    ~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~r3_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) | (~spl3_21 | spl3_23)),
% 0.20/0.49    inference(resolution,[],[f183,f173])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    ( ! [X8] : (r1_orders_2(sK0,X8,sK2(sK0,sK1,sK1)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~r3_orders_2(sK0,X8,sK2(sK0,sK1,sK1))) ) | ~spl3_21),
% 0.20/0.49    inference(avatar_component_clause,[],[f172])).
% 0.20/0.49  fof(f183,plain,(
% 0.20/0.49    ~r1_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1)) | spl3_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f182])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    ~spl3_23 | spl3_24 | ~spl3_15 | ~spl3_16 | ~spl3_19),
% 0.20/0.49    inference(avatar_split_clause,[],[f180,f164,f152,f140,f185,f182])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    spl3_16 <=> ! [X1,X0] : (~r2_hidden(X0,k3_orders_2(sK0,X1,sK2(sK0,sK1,sK1))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r2_orders_2(sK0,X0,sK2(sK0,sK1,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    spl3_19 <=> ! [X6] : (~r1_orders_2(sK0,X6,sK2(sK0,sK1,sK1)) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r2_orders_2(sK0,sK2(sK0,sK1,sK1),X6))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.50  fof(f180,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))) ) | (~spl3_16 | ~spl3_19)),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f179])).
% 0.20/0.50  fof(f179,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~r2_hidden(sK2(sK0,sK1,sK1),k3_orders_2(sK0,X0,sK2(sK0,sK1,sK1))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~r1_orders_2(sK0,sK2(sK0,sK1,sK1),sK2(sK0,sK1,sK1))) ) | (~spl3_16 | ~spl3_19)),
% 0.20/0.50    inference(resolution,[],[f153,f165])).
% 0.20/0.50  fof(f165,plain,(
% 0.20/0.50    ( ! [X6] : (~r2_orders_2(sK0,sK2(sK0,sK1,sK1),X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~r1_orders_2(sK0,X6,sK2(sK0,sK1,sK1))) ) | ~spl3_19),
% 0.20/0.50    inference(avatar_component_clause,[],[f164])).
% 0.20/0.50  fof(f153,plain,(
% 0.20/0.50    ( ! [X0,X1] : (r2_orders_2(sK0,X0,sK2(sK0,sK1,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k3_orders_2(sK0,X1,sK2(sK0,sK1,sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_16),
% 0.20/0.50    inference(avatar_component_clause,[],[f152])).
% 0.20/0.50  fof(f174,plain,(
% 0.20/0.50    spl3_9 | ~spl3_8 | ~spl3_5 | spl3_21 | ~spl3_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f149,f140,f172,f80,f92,f96])).
% 0.20/0.50  fof(f149,plain,(
% 0.20/0.50    ( ! [X8] : (~r3_orders_2(sK0,X8,sK2(sK0,sK1,sK1)) | r1_orders_2(sK0,X8,sK2(sK0,sK1,sK1)) | ~m1_subset_1(X8,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl3_15),
% 0.20/0.50    inference(resolution,[],[f141,f55])).
% 0.20/0.50  fof(f55,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~r3_orders_2(X0,X1,X2) | r1_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f32])).
% 0.20/0.50  fof(f32,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((r3_orders_2(X0,X1,X2) | ~r1_orders_2(X0,X1,X2)) & (r1_orders_2(X0,X1,X2) | ~r3_orders_2(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (r3_orders_2(X0,X1,X2) <=> r1_orders_2(X0,X1,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_orders_2)).
% 0.20/0.50  fof(f141,plain,(
% 0.20/0.50    m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | ~spl3_15),
% 0.20/0.50    inference(avatar_component_clause,[],[f140])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    spl3_9 | ~spl3_8 | ~spl3_5 | spl3_20 | ~spl3_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f148,f140,f168,f80,f92,f96])).
% 0.20/0.50  fof(f148,plain,(
% 0.20/0.50    ( ! [X7] : (r3_orders_2(sK0,X7,X7) | ~m1_subset_1(X7,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl3_15),
% 0.20/0.50    inference(resolution,[],[f141,f54])).
% 0.20/0.50  fof(f54,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | r3_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f19])).
% 0.20/0.50  fof(f19,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (r3_orders_2(X0,X1,X1) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => r3_orders_2(X0,X1,X1))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',reflexivity_r3_orders_2)).
% 0.20/0.50  fof(f166,plain,(
% 0.20/0.50    ~spl3_6 | ~spl3_5 | spl3_19 | ~spl3_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f147,f140,f164,f80,f84])).
% 0.20/0.50  fof(f147,plain,(
% 0.20/0.50    ( ! [X6] : (~r1_orders_2(sK0,X6,sK2(sK0,sK1,sK1)) | ~r2_orders_2(sK0,sK2(sK0,sK1,sK1),X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0)) ) | ~spl3_15),
% 0.20/0.50    inference(resolution,[],[f141,f52])).
% 0.20/0.50  fof(f52,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_orders_2(X0,X1,X2) | ~r2_orders_2(X0,X2,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0))),
% 0.20/0.50    inference(flattening,[],[f15])).
% 0.20/0.50  fof(f15,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : ((~r2_orders_2(X0,X2,X1) | ~r1_orders_2(X0,X1,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f5])).
% 0.20/0.50  fof(f5,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(r2_orders_2(X0,X2,X1) & r1_orders_2(X0,X1,X2)))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_orders_2)).
% 0.20/0.50  fof(f154,plain,(
% 0.20/0.50    spl3_9 | ~spl3_8 | ~spl3_7 | ~spl3_6 | ~spl3_5 | spl3_16 | ~spl3_15),
% 0.20/0.50    inference(avatar_split_clause,[],[f144,f140,f152,f80,f84,f88,f92,f96])).
% 0.20/0.50  fof(f144,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~r2_hidden(X0,k3_orders_2(sK0,X1,sK2(sK0,sK1,sK1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_orders_2(sK0,X0,sK2(sK0,sK1,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl3_15),
% 0.20/0.50    inference(resolution,[],[f141,f43])).
% 0.20/0.50  fof(f43,plain,(
% 0.20/0.50    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,u1_struct_0(X0)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | r2_orders_2(X0,X1,X2) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f27])).
% 0.20/0.50  fof(f27,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | ~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2)) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((r2_hidden(X1,k3_orders_2(X0,X3,X2)) | (~r2_hidden(X1,X3) | ~r2_orders_2(X0,X1,X2))) & ((r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)) | ~r2_hidden(X1,k3_orders_2(X0,X3,X2)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(nnf_transformation,[],[f12])).
% 0.20/0.50  fof(f12,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f11])).
% 0.20/0.50  fof(f11,plain,(
% 0.20/0.50    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f6])).
% 0.20/0.50  fof(f6,axiom,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k3_orders_2(X0,X3,X2)) <=> (r2_hidden(X1,X3) & r2_orders_2(X0,X1,X2)))))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_orders_2)).
% 0.20/0.50  fof(f143,plain,(
% 0.20/0.50    spl3_15 | ~spl3_4 | ~spl3_1 | ~spl3_13),
% 0.20/0.50    inference(avatar_split_clause,[],[f138,f123,f63,f76,f140])).
% 0.20/0.50  fof(f123,plain,(
% 0.20/0.50    spl3_13 <=> ! [X0] : (m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_2(X0,sK0,sK1))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.50  fof(f138,plain,(
% 0.20/0.50    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,sK1),u1_struct_0(sK0)) | (~spl3_1 | ~spl3_13)),
% 0.20/0.50    inference(resolution,[],[f124,f64])).
% 0.20/0.50  fof(f64,plain,(
% 0.20/0.50    m1_orders_2(sK1,sK0,sK1) | ~spl3_1),
% 0.20/0.50    inference(avatar_component_clause,[],[f63])).
% 0.20/0.50  fof(f124,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_orders_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0))) ) | ~spl3_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f123])).
% 0.20/0.50  fof(f137,plain,(
% 0.20/0.50    spl3_9 | ~spl3_8 | ~spl3_7 | ~spl3_6 | ~spl3_5 | spl3_3 | ~spl3_10),
% 0.20/0.50    inference(avatar_split_clause,[],[f128,f102,f72,f80,f84,f88,f92,f96])).
% 0.20/0.50  fof(f72,plain,(
% 0.20/0.50    spl3_3 <=> m1_orders_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f102,plain,(
% 0.20/0.50    spl3_10 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.50  fof(f128,plain,(
% 0.20/0.50    m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl3_10),
% 0.20/0.50    inference(resolution,[],[f103,f61])).
% 0.20/0.50  fof(f61,plain,(
% 0.20/0.50    ( ! [X0] : (~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | m1_orders_2(k1_xboole_0,X0,k1_xboole_0) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(duplicate_literal_removal,[],[f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X0] : (m1_orders_2(k1_xboole_0,X0,k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f57])).
% 0.20/0.50  fof(f57,plain,(
% 0.20/0.50    ( ! [X0,X1] : (m1_orders_2(k1_xboole_0,X0,X1) | k1_xboole_0 != X1 | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(equality_resolution,[],[f51])).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (m1_orders_2(X2,X0,X1) | k1_xboole_0 != X2 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f103,plain,(
% 0.20/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_10),
% 0.20/0.50    inference(avatar_component_clause,[],[f102])).
% 0.20/0.50  fof(f125,plain,(
% 0.20/0.50    spl3_2 | spl3_13 | ~spl3_4 | ~spl3_12),
% 0.20/0.50    inference(avatar_split_clause,[],[f121,f118,f76,f123,f66])).
% 0.20/0.50  fof(f118,plain,(
% 0.20/0.50    spl3_12 <=> ! [X1,X0] : (~m1_orders_2(X0,sK0,X1) | m1_subset_1(sK2(sK0,X1,X0),u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.50  fof(f121,plain,(
% 0.20/0.50    ( ! [X0] : (m1_subset_1(sK2(sK0,sK1,X0),u1_struct_0(sK0)) | ~m1_orders_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK1) ) | (~spl3_4 | ~spl3_12)),
% 0.20/0.50    inference(resolution,[],[f119,f77])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,X1,X0),u1_struct_0(sK0)) | ~m1_orders_2(X0,sK0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X1) ) | ~spl3_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f118])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    spl3_9 | ~spl3_8 | ~spl3_7 | ~spl3_6 | spl3_12 | ~spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f116,f80,f118,f84,f88,f92,f96])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(sK2(sK0,X1,X0),u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl3_5),
% 0.20/0.50    inference(resolution,[],[f46,f81])).
% 0.20/0.50  fof(f81,plain,(
% 0.20/0.50    l1_orders_2(sK0) | ~spl3_5),
% 0.20/0.50    inference(avatar_component_clause,[],[f80])).
% 0.20/0.50  fof(f46,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m1_orders_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X0)) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f31])).
% 0.20/0.50  fof(f104,plain,(
% 0.20/0.50    spl3_10 | ~spl3_2 | ~spl3_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f100,f76,f66,f102])).
% 0.20/0.50  fof(f100,plain,(
% 0.20/0.50    m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl3_2 | ~spl3_4)),
% 0.20/0.50    inference(superposition,[],[f77,f67])).
% 0.20/0.50  fof(f67,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | ~spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f66])).
% 0.20/0.50  fof(f98,plain,(
% 0.20/0.50    ~spl3_9),
% 0.20/0.50    inference(avatar_split_clause,[],[f33,f96])).
% 0.20/0.50  fof(f33,plain,(
% 0.20/0.50    ~v2_struct_0(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    (((k1_xboole_0 = sK1 & ~m1_orders_2(sK1,sK0,sK1)) | (m1_orders_2(sK1,sK0,sK1) & k1_xboole_0 != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f10,f24,f23])).
% 0.20/0.50  fof(f23,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,sK0,X1)) | (m1_orders_2(X1,sK0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f24,plain,(
% 0.20/0.50    ? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,sK0,X1)) | (m1_orders_2(X1,sK0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (((k1_xboole_0 = sK1 & ~m1_orders_2(sK1,sK0,sK1)) | (m1_orders_2(sK1,sK0,sK1) & k1_xboole_0 != sK1)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.50    introduced(choice_axiom,[])).
% 0.20/0.50  fof(f10,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.50    inference(flattening,[],[f9])).
% 0.20/0.50  fof(f9,plain,(
% 0.20/0.50    ? [X0] : (? [X1] : (((k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) | (m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f8])).
% 0.20/0.50  fof(f8,negated_conjecture,(
% 0.20/0.50    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.20/0.50    inference(negated_conjecture,[],[f7])).
% 0.20/0.50  fof(f7,conjecture,(
% 0.20/0.50    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k1_xboole_0 = X1 & ~m1_orders_2(X1,X0,X1)) & ~(m1_orders_2(X1,X0,X1) & k1_xboole_0 != X1))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_orders_2)).
% 0.20/0.50  fof(f94,plain,(
% 0.20/0.50    spl3_8),
% 0.20/0.50    inference(avatar_split_clause,[],[f34,f92])).
% 0.20/0.50  fof(f34,plain,(
% 0.20/0.50    v3_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f90,plain,(
% 0.20/0.50    spl3_7),
% 0.20/0.50    inference(avatar_split_clause,[],[f35,f88])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    v4_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f86,plain,(
% 0.20/0.50    spl3_6),
% 0.20/0.50    inference(avatar_split_clause,[],[f36,f84])).
% 0.20/0.50  fof(f36,plain,(
% 0.20/0.50    v5_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f82,plain,(
% 0.20/0.50    spl3_5),
% 0.20/0.50    inference(avatar_split_clause,[],[f37,f80])).
% 0.20/0.50  fof(f37,plain,(
% 0.20/0.50    l1_orders_2(sK0)),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    spl3_4),
% 0.20/0.50    inference(avatar_split_clause,[],[f38,f76])).
% 0.20/0.50  fof(f38,plain,(
% 0.20/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    ~spl3_2 | ~spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f69,f72,f66])).
% 0.20/0.50  fof(f69,plain,(
% 0.20/0.50    ~m1_orders_2(k1_xboole_0,sK0,k1_xboole_0) | k1_xboole_0 != sK1),
% 0.20/0.50    inference(inner_rewriting,[],[f39])).
% 0.20/0.50  fof(f39,plain,(
% 0.20/0.50    ~m1_orders_2(sK1,sK0,sK1) | k1_xboole_0 != sK1),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  fof(f68,plain,(
% 0.20/0.50    spl3_1 | spl3_2),
% 0.20/0.50    inference(avatar_split_clause,[],[f42,f66,f63])).
% 0.20/0.50  fof(f42,plain,(
% 0.20/0.50    k1_xboole_0 = sK1 | m1_orders_2(sK1,sK0,sK1)),
% 0.20/0.50    inference(cnf_transformation,[],[f25])).
% 0.20/0.50  % SZS output end Proof for theBenchmark
% 0.20/0.50  % (25710)------------------------------
% 0.20/0.50  % (25710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (25710)Termination reason: Refutation
% 0.20/0.50  
% 0.20/0.50  % (25710)Memory used [KB]: 10746
% 0.20/0.50  % (25710)Time elapsed: 0.077 s
% 0.20/0.50  % (25710)------------------------------
% 0.20/0.50  % (25710)------------------------------
% 0.20/0.50  % (25703)Success in time 0.138 s
%------------------------------------------------------------------------------
