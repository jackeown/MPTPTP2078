%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  150 ( 365 expanded)
%              Number of leaves         :   38 ( 182 expanded)
%              Depth                    :   12
%              Number of atoms          :  829 (2382 expanded)
%              Number of equality atoms :   54 (  66 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f78,f82,f86,f90,f94,f98,f102,f106,f110,f123,f129,f136,f141,f146,f151,f156,f166,f172,f193,f198,f210,f231,f236,f243,f251,f252])).

fof(f252,plain,
    ( sK2 != sK3
    | r2_xboole_0(sK3,sK2)
    | ~ r2_xboole_0(sK2,sK3) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f251,plain,
    ( ~ spl5_4
    | spl5_15
    | ~ spl5_5
    | ~ spl5_12
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f246,f164,f127,f88,f144,f84])).

fof(f84,plain,
    ( spl5_4
  <=> m2_orders_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f144,plain,
    ( spl5_15
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f88,plain,
    ( spl5_5
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f127,plain,
    ( spl5_12
  <=> ! [X1,X0,X2] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | r1_tarski(X2,X0)
        | ~ m1_orders_2(X2,sK0,X0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f164,plain,
    ( spl5_18
  <=> m1_orders_2(sK3,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f246,plain,
    ( r1_tarski(sK3,sK2)
    | ~ m2_orders_2(sK2,sK0,sK1)
    | ~ spl5_5
    | ~ spl5_12
    | ~ spl5_18 ),
    inference(resolution,[],[f165,f130])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ m1_orders_2(X0,sK0,X1)
        | r1_tarski(X0,X1)
        | ~ m2_orders_2(X1,sK0,sK1) )
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(resolution,[],[f128,f89])).

fof(f89,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f128,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | r1_tarski(X2,X0)
        | ~ m1_orders_2(X2,sK0,X0)
        | ~ m2_orders_2(X0,sK0,X1) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f127])).

fof(f165,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f164])).

fof(f243,plain,
    ( ~ spl5_5
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f242,f234,f208,f88])).

fof(f208,plain,
    ( spl5_24
  <=> m2_orders_2(k1_xboole_0,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f234,plain,
    ( spl5_28
  <=> ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f242,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(resolution,[],[f235,f209])).

fof(f209,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f208])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) )
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f234])).

fof(f236,plain,
    ( spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_6
    | spl5_28
    | spl5_27 ),
    inference(avatar_split_clause,[],[f232,f229,f234,f92,f96,f100,f104,f108])).

fof(f108,plain,
    ( spl5_10
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f104,plain,
    ( spl5_9
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f100,plain,
    ( spl5_8
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f96,plain,
    ( spl5_7
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f92,plain,
    ( spl5_6
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f229,plain,
    ( spl5_27
  <=> v6_orders_2(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f232,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(k1_xboole_0,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | spl5_27 ),
    inference(resolution,[],[f230,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v6_orders_2(X2,X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) )
          | ~ m2_orders_2(X2,X0,X1) )
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m2_orders_2(X2,X0,X1)
         => ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(X2,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).

fof(f230,plain,
    ( ~ v6_orders_2(k1_xboole_0,sK0)
    | spl5_27 ),
    inference(avatar_component_clause,[],[f229])).

fof(f231,plain,
    ( spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_6
    | ~ spl5_5
    | ~ spl5_27
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f225,f208,f229,f88,f92,f96,f100,f104,f108])).

fof(f225,plain,
    ( ~ v6_orders_2(k1_xboole_0,sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_24 ),
    inference(resolution,[],[f209,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
      | ~ v6_orders_2(k1_xboole_0,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f67,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m2_orders_2(k1_xboole_0,X0,X1)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(k1_xboole_0,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X2
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v6_orders_2(X2,X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ( sK4(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK4(X0,X1,X2))))
                    & r2_hidden(sK4(X0,X1,X2),X2)
                    & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X4] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X0)) )
     => ( sK4(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK4(X0,X1,X2))))
        & r2_hidden(sK4(X0,X1,X2),X2)
        & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X4] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4
                        | ~ r2_hidden(X4,X2)
                        | ~ m1_subset_1(X4,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X3] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                        | ~ r2_hidden(X3,X2)
                        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_orders_2(X2,X0,X1)
                  | ? [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3
                      & r2_hidden(X3,X2)
                      & m1_subset_1(X3,u1_struct_0(X0)) )
                  | ~ r2_wellord1(u1_orders_2(X0),X2)
                  | k1_xboole_0 = X2 )
                & ( ( ! [X3] :
                        ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                        | ~ r2_hidden(X3,X2)
                        | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                    & r2_wellord1(u1_orders_2(X0),X2)
                    & k1_xboole_0 != X2 )
                  | ~ m2_orders_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3
                      | ~ r2_hidden(X3,X2)
                      | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ v6_orders_2(X2,X0) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                & v6_orders_2(X2,X0) )
             => ( m2_orders_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,u1_struct_0(X0))
                     => ( r2_hidden(X3,X2)
                       => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 ) )
                  & r2_wellord1(u1_orders_2(X0),X2)
                  & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).

fof(f210,plain,
    ( spl5_24
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f202,f190,f84,f208])).

fof(f190,plain,
    ( spl5_22
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f202,plain,
    ( m2_orders_2(k1_xboole_0,sK0,sK1)
    | ~ spl5_4
    | ~ spl5_22 ),
    inference(superposition,[],[f85,f191])).

fof(f191,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f190])).

fof(f85,plain,
    ( m2_orders_2(sK2,sK0,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f198,plain,
    ( ~ spl5_5
    | ~ spl5_4
    | ~ spl5_11
    | spl5_21 ),
    inference(avatar_split_clause,[],[f196,f187,f121,f84,f88])).

fof(f121,plain,
    ( spl5_11
  <=> ! [X1,X0] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f187,plain,
    ( spl5_21
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f196,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl5_4
    | ~ spl5_11
    | spl5_21 ),
    inference(resolution,[],[f195,f85])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(sK2,sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) )
    | ~ spl5_11
    | spl5_21 ),
    inference(resolution,[],[f188,f122])).

fof(f122,plain,
    ( ! [X0,X1] :
        ( m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f121])).

fof(f188,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f187])).

fof(f193,plain,
    ( spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_6
    | ~ spl5_21
    | spl5_22
    | ~ spl5_19
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f184,f170,f170,f190,f187,f92,f96,f100,f104,f108])).

fof(f170,plain,
    ( spl5_19
  <=> m1_orders_2(sK2,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f184,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_19 ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( ~ m1_orders_2(sK2,sK0,sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_19 ),
    inference(resolution,[],[f171,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_orders_2(X2,X0,X1)
      | ~ m1_orders_2(X1,X0,X2)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ m1_orders_2(X2,X0,X1)
              | ~ m1_orders_2(X1,X0,X2)
              | k1_xboole_0 = X1
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).

fof(f171,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f170])).

fof(f172,plain,
    ( spl5_19
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f168,f139,f73,f170])).

fof(f73,plain,
    ( spl5_2
  <=> m1_orders_2(sK2,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f139,plain,
    ( spl5_14
  <=> sK2 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f168,plain,
    ( m1_orders_2(sK2,sK0,sK2)
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(forward_demodulation,[],[f77,f140])).

fof(f140,plain,
    ( sK2 = sK3
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f139])).

fof(f77,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f166,plain,
    ( spl5_14
    | spl5_2
    | spl5_18
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f161,f154,f88,f84,f80,f164,f73,f139])).

fof(f80,plain,
    ( spl5_3
  <=> m2_orders_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f154,plain,
    ( spl5_17
  <=> ! [X1,X0,X2] :
        ( m1_orders_2(X0,sK0,X1)
        | m1_orders_2(X1,sK0,X0)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m2_orders_2(X0,sK0,X2)
        | X0 = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f161,plain,
    ( m1_orders_2(sK3,sK0,sK2)
    | m1_orders_2(sK2,sK0,sK3)
    | sK2 = sK3
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(resolution,[],[f158,f85])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_orders_2(sK3,sK0,X0)
        | m1_orders_2(X0,sK0,sK3)
        | sK3 = X0 )
    | ~ spl5_3
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(resolution,[],[f157,f81])).

fof(f81,plain,
    ( m2_orders_2(sK3,sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f157,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | m1_orders_2(X1,sK0,X0)
        | m1_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X1,sK0,sK1)
        | X0 = X1 )
    | ~ spl5_5
    | ~ spl5_17 ),
    inference(resolution,[],[f155,f89])).

fof(f155,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | m1_orders_2(X0,sK0,X1)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m2_orders_2(X0,sK0,X2)
        | X0 = X1 )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f156,plain,
    ( spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_7
    | spl5_17
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f152,f92,f154,f96,f100,f104,f108])).

fof(f152,plain,
    ( ! [X2,X0,X1] :
        ( m1_orders_2(X0,sK0,X1)
        | X0 = X1
        | ~ m2_orders_2(X0,sK0,X2)
        | ~ m2_orders_2(X1,sK0,X2)
        | ~ m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0)))
        | m1_orders_2(X1,sK0,X0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f51,f93])).

fof(f93,plain,
    ( l1_orders_2(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | m1_orders_2(X3,X0,X2)
      | X2 = X3
      | ~ m2_orders_2(X3,X0,X1)
      | ~ m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m1_orders_2(X2,X0,X3)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( m1_orders_2(X2,X0,X3)
                      | m1_orders_2(X3,X0,X2) )
                    & ( ~ m1_orders_2(X3,X0,X2)
                      | ~ m1_orders_2(X2,X0,X3) ) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( m1_orders_2(X2,X0,X3)
                  <=> ~ m1_orders_2(X3,X0,X2) )
                  | X2 = X3
                  | ~ m2_orders_2(X3,X0,X1) )
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( X2 != X3
                   => ( m1_orders_2(X2,X0,X3)
                    <=> ~ m1_orders_2(X3,X0,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).

fof(f151,plain,
    ( ~ spl5_16
    | spl5_15 ),
    inference(avatar_split_clause,[],[f147,f144,f149])).

fof(f149,plain,
    ( spl5_16
  <=> r2_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f147,plain,
    ( ~ r2_xboole_0(sK3,sK2)
    | spl5_15 ),
    inference(resolution,[],[f145,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f145,plain,
    ( ~ r1_tarski(sK3,sK2)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f144])).

fof(f146,plain,
    ( ~ spl5_15
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f142,f70,f144])).

fof(f70,plain,
    ( spl5_1
  <=> r2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f142,plain,
    ( ~ r1_tarski(sK3,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f76,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f76,plain,
    ( r2_xboole_0(sK2,sK3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f141,plain,
    ( spl5_1
    | spl5_14
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f137,f134,f139,f70])).

fof(f134,plain,
    ( spl5_13
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f137,plain,
    ( sK2 = sK3
    | r2_xboole_0(sK2,sK3)
    | ~ spl5_13 ),
    inference(resolution,[],[f135,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f135,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f136,plain,
    ( ~ spl5_3
    | spl5_13
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f131,f127,f88,f73,f134,f80])).

fof(f131,plain,
    ( r1_tarski(sK2,sK3)
    | ~ m2_orders_2(sK3,sK0,sK1)
    | ~ spl5_2
    | ~ spl5_5
    | ~ spl5_12 ),
    inference(resolution,[],[f130,f77])).

fof(f129,plain,
    ( spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_7
    | ~ spl5_6
    | spl5_12
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f124,f121,f127,f92,f96,f100,f104,f108])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m1_orders_2(X2,sK0,X0)
        | r1_tarski(X2,X0)
        | ~ l1_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_11 ),
    inference(resolution,[],[f122,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_orders_2(X2,X0,X1)
      | r1_tarski(X2,X1)
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
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
              ( r1_tarski(X2,X1)
              | ~ m1_orders_2(X2,X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_orders_2(X2,X0,X1)
             => r1_tarski(X2,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).

fof(f123,plain,
    ( spl5_10
    | ~ spl5_9
    | ~ spl5_8
    | ~ spl5_7
    | spl5_11
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f115,f92,f121,f96,f100,f104,f108])).

fof(f115,plain,
    ( ! [X0,X1] :
        ( ~ m2_orders_2(X0,sK0,X1)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v5_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v3_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f62,f93])).

fof(f110,plain,(
    ~ spl5_10 ),
    inference(avatar_split_clause,[],[f40,f108])).

fof(f40,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ m1_orders_2(sK2,sK0,sK3)
      | ~ r2_xboole_0(sK2,sK3) )
    & ( m1_orders_2(sK2,sK0,sK3)
      | r2_xboole_0(sK2,sK3) )
    & m2_orders_2(sK3,sK0,sK1)
    & m2_orders_2(sK2,sK0,sK1)
    & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f30,f29,f28,f27])).

fof(f27,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_orders_2(X2,X0,X3)
                      | ~ r2_xboole_0(X2,X3) )
                    & ( m1_orders_2(X2,X0,X3)
                      | r2_xboole_0(X2,X3) )
                    & m2_orders_2(X3,X0,X1) )
                & m2_orders_2(X2,X0,X1) )
            & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,sK0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,sK0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,sK0,X1) )
              & m2_orders_2(X2,sK0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_orders_2(X2,sK0,X3)
                  | ~ r2_xboole_0(X2,X3) )
                & ( m1_orders_2(X2,sK0,X3)
                  | r2_xboole_0(X2,X3) )
                & m2_orders_2(X3,sK0,X1) )
            & m2_orders_2(X2,sK0,X1) )
        & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_orders_2(X2,sK0,X3)
                | ~ r2_xboole_0(X2,X3) )
              & ( m1_orders_2(X2,sK0,X3)
                | r2_xboole_0(X2,X3) )
              & m2_orders_2(X3,sK0,sK1) )
          & m2_orders_2(X2,sK0,sK1) )
      & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_orders_2(X2,sK0,X3)
              | ~ r2_xboole_0(X2,X3) )
            & ( m1_orders_2(X2,sK0,X3)
              | r2_xboole_0(X2,X3) )
            & m2_orders_2(X3,sK0,sK1) )
        & m2_orders_2(X2,sK0,sK1) )
   => ( ? [X3] :
          ( ( ~ m1_orders_2(sK2,sK0,X3)
            | ~ r2_xboole_0(sK2,X3) )
          & ( m1_orders_2(sK2,sK0,X3)
            | r2_xboole_0(sK2,X3) )
          & m2_orders_2(X3,sK0,sK1) )
      & m2_orders_2(sK2,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ( ~ m1_orders_2(sK2,sK0,X3)
          | ~ r2_xboole_0(sK2,X3) )
        & ( m1_orders_2(sK2,sK0,X3)
          | r2_xboole_0(sK2,X3) )
        & m2_orders_2(X3,sK0,sK1) )
   => ( ( ~ m1_orders_2(sK2,sK0,sK3)
        | ~ r2_xboole_0(sK2,sK3) )
      & ( m1_orders_2(sK2,sK0,sK3)
        | r2_xboole_0(sK2,sK3) )
      & m2_orders_2(sK3,sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_orders_2(X2,X0,X3)
                    | ~ r2_xboole_0(X2,X3) )
                  & ( m1_orders_2(X2,X0,X3)
                    | r2_xboole_0(X2,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( r2_xboole_0(X2,X3)
                  <~> m1_orders_2(X2,X0,X3) )
                  & m2_orders_2(X3,X0,X1) )
              & m2_orders_2(X2,X0,X1) )
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m2_orders_2(X2,X0,X1)
               => ! [X3] :
                    ( m2_orders_2(X3,X0,X1)
                   => ( r2_xboole_0(X2,X3)
                    <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => ! [X3] :
                  ( m2_orders_2(X3,X0,X1)
                 => ( r2_xboole_0(X2,X3)
                  <=> m1_orders_2(X2,X0,X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).

fof(f106,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f41,f104])).

fof(f41,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f42,f100])).

fof(f42,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f98,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f43,f96])).

fof(f43,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f94,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f44,f92])).

fof(f44,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f45,f88])).

fof(f45,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f86,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f46,f84])).

fof(f46,plain,(
    m2_orders_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f47,f80])).

fof(f47,plain,(
    m2_orders_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f48,f73,f70])).

fof(f48,plain,
    ( m1_orders_2(sK2,sK0,sK3)
    | r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f49,f73,f70])).

fof(f49,plain,
    ( ~ m1_orders_2(sK2,sK0,sK3)
    | ~ r2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:18:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (20646)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (20640)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (20654)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (20654)Refutation not found, incomplete strategy% (20654)------------------------------
% 0.22/0.48  % (20654)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (20654)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (20654)Memory used [KB]: 10618
% 0.22/0.48  % (20654)Time elapsed: 0.052 s
% 0.22/0.48  % (20654)------------------------------
% 0.22/0.48  % (20654)------------------------------
% 0.22/0.49  % (20640)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f253,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f75,f78,f82,f86,f90,f94,f98,f102,f106,f110,f123,f129,f136,f141,f146,f151,f156,f166,f172,f193,f198,f210,f231,f236,f243,f251,f252])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    sK2 != sK3 | r2_xboole_0(sK3,sK2) | ~r2_xboole_0(sK2,sK3)),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f251,plain,(
% 0.22/0.49    ~spl5_4 | spl5_15 | ~spl5_5 | ~spl5_12 | ~spl5_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f246,f164,f127,f88,f144,f84])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    spl5_4 <=> m2_orders_2(sK2,sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    spl5_15 <=> r1_tarski(sK3,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    spl5_5 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    spl5_12 <=> ! [X1,X0,X2] : (~m2_orders_2(X0,sK0,X1) | r1_tarski(X2,X0) | ~m1_orders_2(X2,sK0,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.22/0.49  fof(f164,plain,(
% 0.22/0.49    spl5_18 <=> m1_orders_2(sK3,sK0,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 0.22/0.49  fof(f246,plain,(
% 0.22/0.49    r1_tarski(sK3,sK2) | ~m2_orders_2(sK2,sK0,sK1) | (~spl5_5 | ~spl5_12 | ~spl5_18)),
% 0.22/0.49    inference(resolution,[],[f165,f130])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_orders_2(X0,sK0,X1) | r1_tarski(X0,X1) | ~m2_orders_2(X1,sK0,sK1)) ) | (~spl5_5 | ~spl5_12)),
% 0.22/0.49    inference(resolution,[],[f128,f89])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl5_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f88])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | r1_tarski(X2,X0) | ~m1_orders_2(X2,sK0,X0) | ~m2_orders_2(X0,sK0,X1)) ) | ~spl5_12),
% 0.22/0.49    inference(avatar_component_clause,[],[f127])).
% 0.22/0.49  fof(f165,plain,(
% 0.22/0.49    m1_orders_2(sK3,sK0,sK2) | ~spl5_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f164])).
% 0.22/0.49  fof(f243,plain,(
% 0.22/0.49    ~spl5_5 | ~spl5_24 | ~spl5_28),
% 0.22/0.49    inference(avatar_split_clause,[],[f242,f234,f208,f88])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    spl5_24 <=> m2_orders_2(k1_xboole_0,sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.22/0.49  fof(f234,plain,(
% 0.22/0.49    spl5_28 <=> ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (~spl5_24 | ~spl5_28)),
% 0.22/0.49    inference(resolution,[],[f235,f209])).
% 0.22/0.49  fof(f209,plain,(
% 0.22/0.49    m2_orders_2(k1_xboole_0,sK0,sK1) | ~spl5_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f208])).
% 0.22/0.49  fof(f235,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))) ) | ~spl5_28),
% 0.22/0.49    inference(avatar_component_clause,[],[f234])).
% 0.22/0.49  fof(f236,plain,(
% 0.22/0.49    spl5_10 | ~spl5_9 | ~spl5_8 | ~spl5_7 | ~spl5_6 | spl5_28 | spl5_27),
% 0.22/0.49    inference(avatar_split_clause,[],[f232,f229,f234,f92,f96,f100,f104,f108])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    spl5_10 <=> v2_struct_0(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.22/0.49  fof(f104,plain,(
% 0.22/0.49    spl5_9 <=> v3_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    spl5_8 <=> v4_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    spl5_7 <=> v5_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    spl5_6 <=> l1_orders_2(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.22/0.49  fof(f229,plain,(
% 0.22/0.49    spl5_27 <=> v6_orders_2(k1_xboole_0,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.22/0.49  fof(f232,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(k1_xboole_0,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | spl5_27),
% 0.22/0.49    inference(resolution,[],[f230,f61])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v6_orders_2(X2,X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0,X1] : (! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) | ~m2_orders_2(X2,X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X2] : (m2_orders_2(X2,X0,X1) => (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m2_orders_2)).
% 0.22/0.49  fof(f230,plain,(
% 0.22/0.49    ~v6_orders_2(k1_xboole_0,sK0) | spl5_27),
% 0.22/0.49    inference(avatar_component_clause,[],[f229])).
% 0.22/0.49  fof(f231,plain,(
% 0.22/0.49    spl5_10 | ~spl5_9 | ~spl5_8 | ~spl5_7 | ~spl5_6 | ~spl5_5 | ~spl5_27 | ~spl5_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f225,f208,f229,f88,f92,f96,f100,f104,f108])).
% 0.22/0.49  fof(f225,plain,(
% 0.22/0.49    ~v6_orders_2(k1_xboole_0,sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl5_24),
% 0.22/0.49    inference(resolution,[],[f209,f113])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m2_orders_2(k1_xboole_0,X0,X1) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f67,f62])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f23])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m2_orders_2(k1_xboole_0,X0,X1) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(k1_xboole_0,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k1_xboole_0 != X2 | ~m2_orders_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (sK4(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK4(X0,X1,X2)))) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f35,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ! [X2,X1,X0] : (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) => (sK4(X0,X1,X2) != k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,sK4(X0,X1,X2)))) & r2_hidden(sK4(X0,X1,X2),X2) & m1_subset_1(sK4(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X4] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X4))) = X4 | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(rectify,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | ? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((m2_orders_2(X2,X0,X1) | (? [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) != X3 & r2_hidden(X3,X2) & m1_subset_1(X3,u1_struct_0(X0))) | ~r2_wellord1(u1_orders_2(X0),X2) | k1_xboole_0 = X2)) & ((! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2) | ~m2_orders_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : (k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((m2_orders_2(X2,X0,X1) <=> (! [X3] : ((k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3 | ~r2_hidden(X3,X2)) | ~m1_subset_1(X3,u1_struct_0(X0))) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X2,X0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X2,X0)) => (m2_orders_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => (r2_hidden(X3,X2) => k1_funct_1(X1,k1_orders_2(X0,k3_orders_2(X0,X2,X3))) = X3)) & r2_wellord1(u1_orders_2(X0),X2) & k1_xboole_0 != X2)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_orders_2)).
% 0.22/0.49  fof(f210,plain,(
% 0.22/0.49    spl5_24 | ~spl5_4 | ~spl5_22),
% 0.22/0.49    inference(avatar_split_clause,[],[f202,f190,f84,f208])).
% 0.22/0.49  fof(f190,plain,(
% 0.22/0.49    spl5_22 <=> k1_xboole_0 = sK2),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.49  fof(f202,plain,(
% 0.22/0.49    m2_orders_2(k1_xboole_0,sK0,sK1) | (~spl5_4 | ~spl5_22)),
% 0.22/0.49    inference(superposition,[],[f85,f191])).
% 0.22/0.49  fof(f191,plain,(
% 0.22/0.49    k1_xboole_0 = sK2 | ~spl5_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f190])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    m2_orders_2(sK2,sK0,sK1) | ~spl5_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f84])).
% 0.22/0.49  fof(f198,plain,(
% 0.22/0.49    ~spl5_5 | ~spl5_4 | ~spl5_11 | spl5_21),
% 0.22/0.49    inference(avatar_split_clause,[],[f196,f187,f121,f84,f88])).
% 0.22/0.49  fof(f121,plain,(
% 0.22/0.49    spl5_11 <=> ! [X1,X0] : (~m2_orders_2(X0,sK0,X1) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    spl5_21 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (~spl5_4 | ~spl5_11 | spl5_21)),
% 0.22/0.49    inference(resolution,[],[f195,f85])).
% 0.22/0.49  fof(f195,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(sK2,sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))) ) | (~spl5_11 | spl5_21)),
% 0.22/0.49    inference(resolution,[],[f188,f122])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) ) | ~spl5_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f121])).
% 0.22/0.49  fof(f188,plain,(
% 0.22/0.49    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl5_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f187])).
% 0.22/0.49  fof(f193,plain,(
% 0.22/0.49    spl5_10 | ~spl5_9 | ~spl5_8 | ~spl5_7 | ~spl5_6 | ~spl5_21 | spl5_22 | ~spl5_19 | ~spl5_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f184,f170,f170,f190,f187,f92,f96,f100,f104,f108])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    spl5_19 <=> m1_orders_2(sK2,sK0,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.22/0.49  fof(f184,plain,(
% 0.22/0.49    ~m1_orders_2(sK2,sK0,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl5_19),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f183])).
% 0.22/0.49  fof(f183,plain,(
% 0.22/0.49    ~m1_orders_2(sK2,sK0,sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~spl5_19),
% 0.22/0.49    inference(resolution,[],[f171,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((~m1_orders_2(X2,X0,X1) | ~m1_orders_2(X1,X0,X2) | k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(m1_orders_2(X2,X0,X1) & m1_orders_2(X1,X0,X2) & k1_xboole_0 != X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_orders_2)).
% 0.22/0.49  fof(f171,plain,(
% 0.22/0.49    m1_orders_2(sK2,sK0,sK2) | ~spl5_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f170])).
% 0.22/0.49  fof(f172,plain,(
% 0.22/0.49    spl5_19 | ~spl5_2 | ~spl5_14),
% 0.22/0.49    inference(avatar_split_clause,[],[f168,f139,f73,f170])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl5_2 <=> m1_orders_2(sK2,sK0,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.49  fof(f139,plain,(
% 0.22/0.49    spl5_14 <=> sK2 = sK3),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    m1_orders_2(sK2,sK0,sK2) | (~spl5_2 | ~spl5_14)),
% 0.22/0.49    inference(forward_demodulation,[],[f77,f140])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    sK2 = sK3 | ~spl5_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f139])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    m1_orders_2(sK2,sK0,sK3) | ~spl5_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f73])).
% 0.22/0.49  fof(f166,plain,(
% 0.22/0.49    spl5_14 | spl5_2 | spl5_18 | ~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_17),
% 0.22/0.49    inference(avatar_split_clause,[],[f161,f154,f88,f84,f80,f164,f73,f139])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl5_3 <=> m2_orders_2(sK3,sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.49  fof(f154,plain,(
% 0.22/0.49    spl5_17 <=> ! [X1,X0,X2] : (m1_orders_2(X0,sK0,X1) | m1_orders_2(X1,sK0,X0) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X2) | ~m2_orders_2(X0,sK0,X2) | X0 = X1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.22/0.49  fof(f161,plain,(
% 0.22/0.49    m1_orders_2(sK3,sK0,sK2) | m1_orders_2(sK2,sK0,sK3) | sK2 = sK3 | (~spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_17)),
% 0.22/0.49    inference(resolution,[],[f158,f85])).
% 0.22/0.49  fof(f158,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | m1_orders_2(sK3,sK0,X0) | m1_orders_2(X0,sK0,sK3) | sK3 = X0) ) | (~spl5_3 | ~spl5_5 | ~spl5_17)),
% 0.22/0.49    inference(resolution,[],[f157,f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    m2_orders_2(sK3,sK0,sK1) | ~spl5_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f80])).
% 0.22/0.49  fof(f157,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,sK1) | m1_orders_2(X1,sK0,X0) | m1_orders_2(X0,sK0,X1) | ~m2_orders_2(X1,sK0,sK1) | X0 = X1) ) | (~spl5_5 | ~spl5_17)),
% 0.22/0.49    inference(resolution,[],[f155,f89])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | m1_orders_2(X0,sK0,X1) | ~m2_orders_2(X1,sK0,X2) | ~m2_orders_2(X0,sK0,X2) | X0 = X1) ) | ~spl5_17),
% 0.22/0.49    inference(avatar_component_clause,[],[f154])).
% 0.22/0.49  fof(f156,plain,(
% 0.22/0.49    spl5_10 | ~spl5_9 | ~spl5_8 | ~spl5_7 | spl5_17 | ~spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f152,f92,f154,f96,f100,f104,f108])).
% 0.22/0.49  fof(f152,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (m1_orders_2(X0,sK0,X1) | X0 = X1 | ~m2_orders_2(X0,sK0,X2) | ~m2_orders_2(X1,sK0,X2) | ~m1_orders_1(X2,k1_orders_1(u1_struct_0(sK0))) | m1_orders_2(X1,sK0,X0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_6),
% 0.22/0.49    inference(resolution,[],[f51,f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    l1_orders_2(sK0) | ~spl5_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f92])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (~l1_orders_2(X0) | m1_orders_2(X3,X0,X2) | X2 = X3 | ~m2_orders_2(X3,X0,X1) | ~m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m1_orders_2(X2,X0,X3) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f32])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) | m1_orders_2(X3,X0,X2)) & (~m1_orders_2(X3,X0,X2) | ~m1_orders_2(X2,X0,X3))) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3 | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)) | X2 = X3) | ~m2_orders_2(X3,X0,X1)) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (X2 != X3 => (m1_orders_2(X2,X0,X3) <=> ~m1_orders_2(X3,X0,X2)))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_orders_2)).
% 0.22/0.49  fof(f151,plain,(
% 0.22/0.49    ~spl5_16 | spl5_15),
% 0.22/0.49    inference(avatar_split_clause,[],[f147,f144,f149])).
% 0.22/0.49  fof(f149,plain,(
% 0.22/0.49    spl5_16 <=> r2_xboole_0(sK3,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    ~r2_xboole_0(sK3,sK2) | spl5_15),
% 0.22/0.49    inference(resolution,[],[f145,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.49    inference(flattening,[],[f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.49    inference(nnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    ~r1_tarski(sK3,sK2) | spl5_15),
% 0.22/0.49    inference(avatar_component_clause,[],[f144])).
% 0.22/0.49  fof(f146,plain,(
% 0.22/0.49    ~spl5_15 | ~spl5_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f142,f70,f144])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl5_1 <=> r2_xboole_0(sK2,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    ~r1_tarski(sK3,sK2) | ~spl5_1),
% 0.22/0.49    inference(resolution,[],[f76,f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    r2_xboole_0(sK2,sK3) | ~spl5_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f70])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    spl5_1 | spl5_14 | ~spl5_13),
% 0.22/0.49    inference(avatar_split_clause,[],[f137,f134,f139,f70])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    spl5_13 <=> r1_tarski(sK2,sK3)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    sK2 = sK3 | r2_xboole_0(sK2,sK3) | ~spl5_13),
% 0.22/0.49    inference(resolution,[],[f135,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f39])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    r1_tarski(sK2,sK3) | ~spl5_13),
% 0.22/0.49    inference(avatar_component_clause,[],[f134])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    ~spl5_3 | spl5_13 | ~spl5_2 | ~spl5_5 | ~spl5_12),
% 0.22/0.49    inference(avatar_split_clause,[],[f131,f127,f88,f73,f134,f80])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    r1_tarski(sK2,sK3) | ~m2_orders_2(sK3,sK0,sK1) | (~spl5_2 | ~spl5_5 | ~spl5_12)),
% 0.22/0.49    inference(resolution,[],[f130,f77])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    spl5_10 | ~spl5_9 | ~spl5_8 | ~spl5_7 | ~spl5_6 | spl5_12 | ~spl5_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f124,f121,f127,f92,f96,f100,f104,f108])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m1_orders_2(X2,sK0,X0) | r1_tarski(X2,X0) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_11),
% 0.22/0.49    inference(resolution,[],[f122,f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_orders_2(X2,X0,X1) | r1_tarski(X2,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X2,X1) | ~m1_orders_2(X2,X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_orders_2(X2,X0,X1) => r1_tarski(X2,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_orders_2)).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    spl5_10 | ~spl5_9 | ~spl5_8 | ~spl5_7 | spl5_11 | ~spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f115,f92,f121,f96,f100,f104,f108])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m2_orders_2(X0,sK0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl5_6),
% 0.22/0.49    inference(resolution,[],[f62,f93])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    ~spl5_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f40,f108])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ((((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f26,f30,f29,f28,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,X1)) & m2_orders_2(X2,sK0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))) => (? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) & m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ? [X2] : (? [X3] : ((~m1_orders_2(X2,sK0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,sK0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(X2,sK0,sK1)) => (? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) & m2_orders_2(sK2,sK0,sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ? [X3] : ((~m1_orders_2(sK2,sK0,X3) | ~r2_xboole_0(sK2,X3)) & (m1_orders_2(sK2,sK0,X3) | r2_xboole_0(sK2,X3)) & m2_orders_2(X3,sK0,sK1)) => ((~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)) & (m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)) & m2_orders_2(sK3,sK0,sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_orders_2(X2,X0,X3) | ~r2_xboole_0(X2,X3)) & (m1_orders_2(X2,X0,X3) | r2_xboole_0(X2,X3))) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(nnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((r2_xboole_0(X2,X3) <~> m1_orders_2(X2,X0,X3)) & m2_orders_2(X3,X0,X1)) & m2_orders_2(X2,X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f9])).
% 0.22/0.49  fof(f9,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => ! [X3] : (m2_orders_2(X3,X0,X1) => (r2_xboole_0(X2,X3) <=> m1_orders_2(X2,X0,X3))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_orders_2)).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    spl5_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f41,f104])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    v3_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    spl5_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f42,f100])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    v4_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    spl5_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f43,f96])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    v5_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    spl5_6),
% 0.22/0.49    inference(avatar_split_clause,[],[f44,f92])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    l1_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f90,plain,(
% 0.22/0.49    spl5_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f45,f88])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl5_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f46,f84])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    m2_orders_2(sK2,sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl5_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f47,f80])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    m2_orders_2(sK3,sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl5_1 | spl5_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f48,f73,f70])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    m1_orders_2(sK2,sK0,sK3) | r2_xboole_0(sK2,sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    ~spl5_1 | ~spl5_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f49,f73,f70])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ~m1_orders_2(sK2,sK0,sK3) | ~r2_xboole_0(sK2,sK3)),
% 0.22/0.49    inference(cnf_transformation,[],[f31])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (20640)------------------------------
% 0.22/0.49  % (20640)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (20640)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (20640)Memory used [KB]: 10874
% 0.22/0.49  % (20640)Time elapsed: 0.012 s
% 0.22/0.49  % (20640)------------------------------
% 0.22/0.49  % (20640)------------------------------
% 0.22/0.49  % (20646)Refutation not found, incomplete strategy% (20646)------------------------------
% 0.22/0.49  % (20646)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (20646)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (20646)Memory used [KB]: 6140
% 0.22/0.49  % (20646)Time elapsed: 0.059 s
% 0.22/0.49  % (20646)------------------------------
% 0.22/0.49  % (20646)------------------------------
% 0.22/0.50  % (20647)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (20647)Refutation not found, incomplete strategy% (20647)------------------------------
% 0.22/0.50  % (20647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (20647)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (20647)Memory used [KB]: 1663
% 0.22/0.50  % (20647)Time elapsed: 0.026 s
% 0.22/0.50  % (20647)------------------------------
% 0.22/0.50  % (20647)------------------------------
% 0.22/0.50  % (20645)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (20644)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (20633)Success in time 0.135 s
%------------------------------------------------------------------------------
