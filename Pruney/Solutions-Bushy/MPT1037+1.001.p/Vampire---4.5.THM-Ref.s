%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1037+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:08 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  160 ( 417 expanded)
%              Number of leaves         :   35 ( 173 expanded)
%              Depth                    :   23
%              Number of atoms          :  818 (2428 expanded)
%              Number of equality atoms :  124 ( 555 expanded)
%              Maximal formula depth    :   14 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f432,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f54,f58,f71,f78,f88,f92,f117,f234,f254,f257,f261,f265,f321,f326,f327,f328,f379,f390,f406,f412,f424,f426,f428,f430,f431])).

fof(f431,plain,
    ( k1_xboole_0 != sK1
    | r2_hidden(sK4(k1_xboole_0,sK1,sK2,sK3(k1_xboole_0,sK1,sK2)),k1_relset_1(k1_xboole_0,sK1,sK2))
    | ~ r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3(k1_xboole_0,k1_xboole_0,sK2)),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f430,plain,
    ( ~ spl5_4
    | ~ spl5_3
    | spl5_1
    | spl5_38 ),
    inference(avatar_split_clause,[],[f429,f419,f45,f52,f56])).

fof(f56,plain,
    ( spl5_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f52,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f45,plain,
    ( spl5_1
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f419,plain,
    ( spl5_38
  <=> v1_funct_2(sK3(sK0,sK1,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f429,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl5_38 ),
    inference(resolution,[],[f420,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK3(X0,X1,X2),X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X4] :
            ( k1_funct_1(X2,X4) = k1_funct_1(sK3(X0,X1,X2),X4)
            | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK3(X0,X1,X2),X0,X1)
        & v1_funct_1(sK3(X0,X1,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f8,f13])).

fof(f13,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(X2,X4)
              | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ! [X4] :
            ( k1_funct_1(X2,X4) = k1_funct_1(sK3(X0,X1,X2),X4)
            | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
        & m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK3(X0,X1,X2),X0,X1)
        & v1_funct_1(sK3(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(X2,X4)
              | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( k1_funct_1(X3,X4) = k1_funct_1(X2,X4)
              | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ~ ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ? [X4] :
                  ( k1_funct_1(X3,X4) != k1_funct_1(X2,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          & ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t136_funct_2)).

fof(f420,plain,
    ( ~ v1_funct_2(sK3(sK0,sK1,sK2),sK0,sK1)
    | spl5_38 ),
    inference(avatar_component_clause,[],[f419])).

fof(f428,plain,
    ( ~ spl5_4
    | ~ spl5_3
    | spl5_1
    | spl5_39 ),
    inference(avatar_split_clause,[],[f427,f422,f45,f52,f56])).

fof(f422,plain,
    ( spl5_39
  <=> m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f427,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl5_39 ),
    inference(resolution,[],[f423,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f423,plain,
    ( ~ m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | spl5_39 ),
    inference(avatar_component_clause,[],[f422])).

fof(f426,plain,
    ( ~ spl5_4
    | ~ spl5_3
    | spl5_1
    | spl5_37 ),
    inference(avatar_split_clause,[],[f425,f416,f45,f52,f56])).

fof(f416,plain,
    ( spl5_37
  <=> v1_funct_1(sK3(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f425,plain,
    ( k1_xboole_0 = sK1
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl5_37 ),
    inference(resolution,[],[f417,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK3(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f417,plain,
    ( ~ v1_funct_1(sK3(sK0,sK1,sK2))
    | spl5_37 ),
    inference(avatar_component_clause,[],[f416])).

fof(f424,plain,
    ( ~ spl5_37
    | ~ spl5_38
    | ~ spl5_39
    | ~ spl5_4
    | ~ spl5_3
    | ~ spl5_6
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f414,f410,f76,f52,f56,f422,f419,f416])).

fof(f76,plain,
    ( spl5_6
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_funct_1(sK2,sK4(sK0,sK1,sK2,X0)) = k1_funct_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2,X0))
        | ~ v1_funct_2(X0,sK0,sK1)
        | ~ v1_funct_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f410,plain,
    ( spl5_36
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_funct_1(sK2,sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0))) != k1_funct_1(sK3(sK0,sK1,X0),sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f414,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3(sK0,sK1,sK2),sK0,sK1)
    | ~ v1_funct_1(sK3(sK0,sK1,sK2))
    | ~ spl5_6
    | ~ spl5_36 ),
    inference(trivial_inequality_removal,[],[f413])).

fof(f413,plain,
    ( k1_funct_1(sK2,sK4(sK0,sK1,sK2,sK3(sK0,sK1,sK2))) != k1_funct_1(sK2,sK4(sK0,sK1,sK2,sK3(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3(sK0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3(sK0,sK1,sK2),sK0,sK1)
    | ~ v1_funct_1(sK3(sK0,sK1,sK2))
    | ~ spl5_6
    | ~ spl5_36 ),
    inference(superposition,[],[f411,f77])).

fof(f77,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK4(sK0,sK1,sK2,X0)) = k1_funct_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(X0,sK0,sK1)
        | ~ v1_funct_1(X0) )
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f411,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0))) != k1_funct_1(sK3(sK0,sK1,X0),sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0) )
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f410])).

fof(f412,plain,
    ( spl5_1
    | spl5_36
    | ~ spl5_35 ),
    inference(avatar_split_clause,[],[f408,f404,f410,f45])).

fof(f404,plain,
    ( spl5_35
  <=> ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_1(sK3(sK0,sK1,X0))
        | k1_funct_1(sK2,sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0))) != k1_funct_1(sK3(sK0,sK1,X0),sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f408,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(sK2,sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0))) != k1_funct_1(sK3(sK0,sK1,X0),sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_xboole_0 = sK1 )
    | ~ spl5_35 ),
    inference(duplicate_literal_removal,[],[f407])).

fof(f407,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | k1_funct_1(sK2,sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0))) != k1_funct_1(sK3(sK0,sK1,X0),sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0) )
    | ~ spl5_35 ),
    inference(resolution,[],[f405,f23])).

fof(f405,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3(sK0,sK1,X0))
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK2,sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0))) != k1_funct_1(sK3(sK0,sK1,X0),sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl5_35 ),
    inference(avatar_component_clause,[],[f404])).

fof(f406,plain,
    ( spl5_1
    | spl5_35
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f402,f388,f404,f45])).

fof(f388,plain,
    ( spl5_32
  <=> ! [X0] :
        ( k1_funct_1(sK2,sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0))) != k1_funct_1(sK3(sK0,sK1,X0),sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(sK3(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK3(sK0,sK1,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f402,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_funct_1(sK2,sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0))) != k1_funct_1(sK3(sK0,sK1,X0),sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0)))
        | ~ v1_funct_1(sK3(sK0,sK1,X0))
        | k1_xboole_0 = sK1 )
    | ~ spl5_32 ),
    inference(duplicate_literal_removal,[],[f401])).

fof(f401,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_funct_1(sK2,sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0))) != k1_funct_1(sK3(sK0,sK1,X0),sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0)))
        | ~ v1_funct_1(sK3(sK0,sK1,X0))
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0) )
    | ~ spl5_32 ),
    inference(resolution,[],[f389,f27])).

fof(f389,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_funct_1(sK2,sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0))) != k1_funct_1(sK3(sK0,sK1,X0),sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0)))
        | ~ v1_funct_1(sK3(sK0,sK1,X0)) )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f388])).

fof(f390,plain,
    ( spl5_1
    | spl5_32
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f386,f115,f388,f45])).

fof(f115,plain,
    ( spl5_11
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_funct_1(sK2,sK4(sK0,sK1,sK2,X0)) != k1_funct_1(X0,sK4(sK0,sK1,sK2,X0))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f386,plain,
    ( ! [X0] :
        ( k1_funct_1(sK2,sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0))) != k1_funct_1(sK3(sK0,sK1,X0),sK4(sK0,sK1,sK2,sK3(sK0,sK1,X0)))
        | ~ v1_funct_1(sK3(sK0,sK1,X0))
        | ~ m1_subset_1(sK3(sK0,sK1,X0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0) )
    | ~ spl5_11 ),
    inference(resolution,[],[f116,f25])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,sK0,sK1)
        | k1_funct_1(sK2,sK4(sK0,sK1,sK2,X0)) != k1_funct_1(X0,sK4(sK0,sK1,sK2,X0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f115])).

fof(f379,plain,
    ( ~ spl5_4
    | spl5_13
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f376,f86,f48,f45,f176,f56])).

fof(f176,plain,
    ( spl5_13
  <=> r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3(k1_xboole_0,k1_xboole_0,sK2)),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f48,plain,
    ( spl5_2
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f86,plain,
    ( spl5_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f376,plain,
    ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3(k1_xboole_0,k1_xboole_0,sK2)),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(resolution,[],[f375,f87])).

fof(f87,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f375,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3(k1_xboole_0,k1_xboole_0,X0)),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
        | ~ v1_funct_1(X0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(duplicate_literal_removal,[],[f372])).

fof(f372,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3(k1_xboole_0,k1_xboole_0,X0)),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(resolution,[],[f371,f40])).

fof(f40,plain,(
    ! [X2,X1] :
      ( v1_funct_1(sK3(k1_xboole_0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK3(X0,X1,X2))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f371,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3(k1_xboole_0,k1_xboole_0,X0))
        | r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3(k1_xboole_0,k1_xboole_0,X0)),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(duplicate_literal_removal,[],[f368])).

fof(f368,plain,
    ( ! [X0] :
        ( ~ v1_funct_1(sK3(k1_xboole_0,k1_xboole_0,X0))
        | r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3(k1_xboole_0,k1_xboole_0,X0)),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(resolution,[],[f333,f38])).

fof(f38,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK3(k1_xboole_0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK3(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(sK3(k1_xboole_0,k1_xboole_0,X0))
        | r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK2,sK3(k1_xboole_0,k1_xboole_0,X0)),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(resolution,[],[f298,f39])).

fof(f39,plain,(
    ! [X2,X1] :
      ( v1_funct_2(sK3(k1_xboole_0,X1,X2),k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f26])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK3(X0,X1,X2),X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_1(X0)
        | r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK2,X0),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK2,X0),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) )
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(superposition,[],[f196,f70])).

fof(f70,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f196,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,k1_xboole_0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK2,X0),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2)) )
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f195,f49])).

fof(f49,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK2,X0),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
        | ~ v1_funct_2(X0,sK0,sK1) )
    | ~ spl5_2
    | ~ spl5_7 ),
    inference(forward_demodulation,[],[f139,f49])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(X0,sK0,sK1)
        | ~ v1_funct_2(X0,k1_xboole_0,k1_xboole_0)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK4(k1_xboole_0,k1_xboole_0,sK2,X0),k1_relset_1(k1_xboole_0,k1_xboole_0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) )
    | ~ spl5_7 ),
    inference(resolution,[],[f87,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ v1_funct_2(X1,k1_xboole_0,X0)
      | ~ v1_funct_1(X1)
      | r2_hidden(sK4(k1_xboole_0,X0,sK2,X1),k1_relset_1(k1_xboole_0,X0,sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X1,sK0,sK1) ) ),
    inference(global_subsumption,[],[f19,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k1_xboole_0,X0,sK2,X1),k1_relset_1(k1_xboole_0,X0,sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ v1_funct_2(X1,k1_xboole_0,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X1,sK0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(k1_xboole_0,X0,sK2,X1),k1_relset_1(k1_xboole_0,X0,sK2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ v1_funct_2(X1,k1_xboole_0,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X1,sK0,sK1)
      | ~ v1_funct_1(X1) ) ),
    inference(resolution,[],[f42,f22])).

fof(f22,plain,(
    ! [X3] :
      ( ~ r1_partfun1(sK2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X3,sK0,sK1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ! [X3] :
        ( ~ r1_partfun1(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(X3,sK0,sK1)
        | ~ v1_funct_1(X3) )
    & ( k1_xboole_0 = sK0
      | k1_xboole_0 != sK1 )
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ! [X3] :
            ( ~ r1_partfun1(X2,X3)
            | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ! [X3] :
          ( ~ r1_partfun1(sK2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
          | ~ v1_funct_2(X3,sK0,sK1)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = sK0
        | k1_xboole_0 != sK1 )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ! [X3] :
          ( ~ r1_partfun1(X2,X3)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      & ( k1_xboole_0 = X0
        | k1_xboole_0 != X1 )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ~ ( ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
               => ~ r1_partfun1(X2,X3) )
            & ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ~ ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ~ r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_2)).

fof(f42,plain,(
    ! [X2,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK4(k1_xboole_0,X1,X2,X3),k1_relset_1(k1_xboole_0,X1,X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r1_partfun1(X2,X3)
              | ( k1_funct_1(X3,sK4(X0,X1,X2,X3)) != k1_funct_1(X2,sK4(X0,X1,X2,X3))
                & r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2)) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X3,X5) = k1_funct_1(X2,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f16,f17])).

fof(f17,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X3,X4) != k1_funct_1(X2,X4)
          & r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
     => ( k1_funct_1(X3,sK4(X0,X1,X2,X3)) != k1_funct_1(X2,sK4(X0,X1,X2,X3))
        & r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r1_partfun1(X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X3,X4) != k1_funct_1(X2,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            & ( ! [X5] :
                  ( k1_funct_1(X3,X5) = k1_funct_1(X2,X5)
                  | ~ r2_hidden(X5,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(rectify,[],[f15])).

% (23182)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (23184)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% (23183)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( ( r1_partfun1(X2,X3)
              | ? [X4] :
                  ( k1_funct_1(X3,X4) != k1_funct_1(X2,X4)
                  & r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
            & ( ! [X4] :
                  ( k1_funct_1(X3,X4) = k1_funct_1(X2,X4)
                  | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) )
              | ~ r1_partfun1(X2,X3) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r1_partfun1(X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X3,X4) = k1_funct_1(X2,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( r1_partfun1(X2,X3)
          <=> ! [X4] :
                ( k1_funct_1(X3,X4) = k1_funct_1(X2,X4)
                | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2)) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(X3,X0,X1)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( ( k1_xboole_0 = X1
             => k1_xboole_0 = X0 )
           => ( r1_partfun1(X2,X3)
            <=> ! [X4] :
                  ( r2_hidden(X4,k1_relset_1(X0,X1,X2))
                 => k1_funct_1(X3,X4) = k1_funct_1(X2,X4) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_2)).

fof(f19,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f328,plain,
    ( k1_xboole_0 != sK1
    | v1_funct_2(sK3(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_2(sK3(k1_xboole_0,sK1,sK2),k1_xboole_0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f327,plain,
    ( k1_xboole_0 != sK1
    | v1_funct_1(sK3(k1_xboole_0,k1_xboole_0,sK2))
    | ~ v1_funct_1(sK3(k1_xboole_0,sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f326,plain,
    ( k1_xboole_0 != sK1
    | m1_subset_1(sK3(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ m1_subset_1(sK3(k1_xboole_0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f321,plain,
    ( ~ spl5_27
    | ~ spl5_28
    | ~ spl5_29
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f311,f252,f48,f45,f319,f316,f313])).

fof(f313,plain,
    ( spl5_27
  <=> m1_subset_1(sK3(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f316,plain,
    ( spl5_28
  <=> v1_funct_2(sK3(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f319,plain,
    ( spl5_29
  <=> v1_funct_1(sK3(k1_xboole_0,k1_xboole_0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f252,plain,
    ( spl5_24
  <=> r1_partfun1(sK2,sK3(k1_xboole_0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f311,plain,
    ( ~ v1_funct_1(sK3(k1_xboole_0,k1_xboole_0,sK2))
    | ~ v1_funct_2(sK3(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK3(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f310,f70])).

fof(f310,plain,
    ( ~ v1_funct_2(sK3(k1_xboole_0,k1_xboole_0,sK2),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(sK3(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK3(k1_xboole_0,sK1,sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f309,f49])).

fof(f309,plain,
    ( ~ v1_funct_2(sK3(k1_xboole_0,k1_xboole_0,sK2),sK0,k1_xboole_0)
    | ~ m1_subset_1(sK3(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_1(sK3(k1_xboole_0,sK1,sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f308,f70])).

fof(f308,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(sK3(k1_xboole_0,sK1,sK2),sK0,sK1)
    | ~ v1_funct_1(sK3(k1_xboole_0,sK1,sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f307,f49])).

fof(f307,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0,k1_xboole_0,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,k1_xboole_0)))
    | ~ v1_funct_2(sK3(k1_xboole_0,sK1,sK2),sK0,sK1)
    | ~ v1_funct_1(sK3(k1_xboole_0,sK1,sK2))
    | ~ spl5_1
    | ~ spl5_24 ),
    inference(forward_demodulation,[],[f305,f70])).

fof(f305,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK3(k1_xboole_0,sK1,sK2),sK0,sK1)
    | ~ v1_funct_1(sK3(k1_xboole_0,sK1,sK2))
    | ~ spl5_24 ),
    inference(resolution,[],[f253,f22])).

fof(f253,plain,
    ( r1_partfun1(sK2,sK3(k1_xboole_0,sK1,sK2))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f252])).

fof(f265,plain,
    ( ~ spl5_4
    | ~ spl5_8
    | spl5_22 ),
    inference(avatar_split_clause,[],[f263,f245,f90,f56])).

fof(f90,plain,
    ( spl5_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f245,plain,
    ( spl5_22
  <=> m1_subset_1(sK3(k1_xboole_0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f263,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl5_22 ),
    inference(resolution,[],[f246,f38])).

fof(f246,plain,
    ( ~ m1_subset_1(sK3(k1_xboole_0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | spl5_22 ),
    inference(avatar_component_clause,[],[f245])).

fof(f261,plain,
    ( ~ spl5_4
    | ~ spl5_8
    | spl5_23 ),
    inference(avatar_split_clause,[],[f259,f248,f90,f56])).

fof(f248,plain,
    ( spl5_23
  <=> v1_funct_2(sK3(k1_xboole_0,sK1,sK2),k1_xboole_0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f259,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl5_23 ),
    inference(resolution,[],[f249,f39])).

fof(f249,plain,
    ( ~ v1_funct_2(sK3(k1_xboole_0,sK1,sK2),k1_xboole_0,sK1)
    | spl5_23 ),
    inference(avatar_component_clause,[],[f248])).

fof(f257,plain,
    ( ~ spl5_4
    | ~ spl5_8
    | spl5_21 ),
    inference(avatar_split_clause,[],[f255,f242,f90,f56])).

fof(f242,plain,
    ( spl5_21
  <=> v1_funct_1(sK3(k1_xboole_0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f255,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl5_21 ),
    inference(resolution,[],[f243,f40])).

fof(f243,plain,
    ( ~ v1_funct_1(sK3(k1_xboole_0,sK1,sK2))
    | spl5_21 ),
    inference(avatar_component_clause,[],[f242])).

fof(f254,plain,
    ( ~ spl5_4
    | ~ spl5_8
    | ~ spl5_21
    | ~ spl5_23
    | ~ spl5_22
    | spl5_24
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f239,f232,f252,f245,f248,f242,f90,f56])).

fof(f232,plain,
    ( spl5_20
  <=> k1_funct_1(sK2,sK4(k1_xboole_0,sK1,sK2,sK3(k1_xboole_0,sK1,sK2))) = k1_funct_1(sK3(k1_xboole_0,sK1,sK2),sK4(k1_xboole_0,sK1,sK2,sK3(k1_xboole_0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

% (23186)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f239,plain,
    ( r1_partfun1(sK2,sK3(k1_xboole_0,sK1,sK2))
    | ~ m1_subset_1(sK3(k1_xboole_0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_2(sK3(k1_xboole_0,sK1,sK2),k1_xboole_0,sK1)
    | ~ v1_funct_1(sK3(k1_xboole_0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_20 ),
    inference(trivial_inequality_removal,[],[f238])).

fof(f238,plain,
    ( k1_funct_1(sK2,sK4(k1_xboole_0,sK1,sK2,sK3(k1_xboole_0,sK1,sK2))) != k1_funct_1(sK2,sK4(k1_xboole_0,sK1,sK2,sK3(k1_xboole_0,sK1,sK2)))
    | r1_partfun1(sK2,sK3(k1_xboole_0,sK1,sK2))
    | ~ m1_subset_1(sK3(k1_xboole_0,sK1,sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_2(sK3(k1_xboole_0,sK1,sK2),k1_xboole_0,sK1)
    | ~ v1_funct_1(sK3(k1_xboole_0,sK1,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_20 ),
    inference(superposition,[],[f41,f233])).

fof(f233,plain,
    ( k1_funct_1(sK2,sK4(k1_xboole_0,sK1,sK2,sK3(k1_xboole_0,sK1,sK2))) = k1_funct_1(sK3(k1_xboole_0,sK1,sK2),sK4(k1_xboole_0,sK1,sK2,sK3(k1_xboole_0,sK1,sK2)))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f232])).

fof(f41,plain,(
    ! [X2,X3,X1] :
      ( k1_funct_1(X3,sK4(k1_xboole_0,X1,X2,X3)) != k1_funct_1(X2,sK4(k1_xboole_0,X1,X2,X3))
      | r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X3,k1_xboole_0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | k1_funct_1(X3,sK4(X0,X1,X2,X3)) != k1_funct_1(X2,sK4(X0,X1,X2,X3))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f234,plain,
    ( ~ spl5_4
    | ~ spl5_8
    | spl5_20
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f223,f219,f232,f90,f56])).

fof(f219,plain,
    ( spl5_18
  <=> r2_hidden(sK4(k1_xboole_0,sK1,sK2,sK3(k1_xboole_0,sK1,sK2)),k1_relset_1(k1_xboole_0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f223,plain,
    ( k1_funct_1(sK2,sK4(k1_xboole_0,sK1,sK2,sK3(k1_xboole_0,sK1,sK2))) = k1_funct_1(sK3(k1_xboole_0,sK1,sK2),sK4(k1_xboole_0,sK1,sK2,sK3(k1_xboole_0,sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl5_18 ),
    inference(resolution,[],[f220,f37])).

fof(f37,plain,(
    ! [X4,X2,X1] :
      ( ~ r2_hidden(X4,k1_relset_1(k1_xboole_0,X1,X2))
      | k1_funct_1(X2,X4) = k1_funct_1(sK3(k1_xboole_0,X1,X2),X4)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f30])).

fof(f30,plain,(
    ! [X4,X2,X0,X1] :
      ( k1_funct_1(X2,X4) = k1_funct_1(sK3(X0,X1,X2),X4)
      | ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f220,plain,
    ( r2_hidden(sK4(k1_xboole_0,sK1,sK2,sK3(k1_xboole_0,sK1,sK2)),k1_relset_1(k1_xboole_0,sK1,sK2))
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f219])).

fof(f117,plain,
    ( spl5_11
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f113,f52,f45,f115])).

fof(f113,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK1
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(X0,sK0,sK1)
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK2,sK4(sK0,sK1,sK2,X0)) != k1_funct_1(X0,sK4(sK0,sK1,sK2,X0)) )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f112])).

fof(f112,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK1
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(X0,sK0,sK1)
        | ~ v1_funct_1(X0)
        | k1_funct_1(sK2,sK4(sK0,sK1,sK2,X0)) != k1_funct_1(X0,sK4(sK0,sK1,sK2,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(X0,sK0,sK1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f111,f53])).

fof(f53,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f52])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | k1_funct_1(X0,sK4(X1,X2,sK2,X0)) != k1_funct_1(sK2,sK4(X1,X2,sK2,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X0,sK0,sK1) ) ),
    inference(global_subsumption,[],[f19,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,sK4(X1,X2,sK2,X0)) != k1_funct_1(sK2,sK4(X1,X2,sK2,X0))
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X0,sK0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f109])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X0,sK4(X1,X2,sK2,X0)) != k1_funct_1(sK2,sK4(X1,X2,sK2,X0))
      | k1_xboole_0 = X2
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ v1_funct_1(X0) ) ),
    inference(resolution,[],[f35,f22])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | k1_funct_1(X3,sK4(X0,X1,X2,X3)) != k1_funct_1(X2,sK4(X0,X1,X2,X3))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,
    ( spl5_8
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f80,f52,f48,f90])).

fof(f80,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(superposition,[],[f53,f49])).

fof(f88,plain,
    ( spl5_7
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f84,f52,f48,f45,f86])).

fof(f84,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f80,f70])).

fof(f78,plain,
    ( ~ spl5_4
    | ~ spl5_3
    | spl5_1
    | spl5_6
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f72,f68,f76,f45,f52,f56])).

fof(f68,plain,
    ( spl5_5
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | r2_hidden(sK4(sK0,sK1,sK2,X0),k1_relset_1(sK0,sK1,sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f72,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK1)
        | k1_funct_1(sK2,sK4(sK0,sK1,sK2,X0)) = k1_funct_1(sK3(sK0,sK1,sK2),sK4(sK0,sK1,sK2,X0))
        | k1_xboole_0 = sK1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(sK2) )
    | ~ spl5_5 ),
    inference(resolution,[],[f69,f29])).

fof(f29,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,k1_relset_1(X0,X1,X2))
      | k1_funct_1(X2,X4) = k1_funct_1(sK3(X0,X1,X2),X4)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,
    ( ! [X0] :
        ( r2_hidden(sK4(sK0,sK1,sK2,X0),k1_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,sK0,sK1) )
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f71,plain,
    ( spl5_5
    | spl5_1
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f66,f52,f45,f68])).

fof(f66,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK1
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(X0,sK0,sK1)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK4(sK0,sK1,sK2,X0),k1_relset_1(sK0,sK1,sK2)) )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK1
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(X0,sK0,sK1)
        | ~ v1_funct_1(X0)
        | r2_hidden(sK4(sK0,sK1,sK2,X0),k1_relset_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(X0,sK0,sK1) )
    | ~ spl5_3 ),
    inference(resolution,[],[f64,f53])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | r2_hidden(sK4(X0,X1,sK2,X2),k1_relset_1(X0,X1,sK2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X2,sK0,sK1) ) ),
    inference(global_subsumption,[],[f19,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,sK2,X2),k1_relset_1(X0,X1,sK2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X2,sK0,sK1) ) ),
    inference(duplicate_literal_removal,[],[f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,sK2,X2),k1_relset_1(X0,X1,sK2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(sK2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_2(X2,sK0,sK1)
      | ~ v1_funct_1(X2) ) ),
    inference(resolution,[],[f33,f22])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X2,X3)
      | r2_hidden(sK4(X0,X1,X2,X3),k1_relset_1(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f19,f56])).

fof(f54,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f12])).

fof(f50,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f21,f48,f45])).

fof(f21,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f12])).

%------------------------------------------------------------------------------
