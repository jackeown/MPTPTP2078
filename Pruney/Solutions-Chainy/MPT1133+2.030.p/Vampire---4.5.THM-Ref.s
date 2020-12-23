%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:34 EST 2020

% Result     : Theorem 3.78s
% Output     : Refutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :  424 (2375 expanded)
%              Number of leaves         :   62 ( 875 expanded)
%              Depth                    :   24
%              Number of atoms          : 1898 (22660 expanded)
%              Number of equality atoms :  102 (2014 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8925,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f147,f148,f801,f895,f899,f972,f977,f1367,f1905,f2343,f2586,f2598,f2694,f2893,f4415,f4450,f4498,f4579,f4613,f4619,f4628,f4634,f4671,f4708,f4716,f4860,f4866,f7203,f7996,f8245,f8835,f8836,f8859,f8878,f8880,f8882,f8884,f8885,f8886,f8887,f8901,f8903,f8917])).

fof(f8917,plain,
    ( ~ spl8_12
    | spl8_22 ),
    inference(avatar_split_clause,[],[f8784,f426,f238])).

fof(f238,plain,
    ( spl8_12
  <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f426,plain,
    ( spl8_22
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f8784,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | spl8_22 ),
    inference(duplicate_literal_removal,[],[f433])).

fof(f433,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | spl8_22 ),
    inference(superposition,[],[f428,f157])).

fof(f157,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X1,X0) = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f133,f154])).

fof(f154,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f97,f93])).

fof(f93,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK5(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f55,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f97,plain,(
    ! [X0] :
      ( r2_hidden(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0] :
      ( ( sP0(sK6(X0),X0)
        & r2_hidden(sK6(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
     => ( sP0(sK6(X0),X0)
        & r2_hidden(sK6(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( sP0(X1,X0)
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(definition_folding,[],[f32,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ! [X2,X3,X4,X5] :
          ( k4_mcart_1(X2,X3,X4,X5) != X1
          | ( ~ r2_hidden(X3,X0)
            & ~ r2_hidden(X2,X0) ) )
      | ~ sP0(X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f32,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).

fof(f133,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f112])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f428,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | spl8_22 ),
    inference(avatar_component_clause,[],[f426])).

fof(f8903,plain,
    ( ~ spl8_44
    | ~ spl8_37
    | spl8_39 ),
    inference(avatar_split_clause,[],[f2696,f1579,f1365,f1669])).

fof(f1669,plain,
    ( spl8_44
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).

fof(f1365,plain,
    ( spl8_37
  <=> ! [X6] :
        ( v1_partfun1(X6,k1_xboole_0)
        | ~ v1_xboole_0(X6) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).

fof(f1579,plain,
    ( spl8_39
  <=> v1_xboole_0(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).

fof(f2696,plain,
    ( ~ v1_xboole_0(sK3)
    | ~ spl8_37
    | spl8_39 ),
    inference(subsumption_resolution,[],[f2695,f373])).

fof(f373,plain,(
    ! [X4,X3] :
      ( v4_relat_1(X3,X4)
      | ~ v1_xboole_0(X3) ) ),
    inference(resolution,[],[f120,f158])).

fof(f158,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f85,f154])).

fof(f85,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2695,plain,
    ( ~ v4_relat_1(sK3,k1_xboole_0)
    | ~ v1_xboole_0(sK3)
    | ~ spl8_37
    | spl8_39 ),
    inference(subsumption_resolution,[],[f1770,f83])).

fof(f83,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f1770,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v4_relat_1(sK3,k1_xboole_0)
    | ~ v1_xboole_0(sK3)
    | ~ spl8_37
    | spl8_39 ),
    inference(resolution,[],[f1689,f1366])).

fof(f1366,plain,
    ( ! [X6] :
        ( v1_partfun1(X6,k1_xboole_0)
        | ~ v1_xboole_0(X6) )
    | ~ spl8_37 ),
    inference(avatar_component_clause,[],[f1365])).

fof(f1689,plain,
    ( ! [X0] :
        ( ~ v1_partfun1(sK3,X0)
        | ~ v1_xboole_0(X0)
        | ~ v4_relat_1(sK3,X0) )
    | spl8_39 ),
    inference(subsumption_resolution,[],[f1688,f254])).

fof(f254,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f119,f76])).

fof(f76,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | ~ v5_pre_topc(sK3,sK1,sK2) )
    & ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
      | v5_pre_topc(sK3,sK1,sK2) )
    & sK3 = sK4
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f46,f50,f49,f48,f47])).

fof(f47,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK1,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK1,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK1,X1) )
                & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK1,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
                | ~ v5_pre_topc(X2,sK1,sK2) )
              & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
                | v5_pre_topc(X2,sK1,sK2) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
              & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
          & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
              | ~ v5_pre_topc(X2,sK1,sK2) )
            & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
              | v5_pre_topc(X2,sK1,sK2) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
            & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
        & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
            | ~ v5_pre_topc(sK3,sK1,sK2) )
          & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
            | v5_pre_topc(sK3,sK1,sK2) )
          & sK3 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
          & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
      & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
          | ~ v5_pre_topc(sK3,sK1,sK2) )
        & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
          | v5_pre_topc(sK3,sK1,sK2) )
        & sK3 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
        & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | ~ v5_pre_topc(sK3,sK1,sK2) )
      & ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | v5_pre_topc(sK3,sK1,sK2) )
      & sK3 = sK4
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
      & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1688,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ v1_partfun1(sK3,X0)
        | ~ v4_relat_1(sK3,X0)
        | ~ v1_relat_1(sK3) )
    | spl8_39 ),
    inference(superposition,[],[f1581,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f1581,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | spl8_39 ),
    inference(avatar_component_clause,[],[f1579])).

fof(f8901,plain,
    ( ~ spl8_9
    | spl8_55 ),
    inference(avatar_split_clause,[],[f8789,f1951,f224])).

fof(f224,plain,
    ( spl8_9
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f1951,plain,
    ( spl8_55
  <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).

fof(f8789,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl8_55 ),
    inference(duplicate_literal_removal,[],[f2067])).

fof(f2067,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_xboole_0(u1_struct_0(sK2))
    | spl8_55 ),
    inference(superposition,[],[f1953,f157])).

fof(f1953,plain,
    ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
    | spl8_55 ),
    inference(avatar_component_clause,[],[f1951])).

fof(f8887,plain,(
    spl8_165 ),
    inference(avatar_split_clause,[],[f74,f8819])).

fof(f8819,plain,
    ( spl8_165
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_165])])).

fof(f74,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f51])).

fof(f8886,plain,(
    spl8_167 ),
    inference(avatar_split_clause,[],[f75,f8838])).

fof(f8838,plain,
    ( spl8_167
  <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_167])])).

fof(f75,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f51])).

fof(f8885,plain,(
    spl8_168 ),
    inference(avatar_split_clause,[],[f76,f8842])).

fof(f8842,plain,
    ( spl8_168
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_168])])).

fof(f8884,plain,(
    spl8_166 ),
    inference(avatar_split_clause,[],[f151,f8823])).

fof(f8823,plain,
    ( spl8_166
  <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_166])])).

fof(f151,plain,(
    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(forward_demodulation,[],[f78,f80])).

fof(f80,plain,(
    sK3 = sK4 ),
    inference(cnf_transformation,[],[f51])).

fof(f78,plain,(
    v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(cnf_transformation,[],[f51])).

fof(f8882,plain,
    ( ~ spl8_36
    | ~ spl8_34
    | spl8_1
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f4749,f959,f140,f955,f963])).

fof(f963,plain,
    ( spl8_36
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).

fof(f955,plain,
    ( spl8_34
  <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).

fof(f140,plain,
    ( spl8_1
  <=> v5_pre_topc(sK3,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f959,plain,
    ( spl8_35
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).

fof(f4749,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f4748,f70])).

fof(f70,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f4748,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f4747,f71])).

fof(f71,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f51])).

fof(f4747,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f4746,f72])).

fof(f72,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f4746,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f4745,f73])).

fof(f73,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f4745,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f4744,f75])).

fof(f4744,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f4743,f76])).

fof(f4743,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f3547,f74])).

fof(f3547,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ spl8_35 ),
    inference(resolution,[],[f3336,f858])).

fof(f858,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)))
      | v5_pre_topc(X0,X1,X2)
      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2) ) ),
    inference(resolution,[],[f136,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f136,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f126])).

fof(f126,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f92])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                    & ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f3336,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))
    | ~ spl8_35 ),
    inference(resolution,[],[f960,f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f960,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ spl8_35 ),
    inference(avatar_component_clause,[],[f959])).

fof(f8880,plain,
    ( ~ spl8_167
    | ~ spl8_168
    | ~ spl8_165
    | ~ spl8_34
    | spl8_36
    | ~ spl8_1
    | ~ spl8_35 ),
    inference(avatar_split_clause,[],[f7405,f959,f140,f963,f955,f8819,f8842,f8838])).

fof(f7405,plain,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f7404,f70])).

fof(f7404,plain,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK1)
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f7403,f71])).

fof(f7403,plain,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f7402,f72])).

fof(f7402,plain,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_35 ),
    inference(subsumption_resolution,[],[f4116,f73])).

fof(f4116,plain,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_35 ),
    inference(resolution,[],[f960,f135])).

fof(f135,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f8878,plain,
    ( ~ spl8_44
    | ~ spl8_12
    | spl8_29 ),
    inference(avatar_split_clause,[],[f1345,f878,f238,f1669])).

fof(f878,plain,
    ( spl8_29
  <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).

fof(f1345,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_xboole_0(sK3)
    | spl8_29 ),
    inference(resolution,[],[f595,f880])).

fof(f880,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | spl8_29 ),
    inference(avatar_component_clause,[],[f878])).

fof(f595,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,X1,X2)
      | ~ v1_xboole_0(X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f575,f154])).

fof(f575,plain,(
    ! [X10,X11] :
      ( v1_funct_2(k1_xboole_0,X10,X11)
      | ~ v1_xboole_0(X11) ) ),
    inference(superposition,[],[f118,f543])).

fof(f543,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = sK7(X3,X2)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f539,f97])).

fof(f539,plain,(
    ! [X12,X10,X11] :
      ( ~ r2_hidden(X10,sK7(X11,X12))
      | ~ v1_xboole_0(X12) ) ),
    inference(duplicate_literal_removal,[],[f534])).

fof(f534,plain,(
    ! [X12,X10,X11] :
      ( ~ r2_hidden(X10,sK7(X11,X12))
      | ~ v1_xboole_0(X12)
      | ~ v1_xboole_0(X12) ) ),
    inference(resolution,[],[f407,f206])).

fof(f206,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK7(X1,X0),X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f204,f154])).

fof(f204,plain,(
    ! [X0] : r1_tarski(sK7(X0,k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[],[f201,f108])).

fof(f201,plain,(
    ! [X0] : m1_subset_1(sK7(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f113,f133])).

fof(f113,plain,(
    ! [X0,X1] : m1_subset_1(sK7(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_funct_2(sK7(X0,X1),X0,X1)
      & v1_funct_1(sK7(X0,X1))
      & v5_relat_1(sK7(X0,X1),X1)
      & v4_relat_1(sK7(X0,X1),X0)
      & v1_relat_1(sK7(X0,X1))
      & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f15,f68])).

fof(f68,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2)
          & v5_relat_1(X2,X1)
          & v4_relat_1(X2,X0)
          & v1_relat_1(X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( v1_funct_2(sK7(X0,X1),X0,X1)
        & v1_funct_1(sK7(X0,X1))
        & v5_relat_1(sK7(X0,X1),X1)
        & v4_relat_1(sK7(X0,X1),X0)
        & v1_relat_1(sK7(X0,X1))
        & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2)
      & v5_relat_1(X2,X1)
      & v4_relat_1(X2,X0)
      & v1_relat_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

fof(f407,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X0)
      | ~ r2_hidden(X1,X2)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f123,f109])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f118,plain,(
    ! [X0,X1] : v1_funct_2(sK7(X0,X1),X0,X1) ),
    inference(cnf_transformation,[],[f69])).

fof(f8859,plain,
    ( ~ spl8_34
    | ~ spl8_35
    | ~ spl8_165
    | ~ spl8_166
    | spl8_122
    | ~ spl8_36
    | ~ spl8_32
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f8858,f951,f947,f963,f4758,f8823,f8819,f959,f955])).

fof(f4758,plain,
    ( spl8_122
  <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).

fof(f947,plain,
    ( spl8_32
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f951,plain,
    ( spl8_33
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).

fof(f8858,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ spl8_32
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f8857,f948])).

fof(f948,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f947])).

fof(f8857,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f7480,f952])).

fof(f952,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_33 ),
    inference(avatar_component_clause,[],[f951])).

fof(f7480,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f7479,f72])).

fof(f7479,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f2872,f73])).

fof(f2872,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f153,f137])).

fof(f137,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,X1)
      | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f125])).

fof(f125,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v5_pre_topc(X2,X0,X1)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v5_pre_topc(X2,X0,X1)
                      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) ) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f153,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
    inference(forward_demodulation,[],[f79,f80])).

fof(f79,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
    inference(cnf_transformation,[],[f51])).

fof(f8836,plain,
    ( ~ spl8_122
    | spl8_2 ),
    inference(avatar_split_clause,[],[f3467,f144,f4758])).

fof(f144,plain,
    ( spl8_2
  <=> v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f3467,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | spl8_2 ),
    inference(forward_demodulation,[],[f146,f80])).

fof(f146,plain,
    ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f144])).

fof(f8835,plain,
    ( ~ spl8_34
    | ~ spl8_35
    | ~ spl8_165
    | ~ spl8_166
    | spl8_36
    | ~ spl8_122
    | ~ spl8_32
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f8834,f951,f947,f4758,f963,f8823,f8819,f959,f955])).

fof(f8834,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ spl8_32
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f8833,f948])).

fof(f8833,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f7523,f952])).

fof(f7523,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f7522,f72])).

fof(f7522,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f2871,f73])).

fof(f2871,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f153,f138])).

fof(f138,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | v5_pre_topc(X3,X0,X1)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f124])).

fof(f124,plain,(
    ! [X0,X3,X1] :
      ( v5_pre_topc(X3,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X3)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f8245,plain,
    ( ~ spl8_40
    | spl8_60
    | ~ spl8_61
    | ~ spl8_89 ),
    inference(avatar_contradiction_clause,[],[f8244])).

fof(f8244,plain,
    ( $false
    | ~ spl8_40
    | spl8_60
    | ~ spl8_61
    | ~ spl8_89 ),
    inference(subsumption_resolution,[],[f8243,f2111])).

fof(f2111,plain,
    ( k1_xboole_0 != u1_struct_0(sK1)
    | spl8_60 ),
    inference(avatar_component_clause,[],[f2110])).

fof(f2110,plain,
    ( spl8_60
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).

fof(f8243,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl8_40
    | ~ spl8_61
    | ~ spl8_89 ),
    inference(subsumption_resolution,[],[f8221,f83])).

fof(f8221,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl8_40
    | ~ spl8_61
    | ~ spl8_89 ),
    inference(resolution,[],[f2760,f5673])).

fof(f5673,plain,
    ( ! [X2,X3] :
        ( ~ v1_partfun1(X2,X3)
        | ~ v1_xboole_0(X2)
        | k1_xboole_0 = X3 )
    | ~ spl8_61
    | ~ spl8_89 ),
    inference(subsumption_resolution,[],[f5672,f261])).

fof(f261,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f253,f154])).

fof(f253,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[],[f119,f85])).

fof(f5672,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = X3
        | ~ v1_xboole_0(X2)
        | ~ v1_partfun1(X2,X3)
        | ~ v1_relat_1(X2) )
    | ~ spl8_61
    | ~ spl8_89 ),
    inference(subsumption_resolution,[],[f5658,f373])).

fof(f5658,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = X3
        | ~ v1_xboole_0(X2)
        | ~ v1_partfun1(X2,X3)
        | ~ v4_relat_1(X2,X3)
        | ~ v1_relat_1(X2) )
    | ~ spl8_61
    | ~ spl8_89 ),
    inference(superposition,[],[f5650,f103])).

fof(f5650,plain,
    ( ! [X1] :
        ( k1_xboole_0 = k1_relat_1(X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl8_61
    | ~ spl8_89 ),
    inference(resolution,[],[f5603,f97])).

fof(f5603,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k1_relat_1(X2))
        | ~ v1_xboole_0(X2) )
    | ~ spl8_61
    | ~ spl8_89 ),
    inference(duplicate_literal_removal,[],[f5591])).

fof(f5591,plain,
    ( ! [X2,X3] :
        ( ~ v1_xboole_0(X2)
        | ~ r2_hidden(X3,k1_relat_1(X2))
        | ~ v1_xboole_0(X2) )
    | ~ spl8_61
    | ~ spl8_89 ),
    inference(resolution,[],[f5288,f407])).

fof(f5288,plain,
    ( ! [X0] :
        ( r1_tarski(k1_relat_1(X0),X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl8_61
    | ~ spl8_89 ),
    inference(superposition,[],[f5169,f154])).

fof(f5169,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0)
    | ~ spl8_61
    | ~ spl8_89 ),
    inference(forward_demodulation,[],[f3145,f2115])).

fof(f2115,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_61 ),
    inference(avatar_component_clause,[],[f2114])).

fof(f2114,plain,
    ( spl8_61
  <=> k1_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).

fof(f3145,plain,
    ( r1_tarski(k1_relat_1(sK3),sK3)
    | ~ spl8_89 ),
    inference(avatar_component_clause,[],[f3144])).

fof(f3144,plain,
    ( spl8_89
  <=> r1_tarski(k1_relat_1(sK3),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).

fof(f2760,plain,
    ( v1_partfun1(k1_xboole_0,u1_struct_0(sK1))
    | ~ spl8_40
    | ~ spl8_61 ),
    inference(backward_demodulation,[],[f1627,f2115])).

fof(f1627,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | ~ spl8_40 ),
    inference(avatar_component_clause,[],[f1625])).

fof(f1625,plain,
    ( spl8_40
  <=> v1_partfun1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).

fof(f7996,plain,
    ( ~ spl8_12
    | spl8_47 ),
    inference(avatar_split_clause,[],[f1765,f1751,f238])).

fof(f1751,plain,
    ( spl8_47
  <=> r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).

fof(f1765,plain,
    ( ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | spl8_47 ),
    inference(resolution,[],[f1753,f159])).

fof(f159,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f84,f154])).

fof(f84,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f1753,plain,
    ( ~ r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK3)
    | spl8_47 ),
    inference(avatar_component_clause,[],[f1751])).

fof(f7203,plain,
    ( spl8_1
    | ~ spl8_31
    | ~ spl8_48
    | ~ spl8_60
    | ~ spl8_61 ),
    inference(avatar_contradiction_clause,[],[f7202])).

fof(f7202,plain,
    ( $false
    | spl8_1
    | ~ spl8_31
    | ~ spl8_48
    | ~ spl8_60
    | ~ spl8_61 ),
    inference(subsumption_resolution,[],[f7201,f83])).

fof(f7201,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl8_1
    | ~ spl8_31
    | ~ spl8_48
    | ~ spl8_60
    | ~ spl8_61 ),
    inference(forward_demodulation,[],[f7200,f328])).

fof(f328,plain,(
    ! [X8] : k1_xboole_0 = sK7(X8,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f321,f84])).

fof(f321,plain,(
    ! [X8] :
      ( k1_xboole_0 = sK7(X8,k1_xboole_0)
      | ~ r1_tarski(k1_xboole_0,sK7(X8,k1_xboole_0)) ) ),
    inference(resolution,[],[f107,f204])).

fof(f107,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f7200,plain,
    ( ~ v1_xboole_0(sK7(u1_struct_0(sK1),k1_xboole_0))
    | spl8_1
    | ~ spl8_31
    | ~ spl8_48
    | ~ spl8_60
    | ~ spl8_61 ),
    inference(forward_demodulation,[],[f7199,f5694])).

fof(f5694,plain,
    ( k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl8_48
    | ~ spl8_61 ),
    inference(forward_demodulation,[],[f1757,f2115])).

fof(f1757,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = sK3
    | ~ spl8_48 ),
    inference(avatar_component_clause,[],[f1755])).

fof(f1755,plain,
    ( spl8_48
  <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).

fof(f7199,plain,
    ( ~ v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | spl8_1
    | ~ spl8_31
    | ~ spl8_60
    | ~ spl8_61 ),
    inference(subsumption_resolution,[],[f7198,f391])).

fof(f391,plain,(
    ! [X5] : v1_funct_2(k1_xboole_0,k1_xboole_0,X5) ),
    inference(superposition,[],[f118,f329])).

fof(f329,plain,(
    ! [X9] : k1_xboole_0 = sK7(k1_xboole_0,X9) ),
    inference(subsumption_resolution,[],[f322,f84])).

fof(f322,plain,(
    ! [X9] :
      ( k1_xboole_0 = sK7(k1_xboole_0,X9)
      | ~ r1_tarski(k1_xboole_0,sK7(k1_xboole_0,X9)) ) ),
    inference(resolution,[],[f107,f207])).

fof(f207,plain,(
    ! [X0] : r1_tarski(sK7(k1_xboole_0,X0),k1_xboole_0) ),
    inference(resolution,[],[f203,f108])).

fof(f203,plain,(
    ! [X3] : m1_subset_1(sK7(k1_xboole_0,X3),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[],[f113,f134])).

fof(f134,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f7198,plain,
    ( ~ v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK2))
    | ~ v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | spl8_1
    | ~ spl8_31
    | ~ spl8_60
    | ~ spl8_61 ),
    inference(forward_demodulation,[],[f7197,f329])).

fof(f7197,plain,
    ( ~ v1_funct_2(sK7(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_xboole_0,u1_struct_0(sK2))
    | ~ v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | spl8_1
    | ~ spl8_31
    | ~ spl8_60
    | ~ spl8_61 ),
    inference(forward_demodulation,[],[f7196,f2112])).

fof(f2112,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl8_60 ),
    inference(avatar_component_clause,[],[f2110])).

fof(f7196,plain,
    ( ~ v1_funct_2(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | spl8_1
    | ~ spl8_31
    | ~ spl8_61 ),
    inference(subsumption_resolution,[],[f7195,f158])).

fof(f7195,plain,
    ( ~ m1_subset_1(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | spl8_1
    | ~ spl8_31
    | ~ spl8_61 ),
    inference(subsumption_resolution,[],[f7194,f4916])).

fof(f4916,plain,
    ( ! [X0] :
        ( ~ v5_pre_topc(X0,sK1,sK2)
        | ~ v1_xboole_0(X0) )
    | spl8_1
    | ~ spl8_61 ),
    inference(superposition,[],[f2740,f154])).

fof(f2740,plain,
    ( ~ v5_pre_topc(k1_xboole_0,sK1,sK2)
    | spl8_1
    | ~ spl8_61 ),
    inference(backward_demodulation,[],[f142,f2115])).

fof(f142,plain,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f140])).

fof(f7194,plain,
    ( v5_pre_topc(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),sK1,sK2)
    | ~ m1_subset_1(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ spl8_31
    | ~ spl8_61 ),
    inference(subsumption_resolution,[],[f7193,f70])).

fof(f7193,plain,
    ( v5_pre_topc(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),sK1,sK2)
    | ~ m1_subset_1(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK1)
    | ~ v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ spl8_31
    | ~ spl8_61 ),
    inference(subsumption_resolution,[],[f7192,f71])).

fof(f7192,plain,
    ( v5_pre_topc(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),sK1,sK2)
    | ~ m1_subset_1(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ spl8_31
    | ~ spl8_61 ),
    inference(subsumption_resolution,[],[f7191,f72])).

fof(f7191,plain,
    ( v5_pre_topc(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),sK1,sK2)
    | ~ m1_subset_1(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ spl8_31
    | ~ spl8_61 ),
    inference(subsumption_resolution,[],[f7174,f73])).

fof(f7174,plain,
    ( v5_pre_topc(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),sK1,sK2)
    | ~ m1_subset_1(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
    | ~ spl8_31
    | ~ spl8_61 ),
    inference(resolution,[],[f968,f5571])).

fof(f5571,plain,
    ( ! [X0] :
        ( v5_pre_topc(X0,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
        | ~ v1_xboole_0(X0) )
    | ~ spl8_31
    | ~ spl8_61 ),
    inference(superposition,[],[f4886,f154])).

fof(f4886,plain,
    ( v5_pre_topc(k1_xboole_0,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl8_31
    | ~ spl8_61 ),
    inference(backward_demodulation,[],[f888,f2115])).

fof(f888,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl8_31 ),
    inference(avatar_component_clause,[],[f886])).

fof(f886,plain,
    ( spl8_31
  <=> v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).

fof(f968,plain,(
    ! [X8,X9] :
      ( ~ v5_pre_topc(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),X8,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))
      | v5_pre_topc(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),X8,X9)
      | ~ m1_subset_1(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
      | ~ v1_funct_2(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),u1_struct_0(X8),u1_struct_0(X9))
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8) ) ),
    inference(subsumption_resolution,[],[f967,f117])).

fof(f117,plain,(
    ! [X0,X1] : v1_funct_1(sK7(X0,X1)) ),
    inference(cnf_transformation,[],[f69])).

fof(f967,plain,(
    ! [X8,X9] :
      ( ~ v5_pre_topc(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),X8,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))
      | v5_pre_topc(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),X8,X9)
      | ~ v1_funct_1(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))))
      | ~ m1_subset_1(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
      | ~ v1_funct_2(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),u1_struct_0(X8),u1_struct_0(X9))
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8) ) ),
    inference(subsumption_resolution,[],[f936,f118])).

fof(f936,plain,(
    ! [X8,X9] :
      ( ~ v5_pre_topc(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),X8,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))
      | v5_pre_topc(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),X8,X9)
      | ~ v1_funct_2(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))))
      | ~ v1_funct_1(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))))
      | ~ m1_subset_1(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9))))
      | ~ v1_funct_2(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),u1_struct_0(X8),u1_struct_0(X9))
      | ~ l1_pre_topc(X9)
      | ~ v2_pre_topc(X9)
      | ~ l1_pre_topc(X8)
      | ~ v2_pre_topc(X8) ) ),
    inference(resolution,[],[f138,f113])).

fof(f4866,plain,
    ( spl8_61
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f4865,f423,f2114])).

fof(f423,plain,
    ( spl8_21
  <=> ! [X11] : ~ r2_hidden(X11,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f4865,plain,
    ( k1_xboole_0 = sK3
    | ~ spl8_21 ),
    inference(resolution,[],[f424,f97])).

fof(f424,plain,
    ( ! [X11] : ~ r2_hidden(X11,sK3)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f423])).

fof(f4860,plain,
    ( spl8_122
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f4859,f144,f4758])).

fof(f4859,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f145,f80])).

fof(f145,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f144])).

fof(f4716,plain,
    ( spl8_44
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f2611,f423,f1669])).

fof(f2611,plain,
    ( v1_xboole_0(sK3)
    | ~ spl8_21 ),
    inference(resolution,[],[f424,f94])).

fof(f94,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f4708,plain,
    ( spl8_48
    | ~ spl8_13
    | ~ spl8_47 ),
    inference(avatar_split_clause,[],[f3015,f1751,f242,f1755])).

fof(f242,plain,
    ( spl8_13
  <=> r1_tarski(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f3015,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = sK3
    | ~ spl8_13
    | ~ spl8_47 ),
    inference(subsumption_resolution,[],[f3014,f244])).

fof(f244,plain,
    ( r1_tarski(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f242])).

fof(f3014,plain,
    ( u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = sK3
    | ~ r1_tarski(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ spl8_47 ),
    inference(resolution,[],[f1752,f107])).

fof(f1752,plain,
    ( r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK3)
    | ~ spl8_47 ),
    inference(avatar_component_clause,[],[f1751])).

fof(f4671,plain,
    ( spl8_21
    | ~ spl8_55 ),
    inference(avatar_split_clause,[],[f2293,f1951,f423])).

fof(f2293,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))
      | ~ r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f76,f123])).

fof(f4634,plain,
    ( ~ spl8_44
    | spl8_30 ),
    inference(avatar_split_clause,[],[f4458,f882,f1669])).

fof(f882,plain,
    ( spl8_30
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).

fof(f4458,plain,
    ( ~ v1_xboole_0(sK3)
    | spl8_30 ),
    inference(resolution,[],[f884,f158])).

fof(f884,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | spl8_30 ),
    inference(avatar_component_clause,[],[f882])).

fof(f4628,plain,
    ( ~ spl8_44
    | ~ spl8_9
    | spl8_34 ),
    inference(avatar_split_clause,[],[f1346,f955,f224,f1669])).

fof(f1346,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_xboole_0(sK3)
    | spl8_34 ),
    inference(resolution,[],[f595,f957])).

fof(f957,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | spl8_34 ),
    inference(avatar_component_clause,[],[f955])).

fof(f4619,plain,
    ( spl8_12
    | spl8_42 ),
    inference(avatar_split_clause,[],[f4618,f1647,f238])).

fof(f1647,plain,
    ( spl8_42
  <=> v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).

fof(f4618,plain,
    ( v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(subsumption_resolution,[],[f4617,f74])).

fof(f4617,plain,
    ( ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(subsumption_resolution,[],[f4472,f151])).

fof(f4472,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(resolution,[],[f153,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f4613,plain,
    ( ~ spl8_39
    | spl8_89 ),
    inference(avatar_split_clause,[],[f3152,f3144,f1579])).

fof(f3152,plain,
    ( ~ v1_xboole_0(k1_relat_1(sK3))
    | spl8_89 ),
    inference(resolution,[],[f3146,f159])).

fof(f3146,plain,
    ( ~ r1_tarski(k1_relat_1(sK3),sK3)
    | spl8_89 ),
    inference(avatar_component_clause,[],[f3144])).

fof(f4579,plain,
    ( spl8_9
    | spl8_40 ),
    inference(avatar_split_clause,[],[f4578,f1625,f224])).

fof(f4578,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f4577,f75])).

fof(f4577,plain,
    ( v1_partfun1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(subsumption_resolution,[],[f2270,f74])).

fof(f2270,plain,
    ( ~ v1_funct_1(sK3)
    | v1_partfun1(sK3,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f161,f709])).

fof(f709,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
      | ~ v1_funct_1(X0)
      | v1_partfun1(X0,X1)
      | v1_xboole_0(X2)
      | ~ v1_funct_2(X0,X1,X2) ) ),
    inference(resolution,[],[f100,f109])).

fof(f161,plain,(
    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    inference(resolution,[],[f108,f76])).

fof(f4498,plain,
    ( spl8_21
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f4478,f426,f423])).

fof(f4478,plain,(
    ! [X1] :
      ( ~ v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))
      | ~ r2_hidden(X1,sK3) ) ),
    inference(resolution,[],[f153,f123])).

fof(f4450,plain,
    ( ~ spl8_30
    | ~ spl8_31
    | spl8_2
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29 ),
    inference(avatar_split_clause,[],[f4449,f878,f874,f870,f144,f886,f882])).

fof(f870,plain,
    ( spl8_27
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f874,plain,
    ( spl8_28
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f4449,plain,
    ( ~ v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | spl8_2
    | ~ spl8_27
    | ~ spl8_28
    | ~ spl8_29 ),
    inference(subsumption_resolution,[],[f4417,f879])).

fof(f879,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ spl8_29 ),
    inference(avatar_component_clause,[],[f878])).

fof(f4417,plain,
    ( ~ v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | spl8_2
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f4416,f151])).

fof(f4416,plain,
    ( ~ v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | spl8_2
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f3385,f3467])).

fof(f3385,plain,
    ( ~ v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f3384,f70])).

fof(f3384,plain,
    ( ~ v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v2_pre_topc(sK1)
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f3383,f71])).

fof(f3383,plain,
    ( ~ v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f3382,f871])).

fof(f871,plain,
    ( v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f870])).

fof(f3382,plain,
    ( ~ v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f3381,f875])).

fof(f875,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f874])).

fof(f3381,plain,
    ( ~ v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f2870,f74])).

fof(f2870,plain,
    ( ~ v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f153,f135])).

fof(f4415,plain,
    ( spl8_31
    | ~ spl8_1
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(avatar_split_clause,[],[f4414,f882,f878,f140,f886])).

fof(f4414,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl8_1
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f4413,f70])).

fof(f4413,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK1)
    | ~ spl8_1
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f4412,f71])).

fof(f4412,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_1
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f4411,f72])).

fof(f4411,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_1
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f4410,f73])).

fof(f4410,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_1
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f4409,f75])).

fof(f4409,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_1
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f4408,f76])).

fof(f4408,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_1
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f4407,f74])).

fof(f4407,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_1
    | ~ spl8_29
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f4391,f879])).

fof(f4391,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_1
    | ~ spl8_30 ),
    inference(subsumption_resolution,[],[f4376,f141])).

fof(f141,plain,
    ( v5_pre_topc(sK3,sK1,sK2)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f140])).

fof(f4376,plain,
    ( ~ v5_pre_topc(sK3,sK1,sK2)
    | v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_30 ),
    inference(resolution,[],[f883,f137])).

fof(f883,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ spl8_30 ),
    inference(avatar_component_clause,[],[f882])).

fof(f2893,plain,
    ( ~ spl8_29
    | ~ spl8_30
    | spl8_31
    | ~ spl8_2
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(avatar_split_clause,[],[f2892,f874,f870,f144,f886,f882,f878])).

fof(f2892,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ spl8_2
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f2891,f70])).

fof(f2891,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v2_pre_topc(sK1)
    | ~ spl8_2
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f2890,f71])).

fof(f2890,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_2
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f2889,f871])).

fof(f2889,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_2
    | ~ spl8_28 ),
    inference(subsumption_resolution,[],[f2888,f875])).

fof(f2888,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f2887,f74])).

fof(f2887,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f2886,f151])).

fof(f2886,plain,
    ( v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f2869,f150])).

fof(f150,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f145,f80])).

fof(f2869,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))
    | ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1) ),
    inference(resolution,[],[f153,f136])).

fof(f2694,plain,
    ( ~ spl8_44
    | spl8_35 ),
    inference(avatar_split_clause,[],[f1907,f959,f1669])).

fof(f1907,plain,
    ( ~ v1_xboole_0(sK3)
    | spl8_35 ),
    inference(resolution,[],[f961,f158])).

fof(f961,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | spl8_35 ),
    inference(avatar_component_clause,[],[f959])).

fof(f2598,plain,
    ( ~ spl8_42
    | spl8_35
    | ~ spl8_40 ),
    inference(avatar_split_clause,[],[f2597,f1625,f959,f1647])).

fof(f2597,plain,
    ( ~ v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl8_35
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f2546,f376])).

fof(f376,plain,(
    v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) ),
    inference(resolution,[],[f120,f153])).

fof(f2546,plain,
    ( ~ v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl8_35
    | ~ spl8_40 ),
    inference(resolution,[],[f2358,f1908])).

fof(f1908,plain,
    ( ~ r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))
    | spl8_35 ),
    inference(resolution,[],[f961,f109])).

fof(f2358,plain,
    ( ! [X5] :
        ( r1_tarski(sK3,k2_zfmisc_1(X5,u1_struct_0(sK2)))
        | ~ v1_partfun1(sK3,X5)
        | ~ v4_relat_1(sK3,X5) )
    | ~ spl8_40 ),
    inference(superposition,[],[f161,f1993])).

fof(f1993,plain,
    ( ! [X0] :
        ( u1_struct_0(sK1) = X0
        | ~ v1_partfun1(sK3,X0)
        | ~ v4_relat_1(sK3,X0) )
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f1992,f254])).

fof(f1992,plain,
    ( ! [X0] :
        ( u1_struct_0(sK1) = X0
        | ~ v1_relat_1(sK3)
        | ~ v1_partfun1(sK3,X0)
        | ~ v4_relat_1(sK3,X0) )
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f1991,f375])).

fof(f375,plain,(
    v4_relat_1(sK3,u1_struct_0(sK1)) ),
    inference(resolution,[],[f120,f76])).

fof(f1991,plain,
    ( ! [X0] :
        ( u1_struct_0(sK1) = X0
        | ~ v4_relat_1(sK3,u1_struct_0(sK1))
        | ~ v1_relat_1(sK3)
        | ~ v1_partfun1(sK3,X0)
        | ~ v4_relat_1(sK3,X0) )
    | ~ spl8_40 ),
    inference(resolution,[],[f1627,f708])).

fof(f708,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X0,X2)
      | X1 = X2
      | ~ v4_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f705])).

fof(f705,plain,(
    ! [X2,X0,X1] :
      ( X1 = X2
      | ~ v1_partfun1(X0,X2)
      | ~ v4_relat_1(X0,X2)
      | ~ v1_relat_1(X0)
      | ~ v1_partfun1(X0,X1)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f103,f103])).

fof(f2586,plain,
    ( ~ spl8_12
    | spl8_13 ),
    inference(avatar_split_clause,[],[f2524,f242,f238])).

fof(f2524,plain,
    ( r1_tarski(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) ),
    inference(superposition,[],[f162,f157])).

fof(f162,plain,(
    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) ),
    inference(resolution,[],[f108,f153])).

fof(f2343,plain,
    ( ~ spl8_34
    | ~ spl8_35
    | spl8_36
    | ~ spl8_2
    | ~ spl8_32
    | ~ spl8_33 ),
    inference(avatar_split_clause,[],[f2342,f951,f947,f144,f963,f959,f955])).

fof(f2342,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ spl8_2
    | ~ spl8_32
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f2341,f948])).

fof(f2341,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_2
    | ~ spl8_33 ),
    inference(subsumption_resolution,[],[f2340,f952])).

fof(f2340,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f2339,f72])).

fof(f2339,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f2338,f73])).

fof(f2338,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f2337,f74])).

fof(f2337,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f2336,f151])).

fof(f2336,plain,
    ( v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ spl8_2 ),
    inference(subsumption_resolution,[],[f2321,f150])).

fof(f2321,plain,
    ( ~ v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))
    | ~ v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))
    | ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(resolution,[],[f153,f138])).

fof(f1905,plain,
    ( spl8_34
    | ~ spl8_40
    | ~ spl8_42 ),
    inference(avatar_contradiction_clause,[],[f1904])).

fof(f1904,plain,
    ( $false
    | spl8_34
    | ~ spl8_40
    | ~ spl8_42 ),
    inference(subsumption_resolution,[],[f1903,f376])).

fof(f1903,plain,
    ( ~ v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl8_34
    | ~ spl8_40
    | ~ spl8_42 ),
    inference(subsumption_resolution,[],[f1901,f1649])).

fof(f1649,plain,
    ( v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ spl8_42 ),
    inference(avatar_component_clause,[],[f1647])).

fof(f1901,plain,
    ( ~ v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | ~ v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))
    | spl8_34
    | ~ spl8_40 ),
    inference(resolution,[],[f1808,f957])).

fof(f1808,plain,
    ( ! [X0] :
        ( v1_funct_2(sK3,X0,u1_struct_0(sK2))
        | ~ v1_partfun1(sK3,X0)
        | ~ v4_relat_1(sK3,X0) )
    | ~ spl8_40 ),
    inference(superposition,[],[f75,f1692])).

fof(f1692,plain,
    ( ! [X0] :
        ( u1_struct_0(sK1) = X0
        | ~ v1_partfun1(sK3,X0)
        | ~ v4_relat_1(sK3,X0) )
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f1691,f254])).

fof(f1691,plain,
    ( ! [X0] :
        ( u1_struct_0(sK1) = X0
        | ~ v1_relat_1(sK3)
        | ~ v1_partfun1(sK3,X0)
        | ~ v4_relat_1(sK3,X0) )
    | ~ spl8_40 ),
    inference(subsumption_resolution,[],[f1690,f375])).

fof(f1690,plain,
    ( ! [X0] :
        ( u1_struct_0(sK1) = X0
        | ~ v4_relat_1(sK3,u1_struct_0(sK1))
        | ~ v1_relat_1(sK3)
        | ~ v1_partfun1(sK3,X0)
        | ~ v4_relat_1(sK3,X0) )
    | ~ spl8_40 ),
    inference(resolution,[],[f1627,f708])).

fof(f1367,plain,
    ( spl8_23
    | spl8_37 ),
    inference(avatar_split_clause,[],[f1363,f1365,f740])).

fof(f740,plain,
    ( spl8_23
  <=> ! [X2] : v1_xboole_0(X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f1363,plain,(
    ! [X6,X7] :
      ( v1_partfun1(X6,k1_xboole_0)
      | v1_xboole_0(X7)
      | ~ v1_xboole_0(X6) ) ),
    inference(subsumption_resolution,[],[f1362,f369])).

fof(f369,plain,(
    ! [X0] :
      ( v1_funct_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f362,f154])).

fof(f362,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f117,f328])).

fof(f1362,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_1(X6)
      | v1_partfun1(X6,k1_xboole_0)
      | v1_xboole_0(X7)
      | ~ v1_xboole_0(X6) ) ),
    inference(subsumption_resolution,[],[f1361,f158])).

fof(f1361,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(X6)
      | v1_partfun1(X6,k1_xboole_0)
      | v1_xboole_0(X7)
      | ~ v1_xboole_0(X6) ) ),
    inference(subsumption_resolution,[],[f1358,f83])).

fof(f1358,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(X6)
      | v1_partfun1(X6,k1_xboole_0)
      | v1_xboole_0(X7)
      | ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(X6) ) ),
    inference(resolution,[],[f720,f623])).

fof(f623,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X0,X1,X2)
      | ~ v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f603,f154])).

fof(f603,plain,(
    ! [X10,X11] :
      ( v1_funct_2(k1_xboole_0,X10,X11)
      | ~ v1_xboole_0(X10) ) ),
    inference(superposition,[],[f118,f556])).

fof(f556,plain,(
    ! [X2,X3] :
      ( k1_xboole_0 = sK7(X2,X3)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f541,f97])).

fof(f541,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,sK7(X5,X6))
      | ~ v1_xboole_0(X5) ) ),
    inference(duplicate_literal_removal,[],[f532])).

fof(f532,plain,(
    ! [X6,X4,X5] :
      ( ~ r2_hidden(X4,sK7(X5,X6))
      | ~ v1_xboole_0(X5)
      | ~ v1_xboole_0(X5) ) ),
    inference(resolution,[],[f407,f209])).

fof(f209,plain,(
    ! [X0,X1] :
      ( r1_tarski(sK7(X0,X1),X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(superposition,[],[f207,f154])).

fof(f720,plain,(
    ! [X8,X9] :
      ( ~ v1_funct_2(X9,k1_xboole_0,X8)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(X9)
      | v1_partfun1(X9,k1_xboole_0)
      | v1_xboole_0(X8) ) ),
    inference(superposition,[],[f100,f134])).

fof(f977,plain,(
    spl8_33 ),
    inference(avatar_contradiction_clause,[],[f976])).

fof(f976,plain,
    ( $false
    | spl8_33 ),
    inference(subsumption_resolution,[],[f973,f71])).

fof(f973,plain,
    ( ~ l1_pre_topc(sK1)
    | spl8_33 ),
    inference(resolution,[],[f953,f301])).

fof(f301,plain,(
    ! [X5] :
      ( l1_pre_topc(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5)))
      | ~ l1_pre_topc(X5) ) ),
    inference(resolution,[],[f102,f86])).

fof(f86,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f953,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl8_33 ),
    inference(avatar_component_clause,[],[f951])).

fof(f972,plain,(
    spl8_32 ),
    inference(avatar_contradiction_clause,[],[f971])).

fof(f971,plain,
    ( $false
    | spl8_32 ),
    inference(subsumption_resolution,[],[f970,f70])).

fof(f970,plain,
    ( ~ v2_pre_topc(sK1)
    | spl8_32 ),
    inference(subsumption_resolution,[],[f969,f71])).

fof(f969,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | spl8_32 ),
    inference(resolution,[],[f949,f88])).

fof(f88,plain,(
    ! [X0] :
      ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f949,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl8_32 ),
    inference(avatar_component_clause,[],[f947])).

fof(f899,plain,(
    spl8_28 ),
    inference(avatar_contradiction_clause,[],[f898])).

fof(f898,plain,
    ( $false
    | spl8_28 ),
    inference(subsumption_resolution,[],[f896,f73])).

fof(f896,plain,
    ( ~ l1_pre_topc(sK2)
    | spl8_28 ),
    inference(resolution,[],[f876,f301])).

fof(f876,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | spl8_28 ),
    inference(avatar_component_clause,[],[f874])).

fof(f895,plain,(
    spl8_27 ),
    inference(avatar_contradiction_clause,[],[f894])).

fof(f894,plain,
    ( $false
    | spl8_27 ),
    inference(subsumption_resolution,[],[f893,f72])).

fof(f893,plain,
    ( ~ v2_pre_topc(sK2)
    | spl8_27 ),
    inference(subsumption_resolution,[],[f892,f73])).

fof(f892,plain,
    ( ~ l1_pre_topc(sK2)
    | ~ v2_pre_topc(sK2)
    | spl8_27 ),
    inference(resolution,[],[f872,f88])).

fof(f872,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | spl8_27 ),
    inference(avatar_component_clause,[],[f870])).

fof(f801,plain,
    ( spl8_9
    | ~ spl8_23 ),
    inference(avatar_contradiction_clause,[],[f795])).

fof(f795,plain,
    ( $false
    | spl8_9
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f226,f741])).

fof(f741,plain,
    ( ! [X2] : v1_xboole_0(X2)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f740])).

fof(f226,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl8_9 ),
    inference(avatar_component_clause,[],[f224])).

fof(f148,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f81,f144,f140])).

fof(f81,plain,
    ( v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).

fof(f147,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f82,f144,f140])).

fof(f82,plain,
    ( ~ v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))
    | ~ v5_pre_topc(sK3,sK1,sK2) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:55:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (9897)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.50  % (9904)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.50  % (9895)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (9893)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (9890)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (9900)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.51  % (9914)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.52  % (9905)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (9913)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.52  % (9909)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.27/0.52  % (9901)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.27/0.52  % (9903)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.27/0.52  % (9908)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.27/0.52  % (9902)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.27/0.52  % (9896)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.27/0.52  % (9891)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.52  % (9890)Refutation not found, incomplete strategy% (9890)------------------------------
% 1.27/0.52  % (9890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (9890)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.52  
% 1.27/0.52  % (9890)Memory used [KB]: 10618
% 1.27/0.52  % (9890)Time elapsed: 0.112 s
% 1.27/0.52  % (9890)------------------------------
% 1.27/0.52  % (9890)------------------------------
% 1.27/0.52  % (9903)Refutation not found, incomplete strategy% (9903)------------------------------
% 1.27/0.52  % (9903)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.52  % (9894)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 1.27/0.52  % (9910)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.27/0.53  % (9901)Refutation not found, incomplete strategy% (9901)------------------------------
% 1.27/0.53  % (9901)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (9896)Refutation not found, incomplete strategy% (9896)------------------------------
% 1.27/0.53  % (9896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (9903)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (9903)Memory used [KB]: 6268
% 1.27/0.53  % (9903)Time elapsed: 0.117 s
% 1.27/0.53  % (9903)------------------------------
% 1.27/0.53  % (9903)------------------------------
% 1.27/0.53  % (9898)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.41/0.54  % (9916)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.41/0.54  % (9901)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  % (9896)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.54  
% 1.41/0.54  
% 1.41/0.54  % (9901)Memory used [KB]: 10874
% 1.41/0.54  % (9896)Memory used [KB]: 10746
% 1.41/0.54  % (9901)Time elapsed: 0.122 s
% 1.41/0.54  % (9896)Time elapsed: 0.071 s
% 1.41/0.54  % (9901)------------------------------
% 1.41/0.54  % (9901)------------------------------
% 1.41/0.54  % (9896)------------------------------
% 1.41/0.54  % (9896)------------------------------
% 1.41/0.54  % (9911)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.41/0.55  % (9891)Refutation not found, incomplete strategy% (9891)------------------------------
% 1.41/0.55  % (9891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (9891)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.55  
% 1.41/0.55  % (9891)Memory used [KB]: 10746
% 1.41/0.55  % (9891)Time elapsed: 0.116 s
% 1.41/0.55  % (9891)------------------------------
% 1.41/0.55  % (9891)------------------------------
% 1.41/0.55  % (9899)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.41/0.55  % (9892)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.41/0.55  % (9907)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.41/0.56  % (9915)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.41/0.56  % (9912)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 2.10/0.64  % (9908)Refutation not found, incomplete strategy% (9908)------------------------------
% 2.10/0.64  % (9908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.64  % (9908)Termination reason: Refutation not found, incomplete strategy
% 2.10/0.64  
% 2.10/0.64  % (9908)Memory used [KB]: 6780
% 2.10/0.64  % (9908)Time elapsed: 0.233 s
% 2.10/0.64  % (9908)------------------------------
% 2.10/0.64  % (9908)------------------------------
% 2.10/0.66  % (9899)Refutation not found, incomplete strategy% (9899)------------------------------
% 2.10/0.66  % (9899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.10/0.66  % (9899)Termination reason: Refutation not found, incomplete strategy
% 2.10/0.66  
% 2.10/0.66  % (9899)Memory used [KB]: 6268
% 2.10/0.66  % (9899)Time elapsed: 0.252 s
% 2.10/0.66  % (9899)------------------------------
% 2.10/0.66  % (9899)------------------------------
% 3.78/0.86  % (9894)Refutation found. Thanks to Tanya!
% 3.78/0.86  % SZS status Theorem for theBenchmark
% 3.78/0.86  % SZS output start Proof for theBenchmark
% 3.78/0.86  fof(f8925,plain,(
% 3.78/0.86    $false),
% 3.78/0.86    inference(avatar_sat_refutation,[],[f147,f148,f801,f895,f899,f972,f977,f1367,f1905,f2343,f2586,f2598,f2694,f2893,f4415,f4450,f4498,f4579,f4613,f4619,f4628,f4634,f4671,f4708,f4716,f4860,f4866,f7203,f7996,f8245,f8835,f8836,f8859,f8878,f8880,f8882,f8884,f8885,f8886,f8887,f8901,f8903,f8917])).
% 3.78/0.86  fof(f8917,plain,(
% 3.78/0.86    ~spl8_12 | spl8_22),
% 3.78/0.86    inference(avatar_split_clause,[],[f8784,f426,f238])).
% 3.78/0.86  fof(f238,plain,(
% 3.78/0.86    spl8_12 <=> v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))),
% 3.78/0.86    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 3.78/0.86  fof(f426,plain,(
% 3.78/0.86    spl8_22 <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))),
% 3.78/0.86    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 3.78/0.86  fof(f8784,plain,(
% 3.78/0.86    ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | spl8_22),
% 3.78/0.86    inference(duplicate_literal_removal,[],[f433])).
% 3.78/0.86  fof(f433,plain,(
% 3.78/0.86    ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | spl8_22),
% 3.78/0.86    inference(superposition,[],[f428,f157])).
% 3.78/0.86  fof(f157,plain,(
% 3.78/0.86    ( ! [X0,X1] : (k2_zfmisc_1(X1,X0) = X0 | ~v1_xboole_0(X0)) )),
% 3.78/0.86    inference(superposition,[],[f133,f154])).
% 3.78/0.86  fof(f154,plain,(
% 3.78/0.86    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 3.78/0.86    inference(resolution,[],[f97,f93])).
% 3.78/0.86  fof(f93,plain,(
% 3.78/0.86    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.78/0.86    inference(cnf_transformation,[],[f57])).
% 3.78/0.86  fof(f57,plain,(
% 3.78/0.86    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK5(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.78/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f55,f56])).
% 3.78/0.86  fof(f56,plain,(
% 3.78/0.86    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK5(X0),X0))),
% 3.78/0.86    introduced(choice_axiom,[])).
% 3.78/0.86  fof(f55,plain,(
% 3.78/0.86    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.78/0.86    inference(rectify,[],[f54])).
% 3.78/0.86  fof(f54,plain,(
% 3.78/0.86    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.78/0.86    inference(nnf_transformation,[],[f1])).
% 3.78/0.86  fof(f1,axiom,(
% 3.78/0.86    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.78/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 3.78/0.86  fof(f97,plain,(
% 3.78/0.86    ( ! [X0] : (r2_hidden(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 3.78/0.86    inference(cnf_transformation,[],[f61])).
% 3.78/0.86  fof(f61,plain,(
% 3.78/0.86    ! [X0] : ((sP0(sK6(X0),X0) & r2_hidden(sK6(X0),X0)) | k1_xboole_0 = X0)),
% 3.78/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f44,f60])).
% 3.78/0.86  fof(f60,plain,(
% 3.78/0.86    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) => (sP0(sK6(X0),X0) & r2_hidden(sK6(X0),X0)))),
% 3.78/0.86    introduced(choice_axiom,[])).
% 3.78/0.86  fof(f44,plain,(
% 3.78/0.86    ! [X0] : (? [X1] : (sP0(X1,X0) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.78/0.86    inference(definition_folding,[],[f32,f43])).
% 3.78/0.86  fof(f43,plain,(
% 3.78/0.86    ! [X1,X0] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) | ~sP0(X1,X0))),
% 3.78/0.86    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 3.78/0.86  fof(f32,plain,(
% 3.78/0.86    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 3.78/0.86    inference(ennf_transformation,[],[f12])).
% 3.78/0.86  fof(f12,axiom,(
% 3.78/0.86    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 3.78/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_mcart_1)).
% 3.78/0.86  fof(f133,plain,(
% 3.78/0.86    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.78/0.86    inference(equality_resolution,[],[f112])).
% 3.78/0.86  fof(f112,plain,(
% 3.78/0.86    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.78/0.86    inference(cnf_transformation,[],[f67])).
% 3.78/0.86  fof(f67,plain,(
% 3.78/0.86    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.78/0.86    inference(flattening,[],[f66])).
% 3.78/0.86  fof(f66,plain,(
% 3.78/0.86    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.78/0.86    inference(nnf_transformation,[],[f5])).
% 3.78/0.86  fof(f5,axiom,(
% 3.78/0.86    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.78/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.78/0.86  fof(f428,plain,(
% 3.78/0.86    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | spl8_22),
% 3.78/0.86    inference(avatar_component_clause,[],[f426])).
% 3.78/0.86  fof(f8903,plain,(
% 3.78/0.86    ~spl8_44 | ~spl8_37 | spl8_39),
% 3.78/0.86    inference(avatar_split_clause,[],[f2696,f1579,f1365,f1669])).
% 3.78/0.86  fof(f1669,plain,(
% 3.78/0.86    spl8_44 <=> v1_xboole_0(sK3)),
% 3.78/0.86    introduced(avatar_definition,[new_symbols(naming,[spl8_44])])).
% 3.78/0.86  fof(f1365,plain,(
% 3.78/0.86    spl8_37 <=> ! [X6] : (v1_partfun1(X6,k1_xboole_0) | ~v1_xboole_0(X6))),
% 3.78/0.86    introduced(avatar_definition,[new_symbols(naming,[spl8_37])])).
% 3.78/0.86  fof(f1579,plain,(
% 3.78/0.86    spl8_39 <=> v1_xboole_0(k1_relat_1(sK3))),
% 3.78/0.86    introduced(avatar_definition,[new_symbols(naming,[spl8_39])])).
% 3.78/0.86  fof(f2696,plain,(
% 3.78/0.86    ~v1_xboole_0(sK3) | (~spl8_37 | spl8_39)),
% 3.78/0.86    inference(subsumption_resolution,[],[f2695,f373])).
% 3.78/0.86  fof(f373,plain,(
% 3.78/0.86    ( ! [X4,X3] : (v4_relat_1(X3,X4) | ~v1_xboole_0(X3)) )),
% 3.78/0.86    inference(resolution,[],[f120,f158])).
% 3.78/0.86  fof(f158,plain,(
% 3.78/0.86    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~v1_xboole_0(X0)) )),
% 3.78/0.86    inference(superposition,[],[f85,f154])).
% 3.78/0.86  fof(f85,plain,(
% 3.78/0.86    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.78/0.86    inference(cnf_transformation,[],[f6])).
% 3.78/0.86  fof(f6,axiom,(
% 3.78/0.86    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.78/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 3.78/0.86  fof(f120,plain,(
% 3.78/0.86    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 3.78/0.86    inference(cnf_transformation,[],[f39])).
% 3.78/0.86  fof(f39,plain,(
% 3.78/0.86    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.86    inference(ennf_transformation,[],[f11])).
% 3.78/0.86  fof(f11,axiom,(
% 3.78/0.86    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.78/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.78/0.86  fof(f2695,plain,(
% 3.78/0.86    ~v4_relat_1(sK3,k1_xboole_0) | ~v1_xboole_0(sK3) | (~spl8_37 | spl8_39)),
% 3.78/0.86    inference(subsumption_resolution,[],[f1770,f83])).
% 3.78/0.86  fof(f83,plain,(
% 3.78/0.86    v1_xboole_0(k1_xboole_0)),
% 3.78/0.86    inference(cnf_transformation,[],[f2])).
% 3.78/0.86  fof(f2,axiom,(
% 3.78/0.86    v1_xboole_0(k1_xboole_0)),
% 3.78/0.86    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 3.78/0.86  fof(f1770,plain,(
% 3.78/0.86    ~v1_xboole_0(k1_xboole_0) | ~v4_relat_1(sK3,k1_xboole_0) | ~v1_xboole_0(sK3) | (~spl8_37 | spl8_39)),
% 3.78/0.86    inference(resolution,[],[f1689,f1366])).
% 3.78/0.86  fof(f1366,plain,(
% 3.78/0.86    ( ! [X6] : (v1_partfun1(X6,k1_xboole_0) | ~v1_xboole_0(X6)) ) | ~spl8_37),
% 3.78/0.86    inference(avatar_component_clause,[],[f1365])).
% 3.78/0.86  fof(f1689,plain,(
% 3.78/0.86    ( ! [X0] : (~v1_partfun1(sK3,X0) | ~v1_xboole_0(X0) | ~v4_relat_1(sK3,X0)) ) | spl8_39),
% 3.78/0.86    inference(subsumption_resolution,[],[f1688,f254])).
% 3.78/0.86  fof(f254,plain,(
% 3.78/0.86    v1_relat_1(sK3)),
% 3.78/0.86    inference(resolution,[],[f119,f76])).
% 3.78/0.86  fof(f76,plain,(
% 3.78/0.86    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 3.78/0.86    inference(cnf_transformation,[],[f51])).
% 3.78/0.86  fof(f51,plain,(
% 3.78/0.86    ((((~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(sK3,sK1,sK2)) & (v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,sK1,sK2)) & sK3 = sK4 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1)),
% 3.78/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f46,f50,f49,f48,f47])).
% 3.78/0.86  fof(f47,plain,(
% 3.78/0.86    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK1,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK1,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1))),
% 3.78/0.86    introduced(choice_axiom,[])).
% 3.78/0.86  fof(f48,plain,(
% 3.78/0.86    ? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,sK1,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,sK1,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) => (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(X2,sK1,sK2)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(X2,sK1,sK2)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_pre_topc(sK2) & v2_pre_topc(sK2))),
% 3.78/0.86    introduced(choice_axiom,[])).
% 3.78/0.86  fof(f49,plain,(
% 3.78/0.86    ? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(X2,sK1,sK2)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(X2,sK1,sK2)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(X2)) => (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(sK3,sK1,sK2)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,sK1,sK2)) & sK3 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) & v1_funct_1(X3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3))),
% 3.78/0.86    introduced(choice_axiom,[])).
% 3.78/0.86  fof(f50,plain,(
% 3.78/0.86    ? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(sK3,sK1,sK2)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,sK1,sK2)) & sK3 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) & v1_funct_1(X3)) => ((~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(sK3,sK1,sK2)) & (v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,sK1,sK2)) & sK3 = sK4 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) & v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) & v1_funct_1(sK4))),
% 3.78/0.86    introduced(choice_axiom,[])).
% 3.78/0.86  fof(f46,plain,(
% 3.78/0.86    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.78/0.86    inference(flattening,[],[f45])).
% 3.78/0.86  fof(f45,plain,(
% 3.78/0.86    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X2,X0,X1))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.78/0.86    inference(nnf_transformation,[],[f24])).
% 3.78/0.86  fof(f24,plain,(
% 3.78/0.86    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.78/0.86    inference(flattening,[],[f23])).
% 3.78/0.88  fof(f23,plain,(
% 3.78/0.88    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v5_pre_topc(X2,X0,X1) <~> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & X2 = X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.78/0.88    inference(ennf_transformation,[],[f22])).
% 3.78/0.88  fof(f22,negated_conjecture,(
% 3.78/0.88    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.78/0.88    inference(negated_conjecture,[],[f21])).
% 3.78/0.88  fof(f21,conjecture,(
% 3.78/0.88    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.78/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_pre_topc)).
% 3.78/0.88  fof(f119,plain,(
% 3.78/0.88    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f38])).
% 3.78/0.88  fof(f38,plain,(
% 3.78/0.88    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.88    inference(ennf_transformation,[],[f10])).
% 3.78/0.88  fof(f10,axiom,(
% 3.78/0.88    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.78/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.78/0.88  fof(f1688,plain,(
% 3.78/0.88    ( ! [X0] : (~v1_xboole_0(X0) | ~v1_partfun1(sK3,X0) | ~v4_relat_1(sK3,X0) | ~v1_relat_1(sK3)) ) | spl8_39),
% 3.78/0.88    inference(superposition,[],[f1581,f103])).
% 3.78/0.88  fof(f103,plain,(
% 3.78/0.88    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f62])).
% 3.78/0.88  fof(f62,plain,(
% 3.78/0.88    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.78/0.88    inference(nnf_transformation,[],[f37])).
% 3.78/0.88  fof(f37,plain,(
% 3.78/0.88    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.78/0.88    inference(flattening,[],[f36])).
% 3.78/0.88  fof(f36,plain,(
% 3.78/0.88    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.78/0.88    inference(ennf_transformation,[],[f14])).
% 3.78/0.88  fof(f14,axiom,(
% 3.78/0.88    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.78/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 3.78/0.88  fof(f1581,plain,(
% 3.78/0.88    ~v1_xboole_0(k1_relat_1(sK3)) | spl8_39),
% 3.78/0.88    inference(avatar_component_clause,[],[f1579])).
% 3.78/0.88  fof(f8901,plain,(
% 3.78/0.88    ~spl8_9 | spl8_55),
% 3.78/0.88    inference(avatar_split_clause,[],[f8789,f1951,f224])).
% 3.78/0.88  fof(f224,plain,(
% 3.78/0.88    spl8_9 <=> v1_xboole_0(u1_struct_0(sK2))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 3.78/0.88  fof(f1951,plain,(
% 3.78/0.88    spl8_55 <=> v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_55])])).
% 3.78/0.88  fof(f8789,plain,(
% 3.78/0.88    ~v1_xboole_0(u1_struct_0(sK2)) | spl8_55),
% 3.78/0.88    inference(duplicate_literal_removal,[],[f2067])).
% 3.78/0.88  fof(f2067,plain,(
% 3.78/0.88    ~v1_xboole_0(u1_struct_0(sK2)) | ~v1_xboole_0(u1_struct_0(sK2)) | spl8_55),
% 3.78/0.88    inference(superposition,[],[f1953,f157])).
% 3.78/0.88  fof(f1953,plain,(
% 3.78/0.88    ~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) | spl8_55),
% 3.78/0.88    inference(avatar_component_clause,[],[f1951])).
% 3.78/0.88  fof(f8887,plain,(
% 3.78/0.88    spl8_165),
% 3.78/0.88    inference(avatar_split_clause,[],[f74,f8819])).
% 3.78/0.88  fof(f8819,plain,(
% 3.78/0.88    spl8_165 <=> v1_funct_1(sK3)),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_165])])).
% 3.78/0.88  fof(f74,plain,(
% 3.78/0.88    v1_funct_1(sK3)),
% 3.78/0.88    inference(cnf_transformation,[],[f51])).
% 3.78/0.88  fof(f8886,plain,(
% 3.78/0.88    spl8_167),
% 3.78/0.88    inference(avatar_split_clause,[],[f75,f8838])).
% 3.78/0.88  fof(f8838,plain,(
% 3.78/0.88    spl8_167 <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_167])])).
% 3.78/0.88  fof(f75,plain,(
% 3.78/0.88    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 3.78/0.88    inference(cnf_transformation,[],[f51])).
% 3.78/0.88  fof(f8885,plain,(
% 3.78/0.88    spl8_168),
% 3.78/0.88    inference(avatar_split_clause,[],[f76,f8842])).
% 3.78/0.88  fof(f8842,plain,(
% 3.78/0.88    spl8_168 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_168])])).
% 3.78/0.88  fof(f8884,plain,(
% 3.78/0.88    spl8_166),
% 3.78/0.88    inference(avatar_split_clause,[],[f151,f8823])).
% 3.78/0.88  fof(f8823,plain,(
% 3.78/0.88    spl8_166 <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_166])])).
% 3.78/0.88  fof(f151,plain,(
% 3.78/0.88    v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))),
% 3.78/0.88    inference(forward_demodulation,[],[f78,f80])).
% 3.78/0.88  fof(f80,plain,(
% 3.78/0.88    sK3 = sK4),
% 3.78/0.88    inference(cnf_transformation,[],[f51])).
% 3.78/0.88  fof(f78,plain,(
% 3.78/0.88    v1_funct_2(sK4,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))),
% 3.78/0.88    inference(cnf_transformation,[],[f51])).
% 3.78/0.88  fof(f8882,plain,(
% 3.78/0.88    ~spl8_36 | ~spl8_34 | spl8_1 | ~spl8_35),
% 3.78/0.88    inference(avatar_split_clause,[],[f4749,f959,f140,f955,f963])).
% 3.78/0.88  fof(f963,plain,(
% 3.78/0.88    spl8_36 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2)),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_36])])).
% 3.78/0.88  fof(f955,plain,(
% 3.78/0.88    spl8_34 <=> v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_34])])).
% 3.78/0.88  fof(f140,plain,(
% 3.78/0.88    spl8_1 <=> v5_pre_topc(sK3,sK1,sK2)),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 3.78/0.88  fof(f959,plain,(
% 3.78/0.88    spl8_35 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_35])])).
% 3.78/0.88  fof(f4749,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~spl8_35),
% 3.78/0.88    inference(subsumption_resolution,[],[f4748,f70])).
% 3.78/0.88  fof(f70,plain,(
% 3.78/0.88    v2_pre_topc(sK1)),
% 3.78/0.88    inference(cnf_transformation,[],[f51])).
% 3.78/0.88  fof(f4748,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v2_pre_topc(sK1) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~spl8_35),
% 3.78/0.88    inference(subsumption_resolution,[],[f4747,f71])).
% 3.78/0.88  fof(f71,plain,(
% 3.78/0.88    l1_pre_topc(sK1)),
% 3.78/0.88    inference(cnf_transformation,[],[f51])).
% 3.78/0.88  fof(f4747,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~spl8_35),
% 3.78/0.88    inference(subsumption_resolution,[],[f4746,f72])).
% 3.78/0.88  fof(f72,plain,(
% 3.78/0.88    v2_pre_topc(sK2)),
% 3.78/0.88    inference(cnf_transformation,[],[f51])).
% 3.78/0.88  fof(f4746,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~spl8_35),
% 3.78/0.88    inference(subsumption_resolution,[],[f4745,f73])).
% 3.78/0.88  fof(f73,plain,(
% 3.78/0.88    l1_pre_topc(sK2)),
% 3.78/0.88    inference(cnf_transformation,[],[f51])).
% 3.78/0.88  fof(f4745,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~spl8_35),
% 3.78/0.88    inference(subsumption_resolution,[],[f4744,f75])).
% 3.78/0.88  fof(f4744,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~spl8_35),
% 3.78/0.88    inference(subsumption_resolution,[],[f4743,f76])).
% 3.78/0.88  fof(f4743,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~spl8_35),
% 3.78/0.88    inference(subsumption_resolution,[],[f3547,f74])).
% 3.78/0.88  fof(f3547,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~spl8_35),
% 3.78/0.88    inference(resolution,[],[f3336,f858])).
% 3.78/0.88  fof(f858,plain,(
% 3.78/0.88    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2))) | v5_pre_topc(X0,X1,X2) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))),u1_struct_0(X2)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2)))) | ~v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2)) | ~l1_pre_topc(X2) | ~v2_pre_topc(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~v5_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X2)) )),
% 3.78/0.88    inference(resolution,[],[f136,f109])).
% 3.78/0.88  fof(f109,plain,(
% 3.78/0.88    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f65])).
% 3.78/0.88  fof(f65,plain,(
% 3.78/0.88    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.78/0.88    inference(nnf_transformation,[],[f7])).
% 3.78/0.88  fof(f7,axiom,(
% 3.78/0.88    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.78/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.78/0.88  fof(f136,plain,(
% 3.78/0.88    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.88    inference(duplicate_literal_removal,[],[f126])).
% 3.78/0.88  fof(f126,plain,(
% 3.78/0.88    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.88    inference(equality_resolution,[],[f92])).
% 3.78/0.88  fof(f92,plain,(
% 3.78/0.88    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f53])).
% 3.78/0.88  fof(f53,plain,(
% 3.78/0.88    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) & (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.78/0.88    inference(nnf_transformation,[],[f31])).
% 3.78/0.88  fof(f31,plain,(
% 3.78/0.88    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.78/0.88    inference(flattening,[],[f30])).
% 3.78/0.88  fof(f30,plain,(
% 3.78/0.88    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.78/0.88    inference(ennf_transformation,[],[f19])).
% 3.78/0.88  fof(f19,axiom,(
% 3.78/0.88    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 3.78/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 3.78/0.88  fof(f3336,plain,(
% 3.78/0.88    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))) | ~spl8_35),
% 3.78/0.88    inference(resolution,[],[f960,f108])).
% 3.78/0.88  fof(f108,plain,(
% 3.78/0.88    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f65])).
% 3.78/0.88  fof(f960,plain,(
% 3.78/0.88    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~spl8_35),
% 3.78/0.88    inference(avatar_component_clause,[],[f959])).
% 3.78/0.88  fof(f8880,plain,(
% 3.78/0.88    ~spl8_167 | ~spl8_168 | ~spl8_165 | ~spl8_34 | spl8_36 | ~spl8_1 | ~spl8_35),
% 3.78/0.88    inference(avatar_split_clause,[],[f7405,f959,f140,f963,f955,f8819,f8842,f8838])).
% 3.78/0.88  fof(f7405,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,sK2) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl8_35),
% 3.78/0.88    inference(subsumption_resolution,[],[f7404,f70])).
% 3.78/0.88  fof(f7404,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,sK2) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v2_pre_topc(sK1) | ~spl8_35),
% 3.78/0.88    inference(subsumption_resolution,[],[f7403,f71])).
% 3.78/0.88  fof(f7403,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,sK2) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl8_35),
% 3.78/0.88    inference(subsumption_resolution,[],[f7402,f72])).
% 3.78/0.88  fof(f7402,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,sK2) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl8_35),
% 3.78/0.88    inference(subsumption_resolution,[],[f4116,f73])).
% 3.78/0.88  fof(f4116,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,sK2) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl8_35),
% 3.78/0.88    inference(resolution,[],[f960,f135])).
% 3.78/0.88  fof(f135,plain,(
% 3.78/0.88    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.88    inference(duplicate_literal_removal,[],[f127])).
% 3.78/0.88  fof(f127,plain,(
% 3.78/0.88    ( ! [X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.88    inference(equality_resolution,[],[f91])).
% 3.78/0.88  fof(f91,plain,(
% 3.78/0.88    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f53])).
% 3.78/0.88  fof(f8878,plain,(
% 3.78/0.88    ~spl8_44 | ~spl8_12 | spl8_29),
% 3.78/0.88    inference(avatar_split_clause,[],[f1345,f878,f238,f1669])).
% 3.78/0.88  fof(f878,plain,(
% 3.78/0.88    spl8_29 <=> v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_29])])).
% 3.78/0.88  fof(f1345,plain,(
% 3.78/0.88    ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_xboole_0(sK3) | spl8_29),
% 3.78/0.88    inference(resolution,[],[f595,f880])).
% 3.78/0.88  fof(f880,plain,(
% 3.78/0.88    ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | spl8_29),
% 3.78/0.88    inference(avatar_component_clause,[],[f878])).
% 3.78/0.88  fof(f595,plain,(
% 3.78/0.88    ( ! [X2,X0,X1] : (v1_funct_2(X0,X1,X2) | ~v1_xboole_0(X2) | ~v1_xboole_0(X0)) )),
% 3.78/0.88    inference(superposition,[],[f575,f154])).
% 3.78/0.88  fof(f575,plain,(
% 3.78/0.88    ( ! [X10,X11] : (v1_funct_2(k1_xboole_0,X10,X11) | ~v1_xboole_0(X11)) )),
% 3.78/0.88    inference(superposition,[],[f118,f543])).
% 3.78/0.88  fof(f543,plain,(
% 3.78/0.88    ( ! [X2,X3] : (k1_xboole_0 = sK7(X3,X2) | ~v1_xboole_0(X2)) )),
% 3.78/0.88    inference(resolution,[],[f539,f97])).
% 3.78/0.88  fof(f539,plain,(
% 3.78/0.88    ( ! [X12,X10,X11] : (~r2_hidden(X10,sK7(X11,X12)) | ~v1_xboole_0(X12)) )),
% 3.78/0.88    inference(duplicate_literal_removal,[],[f534])).
% 3.78/0.88  fof(f534,plain,(
% 3.78/0.88    ( ! [X12,X10,X11] : (~r2_hidden(X10,sK7(X11,X12)) | ~v1_xboole_0(X12) | ~v1_xboole_0(X12)) )),
% 3.78/0.88    inference(resolution,[],[f407,f206])).
% 3.78/0.88  fof(f206,plain,(
% 3.78/0.88    ( ! [X0,X1] : (r1_tarski(sK7(X1,X0),X0) | ~v1_xboole_0(X0)) )),
% 3.78/0.88    inference(superposition,[],[f204,f154])).
% 3.78/0.88  fof(f204,plain,(
% 3.78/0.88    ( ! [X0] : (r1_tarski(sK7(X0,k1_xboole_0),k1_xboole_0)) )),
% 3.78/0.88    inference(resolution,[],[f201,f108])).
% 3.78/0.88  fof(f201,plain,(
% 3.78/0.88    ( ! [X0] : (m1_subset_1(sK7(X0,k1_xboole_0),k1_zfmisc_1(k1_xboole_0))) )),
% 3.78/0.88    inference(superposition,[],[f113,f133])).
% 3.78/0.88  fof(f113,plain,(
% 3.78/0.88    ( ! [X0,X1] : (m1_subset_1(sK7(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.78/0.88    inference(cnf_transformation,[],[f69])).
% 3.78/0.88  fof(f69,plain,(
% 3.78/0.88    ! [X0,X1] : (v1_funct_2(sK7(X0,X1),X0,X1) & v1_funct_1(sK7(X0,X1)) & v5_relat_1(sK7(X0,X1),X1) & v4_relat_1(sK7(X0,X1),X0) & v1_relat_1(sK7(X0,X1)) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.88    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f15,f68])).
% 3.78/0.88  fof(f68,plain,(
% 3.78/0.88    ! [X1,X0] : (? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (v1_funct_2(sK7(X0,X1),X0,X1) & v1_funct_1(sK7(X0,X1)) & v5_relat_1(sK7(X0,X1),X1) & v4_relat_1(sK7(X0,X1),X0) & v1_relat_1(sK7(X0,X1)) & m1_subset_1(sK7(X0,X1),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 3.78/0.88    introduced(choice_axiom,[])).
% 3.78/0.88  fof(f15,axiom,(
% 3.78/0.88    ! [X0,X1] : ? [X2] : (v1_funct_2(X2,X0,X1) & v1_funct_1(X2) & v5_relat_1(X2,X1) & v4_relat_1(X2,X0) & v1_relat_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.78/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).
% 3.78/0.88  fof(f407,plain,(
% 3.78/0.88    ( ! [X2,X0,X1] : (~r1_tarski(X2,X0) | ~r2_hidden(X1,X2) | ~v1_xboole_0(X0)) )),
% 3.78/0.88    inference(resolution,[],[f123,f109])).
% 3.78/0.88  fof(f123,plain,(
% 3.78/0.88    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f42])).
% 3.78/0.88  fof(f42,plain,(
% 3.78/0.88    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.78/0.88    inference(ennf_transformation,[],[f9])).
% 3.78/0.88  fof(f9,axiom,(
% 3.78/0.88    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.78/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 3.78/0.88  fof(f118,plain,(
% 3.78/0.88    ( ! [X0,X1] : (v1_funct_2(sK7(X0,X1),X0,X1)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f69])).
% 3.78/0.88  fof(f8859,plain,(
% 3.78/0.88    ~spl8_34 | ~spl8_35 | ~spl8_165 | ~spl8_166 | spl8_122 | ~spl8_36 | ~spl8_32 | ~spl8_33),
% 3.78/0.88    inference(avatar_split_clause,[],[f8858,f951,f947,f963,f4758,f8823,f8819,f959,f955])).
% 3.78/0.88  fof(f4758,plain,(
% 3.78/0.88    spl8_122 <=> v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_122])])).
% 3.78/0.88  fof(f947,plain,(
% 3.78/0.88    spl8_32 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 3.78/0.88  fof(f951,plain,(
% 3.78/0.88    spl8_33 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_33])])).
% 3.78/0.88  fof(f8858,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | (~spl8_32 | ~spl8_33)),
% 3.78/0.88    inference(subsumption_resolution,[],[f8857,f948])).
% 3.78/0.88  fof(f948,plain,(
% 3.78/0.88    v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl8_32),
% 3.78/0.88    inference(avatar_component_clause,[],[f947])).
% 3.78/0.88  fof(f8857,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl8_33),
% 3.78/0.88    inference(subsumption_resolution,[],[f7480,f952])).
% 3.78/0.88  fof(f952,plain,(
% 3.78/0.88    l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl8_33),
% 3.78/0.88    inference(avatar_component_clause,[],[f951])).
% 3.78/0.88  fof(f7480,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.78/0.88    inference(subsumption_resolution,[],[f7479,f72])).
% 3.78/0.88  fof(f7479,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.78/0.88    inference(subsumption_resolution,[],[f2872,f73])).
% 3.78/0.88  fof(f2872,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.78/0.88    inference(resolution,[],[f153,f137])).
% 3.78/0.88  fof(f137,plain,(
% 3.78/0.88    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,X1) | v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.88    inference(duplicate_literal_removal,[],[f125])).
% 3.78/0.88  fof(f125,plain,(
% 3.78/0.88    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.88    inference(equality_resolution,[],[f89])).
% 3.78/0.88  fof(f89,plain,(
% 3.78/0.88    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f52])).
% 3.78/0.88  fof(f52,plain,(
% 3.78/0.88    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~v5_pre_topc(X2,X0,X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.78/0.88    inference(nnf_transformation,[],[f29])).
% 3.78/0.88  fof(f29,plain,(
% 3.78/0.88    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.78/0.88    inference(flattening,[],[f28])).
% 3.78/0.88  fof(f28,plain,(
% 3.78/0.88    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.78/0.88    inference(ennf_transformation,[],[f20])).
% 3.78/0.88  fof(f20,axiom,(
% 3.78/0.88    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))))))),
% 3.78/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_pre_topc)).
% 3.78/0.88  fof(f153,plain,(
% 3.78/0.88    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))),
% 3.78/0.88    inference(forward_demodulation,[],[f79,f80])).
% 3.78/0.88  fof(f79,plain,(
% 3.78/0.88    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))),
% 3.78/0.88    inference(cnf_transformation,[],[f51])).
% 3.78/0.88  fof(f8836,plain,(
% 3.78/0.88    ~spl8_122 | spl8_2),
% 3.78/0.88    inference(avatar_split_clause,[],[f3467,f144,f4758])).
% 3.78/0.88  fof(f144,plain,(
% 3.78/0.88    spl8_2 <=> v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 3.78/0.88  fof(f3467,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | spl8_2),
% 3.78/0.88    inference(forward_demodulation,[],[f146,f80])).
% 3.78/0.88  fof(f146,plain,(
% 3.78/0.88    ~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | spl8_2),
% 3.78/0.88    inference(avatar_component_clause,[],[f144])).
% 3.78/0.88  fof(f8835,plain,(
% 3.78/0.88    ~spl8_34 | ~spl8_35 | ~spl8_165 | ~spl8_166 | spl8_36 | ~spl8_122 | ~spl8_32 | ~spl8_33),
% 3.78/0.88    inference(avatar_split_clause,[],[f8834,f951,f947,f4758,f963,f8823,f8819,f959,f955])).
% 3.78/0.88  fof(f8834,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | (~spl8_32 | ~spl8_33)),
% 3.78/0.88    inference(subsumption_resolution,[],[f8833,f948])).
% 3.78/0.88  fof(f8833,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl8_33),
% 3.78/0.88    inference(subsumption_resolution,[],[f7523,f952])).
% 3.78/0.88  fof(f7523,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.78/0.88    inference(subsumption_resolution,[],[f7522,f72])).
% 3.78/0.88  fof(f7522,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.78/0.88    inference(subsumption_resolution,[],[f2871,f73])).
% 3.78/0.88  fof(f2871,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.78/0.88    inference(resolution,[],[f153,f138])).
% 3.78/0.88  fof(f138,plain,(
% 3.78/0.88    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | v5_pre_topc(X3,X0,X1) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.88    inference(duplicate_literal_removal,[],[f124])).
% 3.78/0.88  fof(f124,plain,(
% 3.78/0.88    ( ! [X0,X3,X1] : (v5_pre_topc(X3,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X3) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.88    inference(equality_resolution,[],[f90])).
% 3.78/0.88  fof(f90,plain,(
% 3.78/0.88    ( ! [X2,X0,X3,X1] : (v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))))) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f52])).
% 3.78/0.88  fof(f8245,plain,(
% 3.78/0.88    ~spl8_40 | spl8_60 | ~spl8_61 | ~spl8_89),
% 3.78/0.88    inference(avatar_contradiction_clause,[],[f8244])).
% 3.78/0.88  fof(f8244,plain,(
% 3.78/0.88    $false | (~spl8_40 | spl8_60 | ~spl8_61 | ~spl8_89)),
% 3.78/0.88    inference(subsumption_resolution,[],[f8243,f2111])).
% 3.78/0.88  fof(f2111,plain,(
% 3.78/0.88    k1_xboole_0 != u1_struct_0(sK1) | spl8_60),
% 3.78/0.88    inference(avatar_component_clause,[],[f2110])).
% 3.78/0.88  fof(f2110,plain,(
% 3.78/0.88    spl8_60 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_60])])).
% 3.78/0.88  fof(f8243,plain,(
% 3.78/0.88    k1_xboole_0 = u1_struct_0(sK1) | (~spl8_40 | ~spl8_61 | ~spl8_89)),
% 3.78/0.88    inference(subsumption_resolution,[],[f8221,f83])).
% 3.78/0.88  fof(f8221,plain,(
% 3.78/0.88    ~v1_xboole_0(k1_xboole_0) | k1_xboole_0 = u1_struct_0(sK1) | (~spl8_40 | ~spl8_61 | ~spl8_89)),
% 3.78/0.88    inference(resolution,[],[f2760,f5673])).
% 3.78/0.88  fof(f5673,plain,(
% 3.78/0.88    ( ! [X2,X3] : (~v1_partfun1(X2,X3) | ~v1_xboole_0(X2) | k1_xboole_0 = X3) ) | (~spl8_61 | ~spl8_89)),
% 3.78/0.88    inference(subsumption_resolution,[],[f5672,f261])).
% 3.78/0.88  fof(f261,plain,(
% 3.78/0.88    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.78/0.88    inference(superposition,[],[f253,f154])).
% 3.78/0.88  fof(f253,plain,(
% 3.78/0.88    v1_relat_1(k1_xboole_0)),
% 3.78/0.88    inference(resolution,[],[f119,f85])).
% 3.78/0.88  fof(f5672,plain,(
% 3.78/0.88    ( ! [X2,X3] : (k1_xboole_0 = X3 | ~v1_xboole_0(X2) | ~v1_partfun1(X2,X3) | ~v1_relat_1(X2)) ) | (~spl8_61 | ~spl8_89)),
% 3.78/0.88    inference(subsumption_resolution,[],[f5658,f373])).
% 3.78/0.88  fof(f5658,plain,(
% 3.78/0.88    ( ! [X2,X3] : (k1_xboole_0 = X3 | ~v1_xboole_0(X2) | ~v1_partfun1(X2,X3) | ~v4_relat_1(X2,X3) | ~v1_relat_1(X2)) ) | (~spl8_61 | ~spl8_89)),
% 3.78/0.88    inference(superposition,[],[f5650,f103])).
% 3.78/0.88  fof(f5650,plain,(
% 3.78/0.88    ( ! [X1] : (k1_xboole_0 = k1_relat_1(X1) | ~v1_xboole_0(X1)) ) | (~spl8_61 | ~spl8_89)),
% 3.78/0.88    inference(resolution,[],[f5603,f97])).
% 3.78/0.88  fof(f5603,plain,(
% 3.78/0.88    ( ! [X2,X3] : (~r2_hidden(X3,k1_relat_1(X2)) | ~v1_xboole_0(X2)) ) | (~spl8_61 | ~spl8_89)),
% 3.78/0.88    inference(duplicate_literal_removal,[],[f5591])).
% 3.78/0.88  fof(f5591,plain,(
% 3.78/0.88    ( ! [X2,X3] : (~v1_xboole_0(X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_xboole_0(X2)) ) | (~spl8_61 | ~spl8_89)),
% 3.78/0.88    inference(resolution,[],[f5288,f407])).
% 3.78/0.88  fof(f5288,plain,(
% 3.78/0.88    ( ! [X0] : (r1_tarski(k1_relat_1(X0),X0) | ~v1_xboole_0(X0)) ) | (~spl8_61 | ~spl8_89)),
% 3.78/0.88    inference(superposition,[],[f5169,f154])).
% 3.78/0.88  fof(f5169,plain,(
% 3.78/0.88    r1_tarski(k1_relat_1(k1_xboole_0),k1_xboole_0) | (~spl8_61 | ~spl8_89)),
% 3.78/0.88    inference(forward_demodulation,[],[f3145,f2115])).
% 3.78/0.88  fof(f2115,plain,(
% 3.78/0.88    k1_xboole_0 = sK3 | ~spl8_61),
% 3.78/0.88    inference(avatar_component_clause,[],[f2114])).
% 3.78/0.88  fof(f2114,plain,(
% 3.78/0.88    spl8_61 <=> k1_xboole_0 = sK3),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_61])])).
% 3.78/0.88  fof(f3145,plain,(
% 3.78/0.88    r1_tarski(k1_relat_1(sK3),sK3) | ~spl8_89),
% 3.78/0.88    inference(avatar_component_clause,[],[f3144])).
% 3.78/0.88  fof(f3144,plain,(
% 3.78/0.88    spl8_89 <=> r1_tarski(k1_relat_1(sK3),sK3)),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_89])])).
% 3.78/0.88  fof(f2760,plain,(
% 3.78/0.88    v1_partfun1(k1_xboole_0,u1_struct_0(sK1)) | (~spl8_40 | ~spl8_61)),
% 3.78/0.88    inference(backward_demodulation,[],[f1627,f2115])).
% 3.78/0.88  fof(f1627,plain,(
% 3.78/0.88    v1_partfun1(sK3,u1_struct_0(sK1)) | ~spl8_40),
% 3.78/0.88    inference(avatar_component_clause,[],[f1625])).
% 3.78/0.88  fof(f1625,plain,(
% 3.78/0.88    spl8_40 <=> v1_partfun1(sK3,u1_struct_0(sK1))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_40])])).
% 3.78/0.88  fof(f7996,plain,(
% 3.78/0.88    ~spl8_12 | spl8_47),
% 3.78/0.88    inference(avatar_split_clause,[],[f1765,f1751,f238])).
% 3.78/0.88  fof(f1751,plain,(
% 3.78/0.88    spl8_47 <=> r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK3)),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_47])])).
% 3.78/0.88  fof(f1765,plain,(
% 3.78/0.88    ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | spl8_47),
% 3.78/0.88    inference(resolution,[],[f1753,f159])).
% 3.78/0.88  fof(f159,plain,(
% 3.78/0.88    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) )),
% 3.78/0.88    inference(superposition,[],[f84,f154])).
% 3.78/0.88  fof(f84,plain,(
% 3.78/0.88    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f4])).
% 3.78/0.88  fof(f4,axiom,(
% 3.78/0.88    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.78/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 3.78/0.88  fof(f1753,plain,(
% 3.78/0.88    ~r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK3) | spl8_47),
% 3.78/0.88    inference(avatar_component_clause,[],[f1751])).
% 3.78/0.88  fof(f7203,plain,(
% 3.78/0.88    spl8_1 | ~spl8_31 | ~spl8_48 | ~spl8_60 | ~spl8_61),
% 3.78/0.88    inference(avatar_contradiction_clause,[],[f7202])).
% 3.78/0.88  fof(f7202,plain,(
% 3.78/0.88    $false | (spl8_1 | ~spl8_31 | ~spl8_48 | ~spl8_60 | ~spl8_61)),
% 3.78/0.88    inference(subsumption_resolution,[],[f7201,f83])).
% 3.78/0.88  fof(f7201,plain,(
% 3.78/0.88    ~v1_xboole_0(k1_xboole_0) | (spl8_1 | ~spl8_31 | ~spl8_48 | ~spl8_60 | ~spl8_61)),
% 3.78/0.88    inference(forward_demodulation,[],[f7200,f328])).
% 3.78/0.88  fof(f328,plain,(
% 3.78/0.88    ( ! [X8] : (k1_xboole_0 = sK7(X8,k1_xboole_0)) )),
% 3.78/0.88    inference(subsumption_resolution,[],[f321,f84])).
% 3.78/0.88  fof(f321,plain,(
% 3.78/0.88    ( ! [X8] : (k1_xboole_0 = sK7(X8,k1_xboole_0) | ~r1_tarski(k1_xboole_0,sK7(X8,k1_xboole_0))) )),
% 3.78/0.88    inference(resolution,[],[f107,f204])).
% 3.78/0.88  fof(f107,plain,(
% 3.78/0.88    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f64])).
% 3.78/0.88  fof(f64,plain,(
% 3.78/0.88    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/0.88    inference(flattening,[],[f63])).
% 3.78/0.88  fof(f63,plain,(
% 3.78/0.88    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.78/0.88    inference(nnf_transformation,[],[f3])).
% 3.78/0.88  fof(f3,axiom,(
% 3.78/0.88    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.78/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.78/0.88  fof(f7200,plain,(
% 3.78/0.88    ~v1_xboole_0(sK7(u1_struct_0(sK1),k1_xboole_0)) | (spl8_1 | ~spl8_31 | ~spl8_48 | ~spl8_60 | ~spl8_61)),
% 3.78/0.88    inference(forward_demodulation,[],[f7199,f5694])).
% 3.78/0.88  fof(f5694,plain,(
% 3.78/0.88    k1_xboole_0 = u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | (~spl8_48 | ~spl8_61)),
% 3.78/0.88    inference(forward_demodulation,[],[f1757,f2115])).
% 3.78/0.88  fof(f1757,plain,(
% 3.78/0.88    u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = sK3 | ~spl8_48),
% 3.78/0.88    inference(avatar_component_clause,[],[f1755])).
% 3.78/0.88  fof(f1755,plain,(
% 3.78/0.88    spl8_48 <=> u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = sK3),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_48])])).
% 3.78/0.88  fof(f7199,plain,(
% 3.78/0.88    ~v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | (spl8_1 | ~spl8_31 | ~spl8_60 | ~spl8_61)),
% 3.78/0.88    inference(subsumption_resolution,[],[f7198,f391])).
% 3.78/0.88  fof(f391,plain,(
% 3.78/0.88    ( ! [X5] : (v1_funct_2(k1_xboole_0,k1_xboole_0,X5)) )),
% 3.78/0.88    inference(superposition,[],[f118,f329])).
% 3.78/0.88  fof(f329,plain,(
% 3.78/0.88    ( ! [X9] : (k1_xboole_0 = sK7(k1_xboole_0,X9)) )),
% 3.78/0.88    inference(subsumption_resolution,[],[f322,f84])).
% 3.78/0.88  fof(f322,plain,(
% 3.78/0.88    ( ! [X9] : (k1_xboole_0 = sK7(k1_xboole_0,X9) | ~r1_tarski(k1_xboole_0,sK7(k1_xboole_0,X9))) )),
% 3.78/0.88    inference(resolution,[],[f107,f207])).
% 3.78/0.88  fof(f207,plain,(
% 3.78/0.88    ( ! [X0] : (r1_tarski(sK7(k1_xboole_0,X0),k1_xboole_0)) )),
% 3.78/0.88    inference(resolution,[],[f203,f108])).
% 3.78/0.88  fof(f203,plain,(
% 3.78/0.88    ( ! [X3] : (m1_subset_1(sK7(k1_xboole_0,X3),k1_zfmisc_1(k1_xboole_0))) )),
% 3.78/0.88    inference(superposition,[],[f113,f134])).
% 3.78/0.88  fof(f134,plain,(
% 3.78/0.88    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.78/0.88    inference(equality_resolution,[],[f111])).
% 3.78/0.88  fof(f111,plain,(
% 3.78/0.88    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.78/0.88    inference(cnf_transformation,[],[f67])).
% 3.78/0.88  fof(f7198,plain,(
% 3.78/0.88    ~v1_funct_2(k1_xboole_0,k1_xboole_0,u1_struct_0(sK2)) | ~v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | (spl8_1 | ~spl8_31 | ~spl8_60 | ~spl8_61)),
% 3.78/0.88    inference(forward_demodulation,[],[f7197,f329])).
% 3.78/0.88  fof(f7197,plain,(
% 3.78/0.88    ~v1_funct_2(sK7(k1_xboole_0,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_xboole_0,u1_struct_0(sK2)) | ~v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | (spl8_1 | ~spl8_31 | ~spl8_60 | ~spl8_61)),
% 3.78/0.88    inference(forward_demodulation,[],[f7196,f2112])).
% 3.78/0.88  fof(f2112,plain,(
% 3.78/0.88    k1_xboole_0 = u1_struct_0(sK1) | ~spl8_60),
% 3.78/0.88    inference(avatar_component_clause,[],[f2110])).
% 3.78/0.88  fof(f7196,plain,(
% 3.78/0.88    ~v1_funct_2(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | (spl8_1 | ~spl8_31 | ~spl8_61)),
% 3.78/0.88    inference(subsumption_resolution,[],[f7195,f158])).
% 3.78/0.88  fof(f7195,plain,(
% 3.78/0.88    ~m1_subset_1(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | (spl8_1 | ~spl8_31 | ~spl8_61)),
% 3.78/0.88    inference(subsumption_resolution,[],[f7194,f4916])).
% 3.78/0.88  fof(f4916,plain,(
% 3.78/0.88    ( ! [X0] : (~v5_pre_topc(X0,sK1,sK2) | ~v1_xboole_0(X0)) ) | (spl8_1 | ~spl8_61)),
% 3.78/0.88    inference(superposition,[],[f2740,f154])).
% 3.78/0.88  fof(f2740,plain,(
% 3.78/0.88    ~v5_pre_topc(k1_xboole_0,sK1,sK2) | (spl8_1 | ~spl8_61)),
% 3.78/0.88    inference(backward_demodulation,[],[f142,f2115])).
% 3.78/0.88  fof(f142,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,sK2) | spl8_1),
% 3.78/0.88    inference(avatar_component_clause,[],[f140])).
% 3.78/0.88  fof(f7194,plain,(
% 3.78/0.88    v5_pre_topc(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),sK1,sK2) | ~m1_subset_1(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2)) | ~v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | (~spl8_31 | ~spl8_61)),
% 3.78/0.88    inference(subsumption_resolution,[],[f7193,f70])).
% 3.78/0.88  fof(f7193,plain,(
% 3.78/0.88    v5_pre_topc(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),sK1,sK2) | ~m1_subset_1(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2)) | ~v2_pre_topc(sK1) | ~v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | (~spl8_31 | ~spl8_61)),
% 3.78/0.88    inference(subsumption_resolution,[],[f7192,f71])).
% 3.78/0.88  fof(f7192,plain,(
% 3.78/0.88    v5_pre_topc(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),sK1,sK2) | ~m1_subset_1(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | (~spl8_31 | ~spl8_61)),
% 3.78/0.88    inference(subsumption_resolution,[],[f7191,f72])).
% 3.78/0.88  fof(f7191,plain,(
% 3.78/0.88    v5_pre_topc(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),sK1,sK2) | ~m1_subset_1(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | (~spl8_31 | ~spl8_61)),
% 3.78/0.88    inference(subsumption_resolution,[],[f7174,f73])).
% 3.78/0.88  fof(f7174,plain,(
% 3.78/0.88    v5_pre_topc(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),sK1,sK2) | ~m1_subset_1(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~v1_xboole_0(sK7(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | (~spl8_31 | ~spl8_61)),
% 3.78/0.88    inference(resolution,[],[f968,f5571])).
% 3.78/0.88  fof(f5571,plain,(
% 3.78/0.88    ( ! [X0] : (v5_pre_topc(X0,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_xboole_0(X0)) ) | (~spl8_31 | ~spl8_61)),
% 3.78/0.88    inference(superposition,[],[f4886,f154])).
% 3.78/0.88  fof(f4886,plain,(
% 3.78/0.88    v5_pre_topc(k1_xboole_0,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | (~spl8_31 | ~spl8_61)),
% 3.78/0.88    inference(backward_demodulation,[],[f888,f2115])).
% 3.78/0.88  fof(f888,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl8_31),
% 3.78/0.88    inference(avatar_component_clause,[],[f886])).
% 3.78/0.88  fof(f886,plain,(
% 3.78/0.88    spl8_31 <=> v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_31])])).
% 3.78/0.88  fof(f968,plain,(
% 3.78/0.88    ( ! [X8,X9] : (~v5_pre_topc(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),X8,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))) | v5_pre_topc(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),X8,X9) | ~m1_subset_1(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))) | ~v1_funct_2(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),u1_struct_0(X8),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8)) )),
% 3.78/0.88    inference(subsumption_resolution,[],[f967,f117])).
% 3.78/0.88  fof(f117,plain,(
% 3.78/0.88    ( ! [X0,X1] : (v1_funct_1(sK7(X0,X1))) )),
% 3.78/0.88    inference(cnf_transformation,[],[f69])).
% 3.78/0.88  fof(f967,plain,(
% 3.78/0.88    ( ! [X8,X9] : (~v5_pre_topc(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),X8,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))) | v5_pre_topc(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),X8,X9) | ~v1_funct_1(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))))) | ~m1_subset_1(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))) | ~v1_funct_2(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),u1_struct_0(X8),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8)) )),
% 3.78/0.88    inference(subsumption_resolution,[],[f936,f118])).
% 3.78/0.88  fof(f936,plain,(
% 3.78/0.88    ( ! [X8,X9] : (~v5_pre_topc(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),X8,g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))) | v5_pre_topc(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),X8,X9) | ~v1_funct_2(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))) | ~v1_funct_1(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9))))) | ~m1_subset_1(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X8),u1_struct_0(X9)))) | ~v1_funct_2(sK7(u1_struct_0(X8),u1_struct_0(g1_pre_topc(u1_struct_0(X9),u1_pre_topc(X9)))),u1_struct_0(X8),u1_struct_0(X9)) | ~l1_pre_topc(X9) | ~v2_pre_topc(X9) | ~l1_pre_topc(X8) | ~v2_pre_topc(X8)) )),
% 3.78/0.88    inference(resolution,[],[f138,f113])).
% 3.78/0.88  fof(f4866,plain,(
% 3.78/0.88    spl8_61 | ~spl8_21),
% 3.78/0.88    inference(avatar_split_clause,[],[f4865,f423,f2114])).
% 3.78/0.88  fof(f423,plain,(
% 3.78/0.88    spl8_21 <=> ! [X11] : ~r2_hidden(X11,sK3)),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 3.78/0.88  fof(f4865,plain,(
% 3.78/0.88    k1_xboole_0 = sK3 | ~spl8_21),
% 3.78/0.88    inference(resolution,[],[f424,f97])).
% 3.78/0.88  fof(f424,plain,(
% 3.78/0.88    ( ! [X11] : (~r2_hidden(X11,sK3)) ) | ~spl8_21),
% 3.78/0.88    inference(avatar_component_clause,[],[f423])).
% 3.78/0.88  fof(f4860,plain,(
% 3.78/0.88    spl8_122 | ~spl8_2),
% 3.78/0.88    inference(avatar_split_clause,[],[f4859,f144,f4758])).
% 3.78/0.88  fof(f4859,plain,(
% 3.78/0.88    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl8_2),
% 3.78/0.88    inference(forward_demodulation,[],[f145,f80])).
% 3.78/0.88  fof(f145,plain,(
% 3.78/0.88    v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl8_2),
% 3.78/0.88    inference(avatar_component_clause,[],[f144])).
% 3.78/0.88  fof(f4716,plain,(
% 3.78/0.88    spl8_44 | ~spl8_21),
% 3.78/0.88    inference(avatar_split_clause,[],[f2611,f423,f1669])).
% 3.78/0.88  fof(f2611,plain,(
% 3.78/0.88    v1_xboole_0(sK3) | ~spl8_21),
% 3.78/0.88    inference(resolution,[],[f424,f94])).
% 3.78/0.88  fof(f94,plain,(
% 3.78/0.88    ( ! [X0] : (r2_hidden(sK5(X0),X0) | v1_xboole_0(X0)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f57])).
% 3.78/0.88  fof(f4708,plain,(
% 3.78/0.88    spl8_48 | ~spl8_13 | ~spl8_47),
% 3.78/0.88    inference(avatar_split_clause,[],[f3015,f1751,f242,f1755])).
% 3.78/0.88  fof(f242,plain,(
% 3.78/0.88    spl8_13 <=> r1_tarski(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 3.78/0.88  fof(f3015,plain,(
% 3.78/0.88    u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = sK3 | (~spl8_13 | ~spl8_47)),
% 3.78/0.88    inference(subsumption_resolution,[],[f3014,f244])).
% 3.78/0.88  fof(f244,plain,(
% 3.78/0.88    r1_tarski(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~spl8_13),
% 3.78/0.88    inference(avatar_component_clause,[],[f242])).
% 3.78/0.88  fof(f3014,plain,(
% 3.78/0.88    u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) = sK3 | ~r1_tarski(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~spl8_47),
% 3.78/0.88    inference(resolution,[],[f1752,f107])).
% 3.78/0.88  fof(f1752,plain,(
% 3.78/0.88    r1_tarski(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))),sK3) | ~spl8_47),
% 3.78/0.88    inference(avatar_component_clause,[],[f1751])).
% 3.78/0.88  fof(f4671,plain,(
% 3.78/0.88    spl8_21 | ~spl8_55),
% 3.78/0.88    inference(avatar_split_clause,[],[f2293,f1951,f423])).
% 3.78/0.88  fof(f2293,plain,(
% 3.78/0.88    ( ! [X1] : (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))) | ~r2_hidden(X1,sK3)) )),
% 3.78/0.88    inference(resolution,[],[f76,f123])).
% 3.78/0.88  fof(f4634,plain,(
% 3.78/0.88    ~spl8_44 | spl8_30),
% 3.78/0.88    inference(avatar_split_clause,[],[f4458,f882,f1669])).
% 3.78/0.88  fof(f882,plain,(
% 3.78/0.88    spl8_30 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_30])])).
% 3.78/0.88  fof(f4458,plain,(
% 3.78/0.88    ~v1_xboole_0(sK3) | spl8_30),
% 3.78/0.88    inference(resolution,[],[f884,f158])).
% 3.78/0.88  fof(f884,plain,(
% 3.78/0.88    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | spl8_30),
% 3.78/0.88    inference(avatar_component_clause,[],[f882])).
% 3.78/0.88  fof(f4628,plain,(
% 3.78/0.88    ~spl8_44 | ~spl8_9 | spl8_34),
% 3.78/0.88    inference(avatar_split_clause,[],[f1346,f955,f224,f1669])).
% 3.78/0.88  fof(f1346,plain,(
% 3.78/0.88    ~v1_xboole_0(u1_struct_0(sK2)) | ~v1_xboole_0(sK3) | spl8_34),
% 3.78/0.88    inference(resolution,[],[f595,f957])).
% 3.78/0.88  fof(f957,plain,(
% 3.78/0.88    ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | spl8_34),
% 3.78/0.88    inference(avatar_component_clause,[],[f955])).
% 3.78/0.88  fof(f4619,plain,(
% 3.78/0.88    spl8_12 | spl8_42),
% 3.78/0.88    inference(avatar_split_clause,[],[f4618,f1647,f238])).
% 3.78/0.88  fof(f1647,plain,(
% 3.78/0.88    spl8_42 <=> v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_42])])).
% 3.78/0.88  fof(f4618,plain,(
% 3.78/0.88    v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))),
% 3.78/0.88    inference(subsumption_resolution,[],[f4617,f74])).
% 3.78/0.88  fof(f4617,plain,(
% 3.78/0.88    ~v1_funct_1(sK3) | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))),
% 3.78/0.88    inference(subsumption_resolution,[],[f4472,f151])).
% 3.78/0.88  fof(f4472,plain,(
% 3.78/0.88    ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))),
% 3.78/0.88    inference(resolution,[],[f153,f100])).
% 3.78/0.88  fof(f100,plain,(
% 3.78/0.88    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f34])).
% 3.78/0.88  fof(f34,plain,(
% 3.78/0.88    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.78/0.88    inference(flattening,[],[f33])).
% 3.78/0.88  fof(f33,plain,(
% 3.78/0.88    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.78/0.88    inference(ennf_transformation,[],[f13])).
% 3.78/0.88  fof(f13,axiom,(
% 3.78/0.88    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.78/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 3.78/0.88  fof(f4613,plain,(
% 3.78/0.88    ~spl8_39 | spl8_89),
% 3.78/0.88    inference(avatar_split_clause,[],[f3152,f3144,f1579])).
% 3.78/0.88  fof(f3152,plain,(
% 3.78/0.88    ~v1_xboole_0(k1_relat_1(sK3)) | spl8_89),
% 3.78/0.88    inference(resolution,[],[f3146,f159])).
% 3.78/0.88  fof(f3146,plain,(
% 3.78/0.88    ~r1_tarski(k1_relat_1(sK3),sK3) | spl8_89),
% 3.78/0.88    inference(avatar_component_clause,[],[f3144])).
% 3.78/0.88  fof(f4579,plain,(
% 3.78/0.88    spl8_9 | spl8_40),
% 3.78/0.88    inference(avatar_split_clause,[],[f4578,f1625,f224])).
% 3.78/0.88  fof(f4578,plain,(
% 3.78/0.88    v1_partfun1(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK2))),
% 3.78/0.88    inference(subsumption_resolution,[],[f4577,f75])).
% 3.78/0.88  fof(f4577,plain,(
% 3.78/0.88    v1_partfun1(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK2)) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 3.78/0.88    inference(subsumption_resolution,[],[f2270,f74])).
% 3.78/0.88  fof(f2270,plain,(
% 3.78/0.88    ~v1_funct_1(sK3) | v1_partfun1(sK3,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK2)) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 3.78/0.88    inference(resolution,[],[f161,f709])).
% 3.78/0.88  fof(f709,plain,(
% 3.78/0.88    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_zfmisc_1(X1,X2)) | ~v1_funct_1(X0) | v1_partfun1(X0,X1) | v1_xboole_0(X2) | ~v1_funct_2(X0,X1,X2)) )),
% 3.78/0.88    inference(resolution,[],[f100,f109])).
% 3.78/0.88  fof(f161,plain,(
% 3.78/0.88    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))),
% 3.78/0.88    inference(resolution,[],[f108,f76])).
% 3.78/0.88  fof(f4498,plain,(
% 3.78/0.88    spl8_21 | ~spl8_22),
% 3.78/0.88    inference(avatar_split_clause,[],[f4478,f426,f423])).
% 3.78/0.88  fof(f4478,plain,(
% 3.78/0.88    ( ! [X1] : (~v1_xboole_0(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))) | ~r2_hidden(X1,sK3)) )),
% 3.78/0.88    inference(resolution,[],[f153,f123])).
% 3.78/0.88  fof(f4450,plain,(
% 3.78/0.88    ~spl8_30 | ~spl8_31 | spl8_2 | ~spl8_27 | ~spl8_28 | ~spl8_29),
% 3.78/0.88    inference(avatar_split_clause,[],[f4449,f878,f874,f870,f144,f886,f882])).
% 3.78/0.88  fof(f870,plain,(
% 3.78/0.88    spl8_27 <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 3.78/0.88  fof(f874,plain,(
% 3.78/0.88    spl8_28 <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 3.78/0.88  fof(f4449,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | (spl8_2 | ~spl8_27 | ~spl8_28 | ~spl8_29)),
% 3.78/0.88    inference(subsumption_resolution,[],[f4417,f879])).
% 3.78/0.88  fof(f879,plain,(
% 3.78/0.88    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~spl8_29),
% 3.78/0.88    inference(avatar_component_clause,[],[f878])).
% 3.78/0.88  fof(f4417,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | (spl8_2 | ~spl8_27 | ~spl8_28)),
% 3.78/0.88    inference(subsumption_resolution,[],[f4416,f151])).
% 3.78/0.88  fof(f4416,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | (spl8_2 | ~spl8_27 | ~spl8_28)),
% 3.78/0.88    inference(subsumption_resolution,[],[f3385,f3467])).
% 3.78/0.88  fof(f3385,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | (~spl8_27 | ~spl8_28)),
% 3.78/0.88    inference(subsumption_resolution,[],[f3384,f70])).
% 3.78/0.88  fof(f3384,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v2_pre_topc(sK1) | (~spl8_27 | ~spl8_28)),
% 3.78/0.88    inference(subsumption_resolution,[],[f3383,f71])).
% 3.78/0.88  fof(f3383,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_27 | ~spl8_28)),
% 3.78/0.88    inference(subsumption_resolution,[],[f3382,f871])).
% 3.78/0.88  fof(f871,plain,(
% 3.78/0.88    v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl8_27),
% 3.78/0.88    inference(avatar_component_clause,[],[f870])).
% 3.78/0.88  fof(f3382,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl8_28),
% 3.78/0.88    inference(subsumption_resolution,[],[f3381,f875])).
% 3.78/0.88  fof(f875,plain,(
% 3.78/0.88    l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl8_28),
% 3.78/0.88    inference(avatar_component_clause,[],[f874])).
% 3.78/0.88  fof(f3381,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.78/0.88    inference(subsumption_resolution,[],[f2870,f74])).
% 3.78/0.88  fof(f2870,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.78/0.88    inference(resolution,[],[f153,f135])).
% 3.78/0.88  fof(f4415,plain,(
% 3.78/0.88    spl8_31 | ~spl8_1 | ~spl8_29 | ~spl8_30),
% 3.78/0.88    inference(avatar_split_clause,[],[f4414,f882,f878,f140,f886])).
% 3.78/0.88  fof(f4414,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | (~spl8_1 | ~spl8_29 | ~spl8_30)),
% 3.78/0.88    inference(subsumption_resolution,[],[f4413,f70])).
% 3.78/0.88  fof(f4413,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v2_pre_topc(sK1) | (~spl8_1 | ~spl8_29 | ~spl8_30)),
% 3.78/0.88    inference(subsumption_resolution,[],[f4412,f71])).
% 3.78/0.88  fof(f4412,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_1 | ~spl8_29 | ~spl8_30)),
% 3.78/0.88    inference(subsumption_resolution,[],[f4411,f72])).
% 3.78/0.88  fof(f4411,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_1 | ~spl8_29 | ~spl8_30)),
% 3.78/0.88    inference(subsumption_resolution,[],[f4410,f73])).
% 3.78/0.88  fof(f4410,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_1 | ~spl8_29 | ~spl8_30)),
% 3.78/0.88    inference(subsumption_resolution,[],[f4409,f75])).
% 3.78/0.88  fof(f4409,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_1 | ~spl8_29 | ~spl8_30)),
% 3.78/0.88    inference(subsumption_resolution,[],[f4408,f76])).
% 3.78/0.88  fof(f4408,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_1 | ~spl8_29 | ~spl8_30)),
% 3.78/0.88    inference(subsumption_resolution,[],[f4407,f74])).
% 3.78/0.88  fof(f4407,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_1 | ~spl8_29 | ~spl8_30)),
% 3.78/0.88    inference(subsumption_resolution,[],[f4391,f879])).
% 3.78/0.88  fof(f4391,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_1 | ~spl8_30)),
% 3.78/0.88    inference(subsumption_resolution,[],[f4376,f141])).
% 3.78/0.88  fof(f141,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,sK2) | ~spl8_1),
% 3.78/0.88    inference(avatar_component_clause,[],[f140])).
% 3.78/0.88  fof(f4376,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,sK1,sK2) | v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl8_30),
% 3.78/0.88    inference(resolution,[],[f883,f137])).
% 3.78/0.88  fof(f883,plain,(
% 3.78/0.88    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~spl8_30),
% 3.78/0.88    inference(avatar_component_clause,[],[f882])).
% 3.78/0.88  fof(f2893,plain,(
% 3.78/0.88    ~spl8_29 | ~spl8_30 | spl8_31 | ~spl8_2 | ~spl8_27 | ~spl8_28),
% 3.78/0.88    inference(avatar_split_clause,[],[f2892,f874,f870,f144,f886,f882,f878])).
% 3.78/0.88  fof(f2892,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | (~spl8_2 | ~spl8_27 | ~spl8_28)),
% 3.78/0.88    inference(subsumption_resolution,[],[f2891,f70])).
% 3.78/0.88  fof(f2891,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v2_pre_topc(sK1) | (~spl8_2 | ~spl8_27 | ~spl8_28)),
% 3.78/0.88    inference(subsumption_resolution,[],[f2890,f71])).
% 3.78/0.88  fof(f2890,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_2 | ~spl8_27 | ~spl8_28)),
% 3.78/0.88    inference(subsumption_resolution,[],[f2889,f871])).
% 3.78/0.88  fof(f2889,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | (~spl8_2 | ~spl8_28)),
% 3.78/0.88    inference(subsumption_resolution,[],[f2888,f875])).
% 3.78/0.88  fof(f2888,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl8_2),
% 3.78/0.88    inference(subsumption_resolution,[],[f2887,f74])).
% 3.78/0.88  fof(f2887,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl8_2),
% 3.78/0.88    inference(subsumption_resolution,[],[f2886,f151])).
% 3.78/0.88  fof(f2886,plain,(
% 3.78/0.88    v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl8_2),
% 3.78/0.88    inference(subsumption_resolution,[],[f2869,f150])).
% 3.78/0.88  fof(f150,plain,(
% 3.78/0.88    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~spl8_2),
% 3.78/0.88    inference(forward_demodulation,[],[f145,f80])).
% 3.78/0.88  fof(f2869,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,sK1,g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))) | ~v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1)),
% 3.78/0.88    inference(resolution,[],[f153,f136])).
% 3.78/0.88  fof(f2694,plain,(
% 3.78/0.88    ~spl8_44 | spl8_35),
% 3.78/0.88    inference(avatar_split_clause,[],[f1907,f959,f1669])).
% 3.78/0.88  fof(f1907,plain,(
% 3.78/0.88    ~v1_xboole_0(sK3) | spl8_35),
% 3.78/0.88    inference(resolution,[],[f961,f158])).
% 3.78/0.88  fof(f961,plain,(
% 3.78/0.88    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | spl8_35),
% 3.78/0.88    inference(avatar_component_clause,[],[f959])).
% 3.78/0.88  fof(f2598,plain,(
% 3.78/0.88    ~spl8_42 | spl8_35 | ~spl8_40),
% 3.78/0.88    inference(avatar_split_clause,[],[f2597,f1625,f959,f1647])).
% 3.78/0.88  fof(f2597,plain,(
% 3.78/0.88    ~v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (spl8_35 | ~spl8_40)),
% 3.78/0.88    inference(subsumption_resolution,[],[f2546,f376])).
% 3.78/0.88  fof(f376,plain,(
% 3.78/0.88    v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))))),
% 3.78/0.88    inference(resolution,[],[f120,f153])).
% 3.78/0.88  fof(f2546,plain,(
% 3.78/0.88    ~v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (spl8_35 | ~spl8_40)),
% 3.78/0.88    inference(resolution,[],[f2358,f1908])).
% 3.78/0.88  fof(f1908,plain,(
% 3.78/0.88    ~r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2))) | spl8_35),
% 3.78/0.88    inference(resolution,[],[f961,f109])).
% 3.78/0.88  fof(f2358,plain,(
% 3.78/0.88    ( ! [X5] : (r1_tarski(sK3,k2_zfmisc_1(X5,u1_struct_0(sK2))) | ~v1_partfun1(sK3,X5) | ~v4_relat_1(sK3,X5)) ) | ~spl8_40),
% 3.78/0.88    inference(superposition,[],[f161,f1993])).
% 3.78/0.88  fof(f1993,plain,(
% 3.78/0.88    ( ! [X0] : (u1_struct_0(sK1) = X0 | ~v1_partfun1(sK3,X0) | ~v4_relat_1(sK3,X0)) ) | ~spl8_40),
% 3.78/0.88    inference(subsumption_resolution,[],[f1992,f254])).
% 3.78/0.88  fof(f1992,plain,(
% 3.78/0.88    ( ! [X0] : (u1_struct_0(sK1) = X0 | ~v1_relat_1(sK3) | ~v1_partfun1(sK3,X0) | ~v4_relat_1(sK3,X0)) ) | ~spl8_40),
% 3.78/0.88    inference(subsumption_resolution,[],[f1991,f375])).
% 3.78/0.88  fof(f375,plain,(
% 3.78/0.88    v4_relat_1(sK3,u1_struct_0(sK1))),
% 3.78/0.88    inference(resolution,[],[f120,f76])).
% 3.78/0.88  fof(f1991,plain,(
% 3.78/0.88    ( ! [X0] : (u1_struct_0(sK1) = X0 | ~v4_relat_1(sK3,u1_struct_0(sK1)) | ~v1_relat_1(sK3) | ~v1_partfun1(sK3,X0) | ~v4_relat_1(sK3,X0)) ) | ~spl8_40),
% 3.78/0.88    inference(resolution,[],[f1627,f708])).
% 3.78/0.88  fof(f708,plain,(
% 3.78/0.88    ( ! [X2,X0,X1] : (~v1_partfun1(X0,X2) | X1 = X2 | ~v4_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1)) )),
% 3.78/0.88    inference(duplicate_literal_removal,[],[f705])).
% 3.78/0.88  fof(f705,plain,(
% 3.78/0.88    ( ! [X2,X0,X1] : (X1 = X2 | ~v1_partfun1(X0,X2) | ~v4_relat_1(X0,X2) | ~v1_relat_1(X0) | ~v1_partfun1(X0,X1) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 3.78/0.88    inference(superposition,[],[f103,f103])).
% 3.78/0.88  fof(f2586,plain,(
% 3.78/0.88    ~spl8_12 | spl8_13),
% 3.78/0.88    inference(avatar_split_clause,[],[f2524,f242,f238])).
% 3.78/0.88  fof(f2524,plain,(
% 3.78/0.88    r1_tarski(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_xboole_0(u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))))),
% 3.78/0.88    inference(superposition,[],[f162,f157])).
% 3.78/0.88  fof(f162,plain,(
% 3.78/0.88    r1_tarski(sK3,k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))))),
% 3.78/0.88    inference(resolution,[],[f108,f153])).
% 3.78/0.88  fof(f2343,plain,(
% 3.78/0.88    ~spl8_34 | ~spl8_35 | spl8_36 | ~spl8_2 | ~spl8_32 | ~spl8_33),
% 3.78/0.88    inference(avatar_split_clause,[],[f2342,f951,f947,f144,f963,f959,f955])).
% 3.78/0.88  fof(f2342,plain,(
% 3.78/0.88    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | (~spl8_2 | ~spl8_32 | ~spl8_33)),
% 3.78/0.88    inference(subsumption_resolution,[],[f2341,f948])).
% 3.78/0.88  fof(f2341,plain,(
% 3.78/0.88    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | (~spl8_2 | ~spl8_33)),
% 3.78/0.88    inference(subsumption_resolution,[],[f2340,f952])).
% 3.78/0.88  fof(f2340,plain,(
% 3.78/0.88    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl8_2),
% 3.78/0.88    inference(subsumption_resolution,[],[f2339,f72])).
% 3.78/0.88  fof(f2339,plain,(
% 3.78/0.88    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~v2_pre_topc(sK2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl8_2),
% 3.78/0.88    inference(subsumption_resolution,[],[f2338,f73])).
% 3.78/0.88  fof(f2338,plain,(
% 3.78/0.88    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl8_2),
% 3.78/0.88    inference(subsumption_resolution,[],[f2337,f74])).
% 3.78/0.88  fof(f2337,plain,(
% 3.78/0.88    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl8_2),
% 3.78/0.88    inference(subsumption_resolution,[],[f2336,f151])).
% 3.78/0.88  fof(f2336,plain,(
% 3.78/0.88    v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~spl8_2),
% 3.78/0.88    inference(subsumption_resolution,[],[f2321,f150])).
% 3.78/0.88  fof(f2321,plain,(
% 3.78/0.88    ~v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),sK2) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2)))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)))) | ~v1_funct_2(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),u1_struct_0(sK2)) | ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 3.78/0.88    inference(resolution,[],[f153,f138])).
% 3.78/0.88  fof(f1905,plain,(
% 3.78/0.88    spl8_34 | ~spl8_40 | ~spl8_42),
% 3.78/0.88    inference(avatar_contradiction_clause,[],[f1904])).
% 3.78/0.88  fof(f1904,plain,(
% 3.78/0.88    $false | (spl8_34 | ~spl8_40 | ~spl8_42)),
% 3.78/0.88    inference(subsumption_resolution,[],[f1903,f376])).
% 3.78/0.88  fof(f1903,plain,(
% 3.78/0.88    ~v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (spl8_34 | ~spl8_40 | ~spl8_42)),
% 3.78/0.88    inference(subsumption_resolution,[],[f1901,f1649])).
% 3.78/0.88  fof(f1649,plain,(
% 3.78/0.88    v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~spl8_42),
% 3.78/0.88    inference(avatar_component_clause,[],[f1647])).
% 3.78/0.88  fof(f1901,plain,(
% 3.78/0.88    ~v1_partfun1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | ~v4_relat_1(sK3,u1_struct_0(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))) | (spl8_34 | ~spl8_40)),
% 3.78/0.88    inference(resolution,[],[f1808,f957])).
% 3.78/0.88  fof(f1808,plain,(
% 3.78/0.88    ( ! [X0] : (v1_funct_2(sK3,X0,u1_struct_0(sK2)) | ~v1_partfun1(sK3,X0) | ~v4_relat_1(sK3,X0)) ) | ~spl8_40),
% 3.78/0.88    inference(superposition,[],[f75,f1692])).
% 3.78/0.88  fof(f1692,plain,(
% 3.78/0.88    ( ! [X0] : (u1_struct_0(sK1) = X0 | ~v1_partfun1(sK3,X0) | ~v4_relat_1(sK3,X0)) ) | ~spl8_40),
% 3.78/0.88    inference(subsumption_resolution,[],[f1691,f254])).
% 3.78/0.88  fof(f1691,plain,(
% 3.78/0.88    ( ! [X0] : (u1_struct_0(sK1) = X0 | ~v1_relat_1(sK3) | ~v1_partfun1(sK3,X0) | ~v4_relat_1(sK3,X0)) ) | ~spl8_40),
% 3.78/0.88    inference(subsumption_resolution,[],[f1690,f375])).
% 3.78/0.88  fof(f1690,plain,(
% 3.78/0.88    ( ! [X0] : (u1_struct_0(sK1) = X0 | ~v4_relat_1(sK3,u1_struct_0(sK1)) | ~v1_relat_1(sK3) | ~v1_partfun1(sK3,X0) | ~v4_relat_1(sK3,X0)) ) | ~spl8_40),
% 3.78/0.88    inference(resolution,[],[f1627,f708])).
% 3.78/0.88  fof(f1367,plain,(
% 3.78/0.88    spl8_23 | spl8_37),
% 3.78/0.88    inference(avatar_split_clause,[],[f1363,f1365,f740])).
% 3.78/0.88  fof(f740,plain,(
% 3.78/0.88    spl8_23 <=> ! [X2] : v1_xboole_0(X2)),
% 3.78/0.88    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 3.78/0.88  fof(f1363,plain,(
% 3.78/0.88    ( ! [X6,X7] : (v1_partfun1(X6,k1_xboole_0) | v1_xboole_0(X7) | ~v1_xboole_0(X6)) )),
% 3.78/0.88    inference(subsumption_resolution,[],[f1362,f369])).
% 3.78/0.88  fof(f369,plain,(
% 3.78/0.88    ( ! [X0] : (v1_funct_1(X0) | ~v1_xboole_0(X0)) )),
% 3.78/0.88    inference(superposition,[],[f362,f154])).
% 3.78/0.88  fof(f362,plain,(
% 3.78/0.88    v1_funct_1(k1_xboole_0)),
% 3.78/0.88    inference(superposition,[],[f117,f328])).
% 3.78/0.88  fof(f1362,plain,(
% 3.78/0.88    ( ! [X6,X7] : (~v1_funct_1(X6) | v1_partfun1(X6,k1_xboole_0) | v1_xboole_0(X7) | ~v1_xboole_0(X6)) )),
% 3.78/0.88    inference(subsumption_resolution,[],[f1361,f158])).
% 3.78/0.88  fof(f1361,plain,(
% 3.78/0.88    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X6) | v1_partfun1(X6,k1_xboole_0) | v1_xboole_0(X7) | ~v1_xboole_0(X6)) )),
% 3.78/0.88    inference(subsumption_resolution,[],[f1358,f83])).
% 3.78/0.88  fof(f1358,plain,(
% 3.78/0.88    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X6) | v1_partfun1(X6,k1_xboole_0) | v1_xboole_0(X7) | ~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(X6)) )),
% 3.78/0.88    inference(resolution,[],[f720,f623])).
% 3.78/0.88  fof(f623,plain,(
% 3.78/0.88    ( ! [X2,X0,X1] : (v1_funct_2(X0,X1,X2) | ~v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 3.78/0.88    inference(superposition,[],[f603,f154])).
% 3.78/0.88  fof(f603,plain,(
% 3.78/0.88    ( ! [X10,X11] : (v1_funct_2(k1_xboole_0,X10,X11) | ~v1_xboole_0(X10)) )),
% 3.78/0.88    inference(superposition,[],[f118,f556])).
% 3.78/0.88  fof(f556,plain,(
% 3.78/0.88    ( ! [X2,X3] : (k1_xboole_0 = sK7(X2,X3) | ~v1_xboole_0(X2)) )),
% 3.78/0.88    inference(resolution,[],[f541,f97])).
% 3.78/0.88  fof(f541,plain,(
% 3.78/0.88    ( ! [X6,X4,X5] : (~r2_hidden(X4,sK7(X5,X6)) | ~v1_xboole_0(X5)) )),
% 3.78/0.88    inference(duplicate_literal_removal,[],[f532])).
% 3.78/0.88  fof(f532,plain,(
% 3.78/0.88    ( ! [X6,X4,X5] : (~r2_hidden(X4,sK7(X5,X6)) | ~v1_xboole_0(X5) | ~v1_xboole_0(X5)) )),
% 3.78/0.88    inference(resolution,[],[f407,f209])).
% 3.78/0.88  fof(f209,plain,(
% 3.78/0.88    ( ! [X0,X1] : (r1_tarski(sK7(X0,X1),X0) | ~v1_xboole_0(X0)) )),
% 3.78/0.88    inference(superposition,[],[f207,f154])).
% 3.78/0.88  fof(f720,plain,(
% 3.78/0.88    ( ! [X8,X9] : (~v1_funct_2(X9,k1_xboole_0,X8) | ~m1_subset_1(X9,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X9) | v1_partfun1(X9,k1_xboole_0) | v1_xboole_0(X8)) )),
% 3.78/0.88    inference(superposition,[],[f100,f134])).
% 3.78/0.88  fof(f977,plain,(
% 3.78/0.88    spl8_33),
% 3.78/0.88    inference(avatar_contradiction_clause,[],[f976])).
% 3.78/0.88  fof(f976,plain,(
% 3.78/0.88    $false | spl8_33),
% 3.78/0.88    inference(subsumption_resolution,[],[f973,f71])).
% 3.78/0.88  fof(f973,plain,(
% 3.78/0.88    ~l1_pre_topc(sK1) | spl8_33),
% 3.78/0.88    inference(resolution,[],[f953,f301])).
% 3.78/0.88  fof(f301,plain,(
% 3.78/0.88    ( ! [X5] : (l1_pre_topc(g1_pre_topc(u1_struct_0(X5),u1_pre_topc(X5))) | ~l1_pre_topc(X5)) )),
% 3.78/0.88    inference(resolution,[],[f102,f86])).
% 3.78/0.88  fof(f86,plain,(
% 3.78/0.88    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f25])).
% 3.78/0.88  fof(f25,plain,(
% 3.78/0.88    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.78/0.88    inference(ennf_transformation,[],[f17])).
% 3.78/0.88  fof(f17,axiom,(
% 3.78/0.88    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 3.78/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 3.78/0.88  fof(f102,plain,(
% 3.78/0.88    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | l1_pre_topc(g1_pre_topc(X0,X1))) )),
% 3.78/0.88    inference(cnf_transformation,[],[f35])).
% 3.78/0.88  fof(f35,plain,(
% 3.78/0.88    ! [X0,X1] : ((l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 3.78/0.88    inference(ennf_transformation,[],[f16])).
% 3.78/0.88  fof(f16,axiom,(
% 3.78/0.88    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => (l1_pre_topc(g1_pre_topc(X0,X1)) & v1_pre_topc(g1_pre_topc(X0,X1))))),
% 3.78/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_g1_pre_topc)).
% 3.78/0.88  fof(f953,plain,(
% 3.78/0.88    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl8_33),
% 3.78/0.88    inference(avatar_component_clause,[],[f951])).
% 3.78/0.88  fof(f972,plain,(
% 3.78/0.88    spl8_32),
% 3.78/0.88    inference(avatar_contradiction_clause,[],[f971])).
% 3.78/0.88  fof(f971,plain,(
% 3.78/0.88    $false | spl8_32),
% 3.78/0.88    inference(subsumption_resolution,[],[f970,f70])).
% 3.78/0.88  fof(f970,plain,(
% 3.78/0.88    ~v2_pre_topc(sK1) | spl8_32),
% 3.78/0.88    inference(subsumption_resolution,[],[f969,f71])).
% 3.78/0.88  fof(f969,plain,(
% 3.78/0.88    ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | spl8_32),
% 3.78/0.88    inference(resolution,[],[f949,f88])).
% 3.78/0.88  fof(f88,plain,(
% 3.78/0.88    ( ! [X0] : (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.78/0.88    inference(cnf_transformation,[],[f27])).
% 3.78/0.88  fof(f27,plain,(
% 3.78/0.88    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.78/0.88    inference(flattening,[],[f26])).
% 3.78/0.88  fof(f26,plain,(
% 3.78/0.88    ! [X0] : ((v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.78/0.88    inference(ennf_transformation,[],[f18])).
% 3.78/0.88  fof(f18,axiom,(
% 3.78/0.88    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))),
% 3.78/0.88    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).
% 3.78/0.88  fof(f949,plain,(
% 3.78/0.88    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | spl8_32),
% 3.78/0.88    inference(avatar_component_clause,[],[f947])).
% 3.78/0.88  fof(f899,plain,(
% 3.78/0.88    spl8_28),
% 3.78/0.88    inference(avatar_contradiction_clause,[],[f898])).
% 3.78/0.88  fof(f898,plain,(
% 3.78/0.88    $false | spl8_28),
% 3.78/0.88    inference(subsumption_resolution,[],[f896,f73])).
% 3.78/0.88  fof(f896,plain,(
% 3.78/0.88    ~l1_pre_topc(sK2) | spl8_28),
% 3.78/0.88    inference(resolution,[],[f876,f301])).
% 3.78/0.88  fof(f876,plain,(
% 3.78/0.88    ~l1_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | spl8_28),
% 3.78/0.88    inference(avatar_component_clause,[],[f874])).
% 3.78/0.88  fof(f895,plain,(
% 3.78/0.88    spl8_27),
% 3.78/0.88    inference(avatar_contradiction_clause,[],[f894])).
% 3.78/0.88  fof(f894,plain,(
% 3.78/0.88    $false | spl8_27),
% 3.78/0.88    inference(subsumption_resolution,[],[f893,f72])).
% 3.78/0.88  fof(f893,plain,(
% 3.78/0.88    ~v2_pre_topc(sK2) | spl8_27),
% 3.78/0.88    inference(subsumption_resolution,[],[f892,f73])).
% 3.78/0.88  fof(f892,plain,(
% 3.78/0.88    ~l1_pre_topc(sK2) | ~v2_pre_topc(sK2) | spl8_27),
% 3.78/0.88    inference(resolution,[],[f872,f88])).
% 3.78/0.88  fof(f872,plain,(
% 3.78/0.88    ~v2_pre_topc(g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | spl8_27),
% 3.78/0.88    inference(avatar_component_clause,[],[f870])).
% 3.78/0.88  fof(f801,plain,(
% 3.78/0.88    spl8_9 | ~spl8_23),
% 3.78/0.88    inference(avatar_contradiction_clause,[],[f795])).
% 3.78/0.88  fof(f795,plain,(
% 3.78/0.88    $false | (spl8_9 | ~spl8_23)),
% 3.78/0.88    inference(subsumption_resolution,[],[f226,f741])).
% 3.78/0.88  fof(f741,plain,(
% 3.78/0.88    ( ! [X2] : (v1_xboole_0(X2)) ) | ~spl8_23),
% 3.78/0.88    inference(avatar_component_clause,[],[f740])).
% 3.78/0.88  fof(f226,plain,(
% 3.78/0.88    ~v1_xboole_0(u1_struct_0(sK2)) | spl8_9),
% 3.78/0.88    inference(avatar_component_clause,[],[f224])).
% 3.78/0.88  fof(f148,plain,(
% 3.78/0.88    spl8_1 | spl8_2),
% 3.78/0.88    inference(avatar_split_clause,[],[f81,f144,f140])).
% 3.78/0.88  fof(f81,plain,(
% 3.78/0.88    v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | v5_pre_topc(sK3,sK1,sK2)),
% 3.78/0.88    inference(cnf_transformation,[],[f51])).
% 3.78/0.88  fof(f147,plain,(
% 3.78/0.88    ~spl8_1 | ~spl8_2),
% 3.78/0.88    inference(avatar_split_clause,[],[f82,f144,f140])).
% 3.78/0.88  fof(f82,plain,(
% 3.78/0.88    ~v5_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),g1_pre_topc(u1_struct_0(sK2),u1_pre_topc(sK2))) | ~v5_pre_topc(sK3,sK1,sK2)),
% 3.78/0.88    inference(cnf_transformation,[],[f51])).
% 3.78/0.88  % SZS output end Proof for theBenchmark
% 3.78/0.88  % (9894)------------------------------
% 3.78/0.88  % (9894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.78/0.88  % (9894)Termination reason: Refutation
% 3.78/0.88  
% 3.78/0.88  % (9894)Memory used [KB]: 9338
% 3.78/0.88  % (9894)Time elapsed: 0.442 s
% 3.78/0.88  % (9894)------------------------------
% 3.78/0.88  % (9894)------------------------------
% 3.78/0.89  % (9886)Success in time 0.526 s
%------------------------------------------------------------------------------
