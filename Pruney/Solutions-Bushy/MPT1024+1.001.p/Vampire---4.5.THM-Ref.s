%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1024+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 208 expanded)
%              Number of leaves         :   27 (  82 expanded)
%              Depth                    :   11
%              Number of atoms          :  444 (1055 expanded)
%              Number of equality atoms :   66 ( 202 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f171,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f65,f69,f78,f86,f89,f98,f113,f142,f144,f151,f162,f167,f170])).

fof(f170,plain,
    ( ~ spl8_4
    | ~ spl8_14 ),
    inference(avatar_contradiction_clause,[],[f169])).

fof(f169,plain,
    ( $false
    | ~ spl8_4
    | ~ spl8_14 ),
    inference(subsumption_resolution,[],[f77,f141])).

fof(f141,plain,
    ( ! [X0,X1] : ~ r2_hidden(X0,k9_relat_1(sK3,X1))
    | ~ spl8_14 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl8_14
  <=> ! [X1,X0] : ~ r2_hidden(X0,k9_relat_1(sK3,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_14])])).

fof(f77,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl8_4
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f167,plain,
    ( ~ spl8_2
    | spl8_17 ),
    inference(avatar_contradiction_clause,[],[f166])).

fof(f166,plain,
    ( $false
    | ~ spl8_2
    | spl8_17 ),
    inference(subsumption_resolution,[],[f64,f164])).

fof(f164,plain,
    ( ! [X0] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X0)))
    | spl8_17 ),
    inference(resolution,[],[f161,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relat_1(X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f49,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_relset_1)).

fof(f161,plain,
    ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))
    | spl8_17 ),
    inference(avatar_component_clause,[],[f160])).

fof(f160,plain,
    ( spl8_17
  <=> m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f64,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl8_2
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f162,plain,
    ( ~ spl8_5
    | ~ spl8_3
    | ~ spl8_4
    | ~ spl8_17
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f153,f148,f160,f76,f67,f81])).

fof(f81,plain,
    ( spl8_5
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f67,plain,
    ( spl8_3
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f148,plain,
    ( spl8_15
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK7(sK3,sK2,sK4),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f153,plain,
    ( ~ m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK0))
    | ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl8_15 ),
    inference(resolution,[],[f149,f57])).

fof(f57,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
                  & r2_hidden(sK6(X0,X1,X2),X1)
                  & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
                    & r2_hidden(sK7(X0,X1,X6),X1)
                    & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f29,f32,f31,f30])).

fof(f30,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK5(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = sK5(X0,X1,X2)
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( sK5(X0,X1,X2) = k1_funct_1(X0,sK6(X0,X1,X2))
        & r2_hidden(sK6(X0,X1,X2),X1)
        & r2_hidden(sK6(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
        & r2_hidden(sK7(X0,X1,X6),X1)
        & r2_hidden(sK7(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_funct_1)).

fof(f149,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(sK3,sK2,sK4),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) )
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f148])).

fof(f151,plain,
    ( spl8_15
    | ~ spl8_4
    | ~ spl8_11 ),
    inference(avatar_split_clause,[],[f146,f111,f76,f148])).

fof(f111,plain,
    ( spl8_11
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | ~ m1_subset_1(sK7(sK3,sK2,X0),sK0)
        | sK4 != X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f146,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK7(sK3,sK2,sK4),X0) )
    | ~ spl8_11 ),
    inference(equality_resolution,[],[f145])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( sK4 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | ~ m1_subset_1(X1,k1_zfmisc_1(sK0))
        | ~ r2_hidden(sK7(sK3,sK2,X0),X1) )
    | ~ spl8_11 ),
    inference(resolution,[],[f112,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

fof(f112,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK7(sK3,sK2,X0),sK0)
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | sK4 != X0 )
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f111])).

fof(f144,plain,
    ( ~ spl8_2
    | ~ spl8_13 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl8_2
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f64,f138])).

fof(f138,plain,
    ( ! [X2] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl8_13
  <=> ! [X2] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f142,plain,
    ( ~ spl8_5
    | spl8_13
    | spl8_14
    | ~ spl8_3
    | ~ spl8_10 ),
    inference(avatar_split_clause,[],[f135,f108,f67,f140,f137,f81])).

fof(f108,plain,
    ( spl8_10
  <=> ! [X1,X2] :
        ( ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,X2)))
        | ~ v1_relat_1(sK3) )
    | ~ spl8_3
    | ~ spl8_10 ),
    inference(resolution,[],[f123,f68])).

fof(f68,plain,
    ( v1_funct_1(sK3)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f123,plain,
    ( ! [X6,X8,X7,X5] :
        ( ~ v1_funct_1(X5)
        | ~ r2_hidden(X7,k9_relat_1(X5,X8))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK0,X6)))
        | ~ v1_relat_1(X5) )
    | ~ spl8_10 ),
    inference(resolution,[],[f115,f57])).

fof(f115,plain,
    ( ! [X4,X5,X3] :
        ( ~ r2_hidden(X3,k1_relat_1(X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) )
    | ~ spl8_10 ),
    inference(resolution,[],[f109,f72])).

fof(f109,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | ~ r2_hidden(X1,X2) )
    | ~ spl8_10 ),
    inference(avatar_component_clause,[],[f108])).

fof(f113,plain,
    ( spl8_10
    | spl8_11
    | ~ spl8_7 ),
    inference(avatar_split_clause,[],[f106,f96,f111,f108])).

fof(f96,plain,
    ( spl8_7
  <=> ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | ~ r2_hidden(sK7(sK3,sK2,X0),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f106,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | sK4 != X0
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(sK0))
        | ~ m1_subset_1(sK7(sK3,sK2,X0),sK0) )
    | ~ spl8_7 ),
    inference(resolution,[],[f97,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X2,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ m1_subset_1(X3,X1) ) ),
    inference(resolution,[],[f51,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | r2_hidden(X0,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f97,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK7(sK3,sK2,X0),sK0)
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | sK4 != X0 )
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f98,plain,
    ( ~ spl8_5
    | ~ spl8_3
    | spl8_7
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f93,f84,f96,f67,f81])).

fof(f84,plain,
    ( spl8_6
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f93,plain,
    ( ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(sK7(sK3,sK2,X0),sK0)
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl8_6 ),
    inference(duplicate_literal_removal,[],[f91])).

fof(f91,plain,
    ( ! [X0] :
        ( sK4 != X0
        | ~ r2_hidden(sK7(sK3,sK2,X0),sK0)
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | ~ r2_hidden(X0,k9_relat_1(sK3,sK2))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl8_6 ),
    inference(resolution,[],[f90,f56])).

fof(f56,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK7(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK7(sK3,X0,X1),sK2)
        | sK4 != X1
        | ~ r2_hidden(sK7(sK3,X0,X1),sK0)
        | ~ r2_hidden(X1,k9_relat_1(sK3,X0)) )
    | ~ spl8_6 ),
    inference(superposition,[],[f37,f85])).

fof(f85,plain,
    ( ! [X0,X1] :
        ( k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0
        | ~ r2_hidden(X0,k9_relat_1(sK3,X1)) )
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f37,plain,(
    ! [X5] :
      ( k1_funct_1(sK3,X5) != sK4
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X5,sK0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( ! [X5] :
        ( k1_funct_1(sK3,X5) != sK4
        | ~ r2_hidden(X5,sK2)
        | ~ r2_hidden(X5,sK0) )
    & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f13,f26,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK3,X5) != X4
              | ~ r2_hidden(X5,sK2)
              | ~ r2_hidden(X5,sK0) )
          & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X4] :
        ( ! [X5] :
            ( k1_funct_1(sK3,X5) != X4
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X5,sK0) )
        & r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) )
   => ( ! [X5] :
          ( k1_funct_1(sK3,X5) != sK4
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X5,sK0) )
      & r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t115_funct_2)).

fof(f89,plain,
    ( ~ spl8_2
    | spl8_5 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl8_2
    | spl8_5 ),
    inference(subsumption_resolution,[],[f64,f87])).

fof(f87,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl8_5 ),
    inference(resolution,[],[f82,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f82,plain,
    ( ~ v1_relat_1(sK3)
    | spl8_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f86,plain,
    ( ~ spl8_5
    | spl8_6
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f79,f67,f84,f81])).

fof(f79,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k9_relat_1(sK3,X1))
        | k1_funct_1(sK3,sK7(sK3,X1,X0)) = X0
        | ~ v1_relat_1(sK3) )
    | ~ spl8_3 ),
    inference(resolution,[],[f55,f68])).

fof(f55,plain,(
    ! [X6,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK7(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f78,plain,
    ( ~ spl8_2
    | spl8_4
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f73,f59,f76,f63])).

fof(f59,plain,
    ( spl8_1
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f73,plain,
    ( r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl8_1 ),
    inference(superposition,[],[f60,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f60,plain,
    ( r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f59])).

fof(f69,plain,(
    spl8_3 ),
    inference(avatar_split_clause,[],[f34,f67])).

fof(f34,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f27])).

fof(f65,plain,(
    spl8_2 ),
    inference(avatar_split_clause,[],[f35,f63])).

fof(f35,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f27])).

fof(f61,plain,(
    spl8_1 ),
    inference(avatar_split_clause,[],[f36,f59])).

fof(f36,plain,(
    r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f27])).

%------------------------------------------------------------------------------
