%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 233 expanded)
%              Number of leaves         :   24 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  454 (1297 expanded)
%              Number of equality atoms :   67 ( 155 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f146,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f72,f74,f78,f82,f86,f90,f96,f104,f110,f113,f120,f128,f134,f137,f140,f142,f145])).

fof(f145,plain,
    ( spl6_2
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(avatar_contradiction_clause,[],[f144])).

fof(f144,plain,
    ( $false
    | spl6_2
    | ~ spl6_8
    | ~ spl6_14 ),
    inference(subsumption_resolution,[],[f139,f143])).

fof(f143,plain,
    ( ! [X0] : ~ r2_hidden(sK4,k10_relat_1(sK3,X0))
    | spl6_2
    | ~ spl6_14 ),
    inference(resolution,[],[f65,f133])).

fof(f133,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k10_relat_1(sK3,X1)) )
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl6_14
  <=> ! [X1,X0] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k10_relat_1(sK3,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f65,plain,
    ( ~ r2_hidden(sK4,sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl6_2
  <=> r2_hidden(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f139,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_8
  <=> r2_hidden(sK4,k10_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f142,plain,
    ( ~ spl6_9
    | ~ spl6_7
    | ~ spl6_8
    | spl6_3 ),
    inference(avatar_split_clause,[],[f141,f67,f94,f88,f99])).

fof(f99,plain,
    ( spl6_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f88,plain,
    ( spl6_7
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f67,plain,
    ( spl6_3
  <=> r2_hidden(k1_funct_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f141,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | spl6_3 ),
    inference(resolution,[],[f68,f53])).

fof(f53,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ( ( ~ r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1)
                | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))
                | ~ r2_hidden(sK5(X0,X1,X2),X2) )
              & ( ( r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1)
                  & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK5(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).

% (7559)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
            | ~ r2_hidden(X3,k1_relat_1(X0))
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
              & r2_hidden(X3,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1)
          | ~ r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))
          | ~ r2_hidden(sK5(X0,X1,X2),X2) )
        & ( ( r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1)
            & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) )
          | r2_hidden(sK5(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X4),X1)
                  | ~ r2_hidden(X4,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X4),X1)
                    & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X4,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k10_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0))
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k1_funct_1(X0,X3),X1)
                  | ~ r2_hidden(X3,k1_relat_1(X0)) )
                & ( ( r2_hidden(k1_funct_1(X0,X3),X1)
                    & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k10_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k10_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k1_funct_1(X0,X3),X1)
                & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).

fof(f68,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f140,plain,
    ( spl6_8
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f138,f80,f61,f94])).

fof(f61,plain,
    ( spl6_1
  <=> r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f80,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f138,plain,
    ( r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | ~ spl6_1
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f70,f91])).

fof(f91,plain,
    ( ! [X0] : k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0)
    | ~ spl6_5 ),
    inference(resolution,[],[f51,f81])).

fof(f81,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f70,plain,
    ( r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f137,plain,
    ( ~ spl6_3
    | ~ spl6_2
    | spl6_8
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f136,f125,f102,f94,f64,f67])).

fof(f102,plain,
    ( spl6_10
  <=> ! [X1,X0] :
        ( ~ r2_hidden(k1_funct_1(sK3,X0),X1)
        | r2_hidden(X0,k10_relat_1(sK3,X1))
        | ~ r2_hidden(X0,k1_relat_1(sK3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f125,plain,
    ( spl6_13
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f136,plain,
    ( ~ r2_hidden(sK4,sK0)
    | ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | spl6_8
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f135,f126])).

fof(f126,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f125])).

fof(f135,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ r2_hidden(sK4,k1_relat_1(sK3))
    | spl6_8
    | ~ spl6_10 ),
    inference(resolution,[],[f103,f95])).

fof(f95,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f94])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,k10_relat_1(sK3,X1))
        | ~ r2_hidden(k1_funct_1(sK3,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f134,plain,
    ( ~ spl6_9
    | ~ spl6_7
    | spl6_14
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f129,f125,f132,f88,f99])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( r2_hidden(X0,sK0)
        | ~ r2_hidden(X0,k10_relat_1(sK3,X1))
        | ~ v1_funct_1(sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl6_13 ),
    inference(superposition,[],[f54,f126])).

fof(f54,plain,(
    ! [X4,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f37,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X4,X2)
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f128,plain,
    ( ~ spl6_5
    | spl6_13
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f122,f116,f125,f80])).

fof(f116,plain,
    ( spl6_12
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f122,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_12 ),
    inference(superposition,[],[f44,f117])).

fof(f117,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f116])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f120,plain,
    ( spl6_12
    | spl6_4
    | ~ spl6_6
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f114,f80,f84,f76,f116])).

fof(f76,plain,
    ( spl6_4
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f84,plain,
    ( spl6_6
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f114,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f45,f81])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f113,plain,(
    spl6_11 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl6_11 ),
    inference(resolution,[],[f109,f43])).

fof(f43,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f109,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl6_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl6_11
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f110,plain,
    ( ~ spl6_11
    | ~ spl6_5
    | spl6_9 ),
    inference(avatar_split_clause,[],[f106,f99,f80,f108])).

fof(f106,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl6_5
    | spl6_9 ),
    inference(resolution,[],[f105,f81])).

% (7546)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f105,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl6_9 ),
    inference(resolution,[],[f100,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f100,plain,
    ( ~ v1_relat_1(sK3)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f104,plain,
    ( ~ spl6_9
    | spl6_10
    | ~ spl6_7 ),
    inference(avatar_split_clause,[],[f97,f88,f102,f99])).

fof(f97,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(k1_funct_1(sK3,X0),X1)
        | ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(X0,k10_relat_1(sK3,X1))
        | ~ v1_relat_1(sK3) )
    | ~ spl6_7 ),
    inference(resolution,[],[f52,f89])).

fof(f89,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f52,plain,(
    ! [X4,X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | r2_hidden(X4,k10_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | ~ r2_hidden(k1_funct_1(X0,X4),X1)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | k10_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f96,plain,
    ( ~ spl6_8
    | spl6_1
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f92,f80,f61,f94])).

fof(f92,plain,
    ( ~ r2_hidden(sK4,k10_relat_1(sK3,sK2))
    | spl6_1
    | ~ spl6_5 ),
    inference(superposition,[],[f62,f91])).

fof(f62,plain,
    ( ~ r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f90,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f29,f88])).

fof(f29,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
      | ~ r2_hidden(sK4,sK0)
      | ~ r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) )
    & ( ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
        & r2_hidden(sK4,sK0) )
      | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) )
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ( ~ r2_hidden(k1_funct_1(X3,X4),X2)
              | ~ r2_hidden(X4,X0)
              | ~ r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) )
            & ( ( r2_hidden(k1_funct_1(X3,X4),X2)
                & r2_hidden(X4,X0) )
              | r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) ) )
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(sK3,X4),sK2)
            | ~ r2_hidden(X4,sK0)
            | ~ r2_hidden(X4,k8_relset_1(sK0,sK1,sK3,sK2)) )
          & ( ( r2_hidden(k1_funct_1(sK3,X4),sK2)
              & r2_hidden(X4,sK0) )
            | r2_hidden(X4,k8_relset_1(sK0,sK1,sK3,sK2)) ) )
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X4] :
        ( ( ~ r2_hidden(k1_funct_1(sK3,X4),sK2)
          | ~ r2_hidden(X4,sK0)
          | ~ r2_hidden(X4,k8_relset_1(sK0,sK1,sK3,sK2)) )
        & ( ( r2_hidden(k1_funct_1(sK3,X4),sK2)
            & r2_hidden(X4,sK0) )
          | r2_hidden(X4,k8_relset_1(sK0,sK1,sK3,sK2)) ) )
   => ( ( ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
        | ~ r2_hidden(sK4,sK0)
        | ~ r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) )
      & ( ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
          & r2_hidden(sK4,sK0) )
        | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X3,X4),X2)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) )
          & ( ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) )
            | r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ r2_hidden(k1_funct_1(X3,X4),X2)
            | ~ r2_hidden(X4,X0)
            | ~ r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) )
          & ( ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) )
            | r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <~> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
        <~> ( r2_hidden(k1_funct_1(X3,X4),X2)
            & r2_hidden(X4,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
            <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
                & r2_hidden(X4,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))
          <=> ( r2_hidden(k1_funct_1(X3,X4),X2)
              & r2_hidden(X4,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_2)).

fof(f86,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f30,f84])).

fof(f30,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f82,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f31,f80])).

fof(f31,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    ~ spl6_4 ),
    inference(avatar_split_clause,[],[f32,f76])).

fof(f32,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,
    ( spl6_1
    | spl6_2 ),
    inference(avatar_split_clause,[],[f33,f64,f61])).

fof(f33,plain,
    ( r2_hidden(sK4,sK0)
    | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f72,plain,
    ( spl6_1
    | spl6_3 ),
    inference(avatar_split_clause,[],[f34,f67,f61])).

fof(f34,plain,
    ( r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f69,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f35,f67,f64,f61])).

fof(f35,plain,
    ( ~ r2_hidden(k1_funct_1(sK3,sK4),sK2)
    | ~ r2_hidden(sK4,sK0)
    | ~ r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:33:06 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.21/0.47  % (7551)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (7551)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f69,f72,f74,f78,f82,f86,f90,f96,f104,f110,f113,f120,f128,f134,f137,f140,f142,f145])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    spl6_2 | ~spl6_8 | ~spl6_14),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f144])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    $false | (spl6_2 | ~spl6_8 | ~spl6_14)),
% 0.21/0.47    inference(subsumption_resolution,[],[f139,f143])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    ( ! [X0] : (~r2_hidden(sK4,k10_relat_1(sK3,X0))) ) | (spl6_2 | ~spl6_14)),
% 0.21/0.47    inference(resolution,[],[f65,f133])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,k10_relat_1(sK3,X1))) ) | ~spl6_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f132])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    spl6_14 <=> ! [X1,X0] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,k10_relat_1(sK3,X1)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.47  fof(f65,plain,(
% 0.21/0.47    ~r2_hidden(sK4,sK0) | spl6_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f64])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl6_2 <=> r2_hidden(sK4,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    r2_hidden(sK4,k10_relat_1(sK3,sK2)) | ~spl6_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl6_8 <=> r2_hidden(sK4,k10_relat_1(sK3,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    ~spl6_9 | ~spl6_7 | ~spl6_8 | spl6_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f141,f67,f94,f88,f99])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    spl6_9 <=> v1_relat_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    spl6_7 <=> v1_funct_1(sK3)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl6_3 <=> r2_hidden(k1_funct_1(sK3,sK4),sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    ~r2_hidden(sK4,k10_relat_1(sK3,sK2)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | spl6_3),
% 0.21/0.47    inference(resolution,[],[f68,f53])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    ( ! [X4,X0,X1] : (r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(equality_resolution,[],[f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X4,X2,X0,X1] : (r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ((~r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1) | ~r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f25,f26])).
% 0.21/0.48  % (7559)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((~r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1) | ~r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0)) | ~r2_hidden(sK5(X0,X1,X2),X2)) & ((r2_hidden(k1_funct_1(X0,sK5(X0,X1,X2)),X1) & r2_hidden(sK5(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK5(X0,X1,X2),X2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X4),X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X4,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(rectify,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : ((k10_relat_1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k1_funct_1(X0,X3),X1) | ~r2_hidden(X3,k1_relat_1(X0)))) & ((r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k10_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(nnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ! [X0] : (! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k10_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k1_funct_1(X0,X3),X1) & r2_hidden(X3,k1_relat_1(X0))))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_funct_1)).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~r2_hidden(k1_funct_1(sK3,sK4),sK2) | spl6_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f67])).
% 0.21/0.48  fof(f140,plain,(
% 0.21/0.48    spl6_8 | ~spl6_1 | ~spl6_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f138,f80,f61,f94])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl6_1 <=> r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl6_5 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    r2_hidden(sK4,k10_relat_1(sK3,sK2)) | (~spl6_1 | ~spl6_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f70,f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0] : (k8_relset_1(sK0,sK1,sK3,X0) = k10_relat_1(sK3,X0)) ) | ~spl6_5),
% 0.21/0.48    inference(resolution,[],[f51,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) | ~spl6_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    ~spl6_3 | ~spl6_2 | spl6_8 | ~spl6_10 | ~spl6_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f136,f125,f102,f94,f64,f67])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    spl6_10 <=> ! [X1,X0] : (~r2_hidden(k1_funct_1(sK3,X0),X1) | r2_hidden(X0,k10_relat_1(sK3,X1)) | ~r2_hidden(X0,k1_relat_1(sK3)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    spl6_13 <=> sK0 = k1_relat_1(sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ~r2_hidden(sK4,sK0) | ~r2_hidden(k1_funct_1(sK3,sK4),sK2) | (spl6_8 | ~spl6_10 | ~spl6_13)),
% 0.21/0.48    inference(forward_demodulation,[],[f135,f126])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK3) | ~spl6_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f125])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ~r2_hidden(k1_funct_1(sK3,sK4),sK2) | ~r2_hidden(sK4,k1_relat_1(sK3)) | (spl6_8 | ~spl6_10)),
% 0.21/0.48    inference(resolution,[],[f103,f95])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k10_relat_1(sK3,sK2)) | spl6_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f94])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X0,k10_relat_1(sK3,X1)) | ~r2_hidden(k1_funct_1(sK3,X0),X1) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl6_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f102])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    ~spl6_9 | ~spl6_7 | spl6_14 | ~spl6_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f129,f125,f132,f88,f99])).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r2_hidden(X0,sK0) | ~r2_hidden(X0,k10_relat_1(sK3,X1)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3)) ) | ~spl6_13),
% 0.21/0.48    inference(superposition,[],[f54,f126])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X4,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X4,X2) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    ~spl6_5 | spl6_13 | ~spl6_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f122,f116,f125,f80])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl6_12 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl6_12),
% 0.21/0.48    inference(superposition,[],[f44,f117])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f116])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    spl6_12 | spl6_4 | ~spl6_6 | ~spl6_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f114,f80,f84,f76,f116])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl6_4 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl6_6 <=> v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl6_5),
% 0.21/0.48    inference(resolution,[],[f45,f81])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(nnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    spl6_11),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f111])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    $false | spl6_11),
% 0.21/0.48    inference(resolution,[],[f109,f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl6_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f108])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl6_11 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ~spl6_11 | ~spl6_5 | spl6_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f106,f99,f80,f108])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl6_5 | spl6_9)),
% 0.21/0.48    inference(resolution,[],[f105,f81])).
% 0.21/0.48  % (7546)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl6_9),
% 0.21/0.48    inference(resolution,[],[f100,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    ~v1_relat_1(sK3) | spl6_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ~spl6_9 | spl6_10 | ~spl6_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f97,f88,f102,f99])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r2_hidden(k1_funct_1(sK3,X0),X1) | ~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(X0,k10_relat_1(sK3,X1)) | ~v1_relat_1(sK3)) ) | ~spl6_7),
% 0.21/0.48    inference(resolution,[],[f52,f89])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    v1_funct_1(sK3) | ~spl6_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f88])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X4,X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0)) | r2_hidden(X4,k10_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | ~r2_hidden(k1_funct_1(X0,X4),X1) | ~r2_hidden(X4,k1_relat_1(X0)) | k10_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ~spl6_8 | spl6_1 | ~spl6_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f92,f80,f61,f94])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k10_relat_1(sK3,sK2)) | (spl6_1 | ~spl6_5)),
% 0.21/0.48    inference(superposition,[],[f62,f91])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ~r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)) | spl6_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl6_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f88])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    v1_funct_1(sK3)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ((~r2_hidden(k1_funct_1(sK3,sK4),sK2) | ~r2_hidden(sK4,sK0) | ~r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))) & ((r2_hidden(k1_funct_1(sK3,sK4),sK2) & r2_hidden(sK4,sK0)) | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2)))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f19,f21,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : ((~r2_hidden(k1_funct_1(X3,X4),X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))) & ((r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)) | r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : ((~r2_hidden(k1_funct_1(sK3,X4),sK2) | ~r2_hidden(X4,sK0) | ~r2_hidden(X4,k8_relset_1(sK0,sK1,sK3,sK2))) & ((r2_hidden(k1_funct_1(sK3,X4),sK2) & r2_hidden(X4,sK0)) | r2_hidden(X4,k8_relset_1(sK0,sK1,sK3,sK2)))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X4] : ((~r2_hidden(k1_funct_1(sK3,X4),sK2) | ~r2_hidden(X4,sK0) | ~r2_hidden(X4,k8_relset_1(sK0,sK1,sK3,sK2))) & ((r2_hidden(k1_funct_1(sK3,X4),sK2) & r2_hidden(X4,sK0)) | r2_hidden(X4,k8_relset_1(sK0,sK1,sK3,sK2)))) => ((~r2_hidden(k1_funct_1(sK3,sK4),sK2) | ~r2_hidden(sK4,sK0) | ~r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))) & ((r2_hidden(k1_funct_1(sK3,sK4),sK2) & r2_hidden(sK4,sK0)) | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : ((~r2_hidden(k1_funct_1(X3,X4),X2) | ~r2_hidden(X4,X0) | ~r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))) & ((r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)) | r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (((~r2_hidden(k1_funct_1(X3,X4),X2) | ~r2_hidden(X4,X0)) | ~r2_hidden(X4,k8_relset_1(X0,X1,X3,X2))) & ((r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)) | r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.48    inference(nnf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (? [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <~> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 0.21/0.48    inference(flattening,[],[f9])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : ((? [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <~> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <=> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f7])).
% 0.21/0.48  fof(f7,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (r2_hidden(X4,k8_relset_1(X0,X1,X3,X2)) <=> (r2_hidden(k1_funct_1(X3,X4),X2) & r2_hidden(X4,X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_funct_2)).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    spl6_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f84])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v1_funct_2(sK3,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    spl6_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f80])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ~spl6_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f76])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    k1_xboole_0 != sK1),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl6_1 | spl6_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f64,f61])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    r2_hidden(sK4,sK0) | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl6_1 | spl6_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f67,f61])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    r2_hidden(k1_funct_1(sK3,sK4),sK2) | r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f67,f64,f61])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~r2_hidden(k1_funct_1(sK3,sK4),sK2) | ~r2_hidden(sK4,sK0) | ~r2_hidden(sK4,k8_relset_1(sK0,sK1,sK3,sK2))),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (7551)------------------------------
% 0.21/0.48  % (7551)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7551)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (7551)Memory used [KB]: 10746
% 0.21/0.48  % (7551)Time elapsed: 0.057 s
% 0.21/0.48  % (7551)------------------------------
% 0.21/0.48  % (7551)------------------------------
% 0.21/0.48  % (7541)Success in time 0.121 s
%------------------------------------------------------------------------------
