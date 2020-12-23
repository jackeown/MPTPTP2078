%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:30 EST 2020

% Result     : Theorem 1.19s
% Output     : Refutation 1.19s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 194 expanded)
%              Number of leaves         :   32 (  90 expanded)
%              Depth                    :    9
%              Number of atoms          :  408 ( 966 expanded)
%              Number of equality atoms :   90 ( 221 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f94,f98,f102,f108,f116,f122,f125,f135,f143,f200,f208,f209,f230])).

fof(f230,plain,
    ( ~ spl9_3
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(avatar_split_clause,[],[f227,f141,f114,f80])).

fof(f80,plain,
    ( spl9_3
  <=> r2_hidden(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f114,plain,
    ( spl9_11
  <=> ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(k4_tarski(X0,sK4),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f141,plain,
    ( spl9_16
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).

fof(f227,plain,
    ( ~ r2_hidden(sK5,sK2)
    | ~ spl9_11
    | ~ spl9_16 ),
    inference(resolution,[],[f142,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k4_tarski(X0,sK4),sK3)
        | ~ r2_hidden(X0,sK2) )
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f142,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl9_16 ),
    inference(avatar_component_clause,[],[f141])).

fof(f209,plain,
    ( sK0 != k1_relat_1(sK3)
    | r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK5,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f208,plain,
    ( ~ spl9_6
    | spl9_24
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f202,f196,f205,f92])).

fof(f92,plain,
    ( spl9_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f205,plain,
    ( spl9_24
  <=> sK0 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f196,plain,
    ( spl9_23
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f202,plain,
    ( sK0 = k1_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_23 ),
    inference(superposition,[],[f52,f197])).

fof(f197,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f196])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f200,plain,
    ( spl9_23
    | spl9_5
    | ~ spl9_7
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f194,f92,f96,f88,f196])).

fof(f88,plain,
    ( spl9_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f96,plain,
    ( spl9_7
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f194,plain,
    ( ~ v1_funct_2(sK3,sK0,sK1)
    | k1_xboole_0 = sK1
    | sK0 = k1_relset_1(sK0,sK1,sK3)
    | ~ spl9_6 ),
    inference(resolution,[],[f53,f93])).

fof(f93,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl9_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f143,plain,
    ( ~ spl9_15
    | spl9_16
    | ~ spl9_2
    | ~ spl9_14 ),
    inference(avatar_split_clause,[],[f136,f133,f76,f141,f138])).

fof(f138,plain,
    ( spl9_15
  <=> r2_hidden(sK5,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f76,plain,
    ( spl9_2
  <=> sK4 = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f133,plain,
    ( spl9_14
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).

fof(f136,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ spl9_2
    | ~ spl9_14 ),
    inference(superposition,[],[f134,f77])).

fof(f77,plain,
    ( sK4 = k1_funct_1(sK3,sK5)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f134,plain,
    ( ! [X0] :
        ( r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
        | ~ r2_hidden(X0,k1_relat_1(sK3)) )
    | ~ spl9_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f135,plain,
    ( ~ spl9_10
    | spl9_14
    | ~ spl9_8 ),
    inference(avatar_split_clause,[],[f131,f100,f133,f111])).

fof(f111,plain,
    ( spl9_10
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).

fof(f100,plain,
    ( spl9_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_relat_1(sK3))
        | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3)
        | ~ v1_relat_1(sK3) )
    | ~ spl9_8 ),
    inference(resolution,[],[f65,f101])).

fof(f101,plain,
    ( v1_funct_1(sK3)
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f100])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X0)
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X1,X2),X0)
      | k1_funct_1(X0,X1) != X2
      | ~ r2_hidden(X1,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( ( k1_funct_1(X0,X1) = X2
                | k1_xboole_0 != X2 )
              & ( k1_xboole_0 = X2
                | k1_funct_1(X0,X1) != X2 ) )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( ( k1_funct_1(X0,X1) = X2
                | ~ r2_hidden(k4_tarski(X1,X2),X0) )
              & ( r2_hidden(k4_tarski(X1,X2),X0)
                | k1_funct_1(X0,X1) != X2 ) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 )
            | r2_hidden(X1,k1_relat_1(X0)) )
          & ( ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) )
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( ( ~ r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> k1_xboole_0 = X2 ) )
          & ( r2_hidden(X1,k1_relat_1(X0))
           => ( k1_funct_1(X0,X1) = X2
            <=> r2_hidden(k4_tarski(X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).

fof(f125,plain,(
    spl9_12 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | spl9_12 ),
    inference(resolution,[],[f121,f51])).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f121,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl9_12 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl9_12
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).

fof(f122,plain,
    ( ~ spl9_12
    | ~ spl9_6
    | spl9_10 ),
    inference(avatar_split_clause,[],[f118,f111,f92,f120])).

fof(f118,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl9_6
    | spl9_10 ),
    inference(resolution,[],[f117,f93])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl9_10 ),
    inference(resolution,[],[f112,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f112,plain,
    ( ~ v1_relat_1(sK3)
    | spl9_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f116,plain,
    ( ~ spl9_10
    | spl9_11
    | spl9_9 ),
    inference(avatar_split_clause,[],[f109,f106,f114,f111])).

fof(f106,plain,
    ( spl9_9
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | ~ r2_hidden(k4_tarski(X0,sK4),sK3)
        | ~ v1_relat_1(sK3) )
    | spl9_9 ),
    inference(resolution,[],[f60,f107])).

fof(f107,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl9_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f60,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK6(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK7(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) )
                | r2_hidden(sK6(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK8(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f25,f28,f27,f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( ~ r2_hidden(X4,X1)
                | ~ r2_hidden(k4_tarski(X4,X3),X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( r2_hidden(X5,X1)
                & r2_hidden(k4_tarski(X5,X3),X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( ~ r2_hidden(X4,X1)
              | ~ r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK6(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) )
          | r2_hidden(sK6(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0) )
     => ( r2_hidden(sK7(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK8(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( r2_hidden(X5,X1)
                      & r2_hidden(k4_tarski(X5,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ? [X8] :
                      ( r2_hidden(X8,X1)
                      & r2_hidden(k4_tarski(X8,X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(k4_tarski(X4,X3),X0) ) )
                & ( ? [X4] :
                      ( r2_hidden(X4,X1)
                      & r2_hidden(k4_tarski(X4,X3),X0) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).

fof(f108,plain,
    ( ~ spl9_9
    | spl9_1
    | ~ spl9_6 ),
    inference(avatar_split_clause,[],[f104,f92,f72,f106])).

fof(f72,plain,
    ( spl9_1
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f104,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl9_1
    | ~ spl9_6 ),
    inference(superposition,[],[f73,f103])).

fof(f103,plain,
    ( ! [X0] : k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)
    | ~ spl9_6 ),
    inference(resolution,[],[f59,f93])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f73,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | spl9_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f102,plain,(
    spl9_8 ),
    inference(avatar_split_clause,[],[f32,f100])).

fof(f32,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & sK4 = k1_funct_1(sK3,sK5)
    & r2_hidden(sK5,sK2)
    & r2_hidden(sK5,sK0)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
            & ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) ) )
        & k1_xboole_0 != X1
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))
          & ? [X5] :
              ( k1_funct_1(sK3,X5) = X4
              & r2_hidden(X5,sK2)
              & r2_hidden(X5,sK0) ) )
      & k1_xboole_0 != sK1
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X4] :
        ( ~ r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2))
        & ? [X5] :
            ( k1_funct_1(sK3,X5) = X4
            & r2_hidden(X5,sK2)
            & r2_hidden(X5,sK0) ) )
   => ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
      & ? [X5] :
          ( k1_funct_1(sK3,X5) = sK4
          & r2_hidden(X5,sK2)
          & r2_hidden(X5,sK0) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X5] :
        ( k1_funct_1(sK3,X5) = sK4
        & r2_hidden(X5,sK2)
        & r2_hidden(X5,sK0) )
   => ( sK4 = k1_funct_1(sK3,sK5)
      & r2_hidden(sK5,sK2)
      & r2_hidden(sK5,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ~ r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))
          & ? [X5] :
              ( k1_funct_1(X3,X5) = X4
              & r2_hidden(X5,X2)
              & r2_hidden(X5,X0) ) )
      & k1_xboole_0 != X1
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ( k1_xboole_0 != X1
         => ! [X4] :
              ( ? [X5] :
                  ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
             => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( k1_xboole_0 != X1
       => ! [X4] :
            ( ? [X5] :
                ( k1_funct_1(X3,X5) = X4
                & r2_hidden(X5,X2)
                & r2_hidden(X5,X0) )
           => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_2)).

fof(f98,plain,(
    spl9_7 ),
    inference(avatar_split_clause,[],[f33,f96])).

fof(f33,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f94,plain,(
    spl9_6 ),
    inference(avatar_split_clause,[],[f34,f92])).

fof(f34,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f90,plain,(
    ~ spl9_5 ),
    inference(avatar_split_clause,[],[f35,f88])).

fof(f35,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f86,plain,(
    spl9_4 ),
    inference(avatar_split_clause,[],[f36,f84])).

fof(f84,plain,
    ( spl9_4
  <=> r2_hidden(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f36,plain,(
    r2_hidden(sK5,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f82,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f37,f80])).

fof(f37,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f78,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f38,f76])).

fof(f38,plain,(
    sK4 = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f23])).

fof(f74,plain,(
    ~ spl9_1 ),
    inference(avatar_split_clause,[],[f39,f72])).

fof(f39,plain,(
    ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:31:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.37  ipcrm: permission denied for id (1209401344)
% 0.15/0.38  ipcrm: permission denied for id (1209434114)
% 0.15/0.38  ipcrm: permission denied for id (1209466883)
% 0.15/0.38  ipcrm: permission denied for id (1209532422)
% 0.15/0.38  ipcrm: permission denied for id (1209565191)
% 0.15/0.39  ipcrm: permission denied for id (1209663499)
% 0.15/0.39  ipcrm: permission denied for id (1209761807)
% 0.15/0.40  ipcrm: permission denied for id (1209892882)
% 0.15/0.40  ipcrm: permission denied for id (1209925651)
% 0.22/0.41  ipcrm: permission denied for id (1210089500)
% 0.22/0.41  ipcrm: permission denied for id (1210155040)
% 0.22/0.42  ipcrm: permission denied for id (1210220579)
% 0.22/0.42  ipcrm: permission denied for id (1210253348)
% 0.22/0.42  ipcrm: permission denied for id (1210286118)
% 0.22/0.43  ipcrm: permission denied for id (1210417195)
% 0.22/0.43  ipcrm: permission denied for id (1210515502)
% 0.22/0.43  ipcrm: permission denied for id (1210548271)
% 0.22/0.44  ipcrm: permission denied for id (1210679347)
% 0.22/0.44  ipcrm: permission denied for id (1210744885)
% 0.22/0.44  ipcrm: permission denied for id (1210777654)
% 0.22/0.44  ipcrm: permission denied for id (1210810423)
% 0.22/0.44  ipcrm: permission denied for id (1210843192)
% 0.22/0.45  ipcrm: permission denied for id (1211072575)
% 0.22/0.45  ipcrm: permission denied for id (1211138113)
% 0.22/0.45  ipcrm: permission denied for id (1211170882)
% 0.22/0.46  ipcrm: permission denied for id (1211269188)
% 0.22/0.46  ipcrm: permission denied for id (1211301958)
% 0.22/0.46  ipcrm: permission denied for id (1211334727)
% 0.22/0.46  ipcrm: permission denied for id (1211367496)
% 0.22/0.47  ipcrm: permission denied for id (1211465803)
% 0.22/0.47  ipcrm: permission denied for id (1211498572)
% 0.22/0.47  ipcrm: permission denied for id (1211531341)
% 0.22/0.47  ipcrm: permission denied for id (1211564110)
% 0.22/0.47  ipcrm: permission denied for id (1211596879)
% 0.22/0.47  ipcrm: permission denied for id (1211629648)
% 0.22/0.48  ipcrm: permission denied for id (1211662417)
% 0.22/0.48  ipcrm: permission denied for id (1211695187)
% 0.22/0.48  ipcrm: permission denied for id (1211727956)
% 0.22/0.48  ipcrm: permission denied for id (1211760726)
% 0.22/0.49  ipcrm: permission denied for id (1211826264)
% 0.22/0.49  ipcrm: permission denied for id (1211859034)
% 0.22/0.49  ipcrm: permission denied for id (1211891804)
% 0.22/0.50  ipcrm: permission denied for id (1211957342)
% 0.22/0.51  ipcrm: permission denied for id (1212088426)
% 0.22/0.52  ipcrm: permission denied for id (1212121195)
% 0.22/0.52  ipcrm: permission denied for id (1212153964)
% 0.22/0.52  ipcrm: permission denied for id (1212219503)
% 0.22/0.53  ipcrm: permission denied for id (1212317810)
% 0.22/0.53  ipcrm: permission denied for id (1212350579)
% 0.22/0.53  ipcrm: permission denied for id (1212416118)
% 0.22/0.53  ipcrm: permission denied for id (1212448887)
% 0.22/0.54  ipcrm: permission denied for id (1212514426)
% 0.22/0.54  ipcrm: permission denied for id (1212547195)
% 0.22/0.54  ipcrm: permission denied for id (1212612734)
% 1.00/0.67  % (7605)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.19/0.68  % (7611)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 1.19/0.68  % (7603)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 1.19/0.69  % (7602)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.19/0.69  % (7603)Refutation found. Thanks to Tanya!
% 1.19/0.69  % SZS status Theorem for theBenchmark
% 1.19/0.69  % (7613)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.19/0.70  % (7610)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.19/0.70  % SZS output start Proof for theBenchmark
% 1.19/0.70  fof(f231,plain,(
% 1.19/0.70    $false),
% 1.19/0.70    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f94,f98,f102,f108,f116,f122,f125,f135,f143,f200,f208,f209,f230])).
% 1.19/0.70  fof(f230,plain,(
% 1.19/0.70    ~spl9_3 | ~spl9_11 | ~spl9_16),
% 1.19/0.70    inference(avatar_split_clause,[],[f227,f141,f114,f80])).
% 1.19/0.70  fof(f80,plain,(
% 1.19/0.70    spl9_3 <=> r2_hidden(sK5,sK2)),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.19/0.70  fof(f114,plain,(
% 1.19/0.70    spl9_11 <=> ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(k4_tarski(X0,sK4),sK3))),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 1.19/0.70  fof(f141,plain,(
% 1.19/0.70    spl9_16 <=> r2_hidden(k4_tarski(sK5,sK4),sK3)),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_16])])).
% 1.19/0.70  fof(f227,plain,(
% 1.19/0.70    ~r2_hidden(sK5,sK2) | (~spl9_11 | ~spl9_16)),
% 1.19/0.70    inference(resolution,[],[f142,f115])).
% 1.19/0.70  fof(f115,plain,(
% 1.19/0.70    ( ! [X0] : (~r2_hidden(k4_tarski(X0,sK4),sK3) | ~r2_hidden(X0,sK2)) ) | ~spl9_11),
% 1.19/0.70    inference(avatar_component_clause,[],[f114])).
% 1.19/0.70  fof(f142,plain,(
% 1.19/0.70    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~spl9_16),
% 1.19/0.70    inference(avatar_component_clause,[],[f141])).
% 1.19/0.70  fof(f209,plain,(
% 1.19/0.70    sK0 != k1_relat_1(sK3) | r2_hidden(sK5,k1_relat_1(sK3)) | ~r2_hidden(sK5,sK0)),
% 1.19/0.70    introduced(theory_tautology_sat_conflict,[])).
% 1.19/0.70  fof(f208,plain,(
% 1.19/0.70    ~spl9_6 | spl9_24 | ~spl9_23),
% 1.19/0.70    inference(avatar_split_clause,[],[f202,f196,f205,f92])).
% 1.19/0.70  fof(f92,plain,(
% 1.19/0.70    spl9_6 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 1.19/0.70  fof(f205,plain,(
% 1.19/0.70    spl9_24 <=> sK0 = k1_relat_1(sK3)),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 1.19/0.70  fof(f196,plain,(
% 1.19/0.70    spl9_23 <=> sK0 = k1_relset_1(sK0,sK1,sK3)),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 1.19/0.70  fof(f202,plain,(
% 1.19/0.70    sK0 = k1_relat_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_23),
% 1.19/0.70    inference(superposition,[],[f52,f197])).
% 1.19/0.70  fof(f197,plain,(
% 1.19/0.70    sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl9_23),
% 1.19/0.70    inference(avatar_component_clause,[],[f196])).
% 1.19/0.70  fof(f52,plain,(
% 1.19/0.70    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.19/0.70    inference(cnf_transformation,[],[f16])).
% 1.19/0.70  fof(f16,plain,(
% 1.19/0.70    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.70    inference(ennf_transformation,[],[f5])).
% 1.19/0.70  fof(f5,axiom,(
% 1.19/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.19/0.70  fof(f200,plain,(
% 1.19/0.70    spl9_23 | spl9_5 | ~spl9_7 | ~spl9_6),
% 1.19/0.70    inference(avatar_split_clause,[],[f194,f92,f96,f88,f196])).
% 1.19/0.70  fof(f88,plain,(
% 1.19/0.70    spl9_5 <=> k1_xboole_0 = sK1),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.19/0.70  fof(f96,plain,(
% 1.19/0.70    spl9_7 <=> v1_funct_2(sK3,sK0,sK1)),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 1.19/0.70  fof(f194,plain,(
% 1.19/0.70    ~v1_funct_2(sK3,sK0,sK1) | k1_xboole_0 = sK1 | sK0 = k1_relset_1(sK0,sK1,sK3) | ~spl9_6),
% 1.19/0.70    inference(resolution,[],[f53,f93])).
% 1.19/0.70  fof(f93,plain,(
% 1.19/0.70    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl9_6),
% 1.19/0.70    inference(avatar_component_clause,[],[f92])).
% 1.19/0.70  fof(f53,plain,(
% 1.19/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 1.19/0.70    inference(cnf_transformation,[],[f31])).
% 1.19/0.70  fof(f31,plain,(
% 1.19/0.70    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.70    inference(nnf_transformation,[],[f18])).
% 1.19/0.70  fof(f18,plain,(
% 1.19/0.70    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.70    inference(flattening,[],[f17])).
% 1.19/0.70  fof(f17,plain,(
% 1.19/0.70    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.70    inference(ennf_transformation,[],[f7])).
% 1.19/0.70  fof(f7,axiom,(
% 1.19/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.19/0.70  fof(f143,plain,(
% 1.19/0.70    ~spl9_15 | spl9_16 | ~spl9_2 | ~spl9_14),
% 1.19/0.70    inference(avatar_split_clause,[],[f136,f133,f76,f141,f138])).
% 1.19/0.70  fof(f138,plain,(
% 1.19/0.70    spl9_15 <=> r2_hidden(sK5,k1_relat_1(sK3))),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 1.19/0.70  fof(f76,plain,(
% 1.19/0.70    spl9_2 <=> sK4 = k1_funct_1(sK3,sK5)),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.19/0.70  fof(f133,plain,(
% 1.19/0.70    spl9_14 <=> ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3))),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_14])])).
% 1.19/0.70  fof(f136,plain,(
% 1.19/0.70    r2_hidden(k4_tarski(sK5,sK4),sK3) | ~r2_hidden(sK5,k1_relat_1(sK3)) | (~spl9_2 | ~spl9_14)),
% 1.19/0.70    inference(superposition,[],[f134,f77])).
% 1.19/0.70  fof(f77,plain,(
% 1.19/0.70    sK4 = k1_funct_1(sK3,sK5) | ~spl9_2),
% 1.19/0.70    inference(avatar_component_clause,[],[f76])).
% 1.19/0.70  fof(f134,plain,(
% 1.19/0.70    ( ! [X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~r2_hidden(X0,k1_relat_1(sK3))) ) | ~spl9_14),
% 1.19/0.70    inference(avatar_component_clause,[],[f133])).
% 1.19/0.70  fof(f135,plain,(
% 1.19/0.70    ~spl9_10 | spl9_14 | ~spl9_8),
% 1.19/0.70    inference(avatar_split_clause,[],[f131,f100,f133,f111])).
% 1.19/0.70  fof(f111,plain,(
% 1.19/0.70    spl9_10 <=> v1_relat_1(sK3)),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_10])])).
% 1.19/0.70  fof(f100,plain,(
% 1.19/0.70    spl9_8 <=> v1_funct_1(sK3)),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 1.19/0.70  fof(f131,plain,(
% 1.19/0.70    ( ! [X0] : (~r2_hidden(X0,k1_relat_1(sK3)) | r2_hidden(k4_tarski(X0,k1_funct_1(sK3,X0)),sK3) | ~v1_relat_1(sK3)) ) | ~spl9_8),
% 1.19/0.70    inference(resolution,[],[f65,f101])).
% 1.19/0.70  fof(f101,plain,(
% 1.19/0.70    v1_funct_1(sK3) | ~spl9_8),
% 1.19/0.70    inference(avatar_component_clause,[],[f100])).
% 1.19/0.70  fof(f65,plain,(
% 1.19/0.70    ( ! [X0,X1] : (~v1_funct_1(X0) | ~r2_hidden(X1,k1_relat_1(X0)) | r2_hidden(k4_tarski(X1,k1_funct_1(X0,X1)),X0) | ~v1_relat_1(X0)) )),
% 1.19/0.70    inference(equality_resolution,[],[f47])).
% 1.19/0.70  fof(f47,plain,(
% 1.19/0.70    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2 | ~r2_hidden(X1,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.19/0.70    inference(cnf_transformation,[],[f30])).
% 1.19/0.70  fof(f30,plain,(
% 1.19/0.70    ! [X0] : (! [X1,X2] : ((((k1_funct_1(X0,X1) = X2 | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | k1_funct_1(X0,X1) != X2)) | r2_hidden(X1,k1_relat_1(X0))) & (((k1_funct_1(X0,X1) = X2 | ~r2_hidden(k4_tarski(X1,X2),X0)) & (r2_hidden(k4_tarski(X1,X2),X0) | k1_funct_1(X0,X1) != X2)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.19/0.70    inference(nnf_transformation,[],[f15])).
% 1.19/0.70  fof(f15,plain,(
% 1.19/0.70    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.19/0.70    inference(flattening,[],[f14])).
% 1.19/0.70  fof(f14,plain,(
% 1.19/0.70    ! [X0] : (! [X1,X2] : (((k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2) | r2_hidden(X1,k1_relat_1(X0))) & ((k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.19/0.70    inference(ennf_transformation,[],[f4])).
% 1.19/0.70  fof(f4,axiom,(
% 1.19/0.70    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : ((~r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> k1_xboole_0 = X2)) & (r2_hidden(X1,k1_relat_1(X0)) => (k1_funct_1(X0,X1) = X2 <=> r2_hidden(k4_tarski(X1,X2),X0)))))),
% 1.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_funct_1)).
% 1.19/0.70  fof(f125,plain,(
% 1.19/0.70    spl9_12),
% 1.19/0.70    inference(avatar_contradiction_clause,[],[f123])).
% 1.19/0.70  fof(f123,plain,(
% 1.19/0.70    $false | spl9_12),
% 1.19/0.70    inference(resolution,[],[f121,f51])).
% 1.19/0.70  fof(f51,plain,(
% 1.19/0.70    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.19/0.70    inference(cnf_transformation,[],[f3])).
% 1.19/0.70  fof(f3,axiom,(
% 1.19/0.70    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.19/0.70  fof(f121,plain,(
% 1.19/0.70    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | spl9_12),
% 1.19/0.70    inference(avatar_component_clause,[],[f120])).
% 1.19/0.70  fof(f120,plain,(
% 1.19/0.70    spl9_12 <=> v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_12])])).
% 1.19/0.70  fof(f122,plain,(
% 1.19/0.70    ~spl9_12 | ~spl9_6 | spl9_10),
% 1.19/0.70    inference(avatar_split_clause,[],[f118,f111,f92,f120])).
% 1.19/0.70  fof(f118,plain,(
% 1.19/0.70    ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | (~spl9_6 | spl9_10)),
% 1.19/0.70    inference(resolution,[],[f117,f93])).
% 1.19/0.70  fof(f117,plain,(
% 1.19/0.70    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl9_10),
% 1.19/0.70    inference(resolution,[],[f112,f40])).
% 1.19/0.70  fof(f40,plain,(
% 1.19/0.70    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.19/0.70    inference(cnf_transformation,[],[f12])).
% 1.19/0.70  fof(f12,plain,(
% 1.19/0.70    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.19/0.70    inference(ennf_transformation,[],[f1])).
% 1.19/0.70  fof(f1,axiom,(
% 1.19/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.19/0.70  fof(f112,plain,(
% 1.19/0.70    ~v1_relat_1(sK3) | spl9_10),
% 1.19/0.70    inference(avatar_component_clause,[],[f111])).
% 1.19/0.70  fof(f116,plain,(
% 1.19/0.70    ~spl9_10 | spl9_11 | spl9_9),
% 1.19/0.70    inference(avatar_split_clause,[],[f109,f106,f114,f111])).
% 1.19/0.70  fof(f106,plain,(
% 1.19/0.70    spl9_9 <=> r2_hidden(sK4,k9_relat_1(sK3,sK2))),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_9])])).
% 1.19/0.70  fof(f109,plain,(
% 1.19/0.70    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r2_hidden(k4_tarski(X0,sK4),sK3) | ~v1_relat_1(sK3)) ) | spl9_9),
% 1.19/0.70    inference(resolution,[],[f60,f107])).
% 1.19/0.70  fof(f107,plain,(
% 1.19/0.70    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | spl9_9),
% 1.19/0.70    inference(avatar_component_clause,[],[f106])).
% 1.19/0.70  fof(f60,plain,(
% 1.19/0.70    ( ! [X6,X0,X7,X1] : (r2_hidden(X6,k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | ~v1_relat_1(X0)) )),
% 1.19/0.70    inference(equality_resolution,[],[f43])).
% 1.19/0.70  fof(f43,plain,(
% 1.19/0.70    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | ~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0) | k9_relat_1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.19/0.70    inference(cnf_transformation,[],[f29])).
% 1.19/0.70  fof(f29,plain,(
% 1.19/0.70    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & ((r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0)) | r2_hidden(sK6(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & ((r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.19/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8])],[f25,f28,f27,f26])).
% 1.19/0.70  fof(f26,plain,(
% 1.19/0.70    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2))) => ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,sK6(X0,X1,X2)),X0)) | ~r2_hidden(sK6(X0,X1,X2),X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0)) | r2_hidden(sK6(X0,X1,X2),X2))))),
% 1.19/0.70    introduced(choice_axiom,[])).
% 1.19/0.70  fof(f27,plain,(
% 1.19/0.70    ! [X2,X1,X0] : (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,sK6(X0,X1,X2)),X0)) => (r2_hidden(sK7(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK7(X0,X1,X2),sK6(X0,X1,X2)),X0)))),
% 1.19/0.70    introduced(choice_axiom,[])).
% 1.19/0.70  fof(f28,plain,(
% 1.19/0.70    ! [X6,X1,X0] : (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) => (r2_hidden(sK8(X0,X1,X6),X1) & r2_hidden(k4_tarski(sK8(X0,X1,X6),X6),X0)))),
% 1.19/0.70    introduced(choice_axiom,[])).
% 1.19/0.70  fof(f25,plain,(
% 1.19/0.70    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X3),X0)) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (~r2_hidden(X7,X1) | ~r2_hidden(k4_tarski(X7,X6),X0))) & (? [X8] : (r2_hidden(X8,X1) & r2_hidden(k4_tarski(X8,X6),X0)) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.19/0.70    inference(rectify,[],[f24])).
% 1.19/0.70  fof(f24,plain,(
% 1.19/0.70    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2)) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (~r2_hidden(X4,X1) | ~r2_hidden(k4_tarski(X4,X3),X0))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.19/0.70    inference(nnf_transformation,[],[f13])).
% 1.19/0.70  fof(f13,plain,(
% 1.19/0.70    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))) | ~v1_relat_1(X0))),
% 1.19/0.70    inference(ennf_transformation,[],[f2])).
% 1.19/0.70  fof(f2,axiom,(
% 1.19/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X3),X0)))))),
% 1.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_relat_1)).
% 1.19/0.70  fof(f108,plain,(
% 1.19/0.70    ~spl9_9 | spl9_1 | ~spl9_6),
% 1.19/0.70    inference(avatar_split_clause,[],[f104,f92,f72,f106])).
% 1.19/0.70  fof(f72,plain,(
% 1.19/0.70    spl9_1 <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.19/0.70  fof(f104,plain,(
% 1.19/0.70    ~r2_hidden(sK4,k9_relat_1(sK3,sK2)) | (spl9_1 | ~spl9_6)),
% 1.19/0.70    inference(superposition,[],[f73,f103])).
% 1.19/0.70  fof(f103,plain,(
% 1.19/0.70    ( ! [X0] : (k7_relset_1(sK0,sK1,sK3,X0) = k9_relat_1(sK3,X0)) ) | ~spl9_6),
% 1.19/0.70    inference(resolution,[],[f59,f93])).
% 1.19/0.70  fof(f59,plain,(
% 1.19/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)) )),
% 1.19/0.70    inference(cnf_transformation,[],[f19])).
% 1.19/0.70  fof(f19,plain,(
% 1.19/0.70    ! [X0,X1,X2,X3] : (k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.19/0.70    inference(ennf_transformation,[],[f6])).
% 1.19/0.70  fof(f6,axiom,(
% 1.19/0.70    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3))),
% 1.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).
% 1.19/0.70  fof(f73,plain,(
% 1.19/0.70    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) | spl9_1),
% 1.19/0.70    inference(avatar_component_clause,[],[f72])).
% 1.19/0.70  fof(f102,plain,(
% 1.19/0.70    spl9_8),
% 1.19/0.70    inference(avatar_split_clause,[],[f32,f100])).
% 1.19/0.70  fof(f32,plain,(
% 1.19/0.70    v1_funct_1(sK3)),
% 1.19/0.70    inference(cnf_transformation,[],[f23])).
% 1.19/0.70  fof(f23,plain,(
% 1.19/0.70    (~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) & (sK4 = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK5,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 1.19/0.70    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f11,f22,f21,f20])).
% 1.19/0.70  fof(f20,plain,(
% 1.19/0.70    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (~r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) & ? [X5] : (k1_funct_1(sK3,X5) = X4 & r2_hidden(X5,sK2) & r2_hidden(X5,sK0))) & k1_xboole_0 != sK1 & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 1.19/0.70    introduced(choice_axiom,[])).
% 1.19/0.70  fof(f21,plain,(
% 1.19/0.70    ? [X4] : (~r2_hidden(X4,k7_relset_1(sK0,sK1,sK3,sK2)) & ? [X5] : (k1_funct_1(sK3,X5) = X4 & r2_hidden(X5,sK2) & r2_hidden(X5,sK0))) => (~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) & ? [X5] : (k1_funct_1(sK3,X5) = sK4 & r2_hidden(X5,sK2) & r2_hidden(X5,sK0)))),
% 1.19/0.70    introduced(choice_axiom,[])).
% 1.19/0.70  fof(f22,plain,(
% 1.19/0.70    ? [X5] : (k1_funct_1(sK3,X5) = sK4 & r2_hidden(X5,sK2) & r2_hidden(X5,sK0)) => (sK4 = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK5,sK0))),
% 1.19/0.70    introduced(choice_axiom,[])).
% 1.19/0.70  fof(f11,plain,(
% 1.19/0.70    ? [X0,X1,X2,X3] : (? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.19/0.70    inference(flattening,[],[f10])).
% 1.19/0.70  fof(f10,plain,(
% 1.19/0.70    ? [X0,X1,X2,X3] : ((? [X4] : (~r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) & ? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0))) & k1_xboole_0 != X1) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.19/0.70    inference(ennf_transformation,[],[f9])).
% 1.19/0.70  fof(f9,negated_conjecture,(
% 1.19/0.70    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 1.19/0.70    inference(negated_conjecture,[],[f8])).
% 1.19/0.70  fof(f8,conjecture,(
% 1.19/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (k1_xboole_0 != X1 => ! [X4] : (? [X5] : (k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) => r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)))))),
% 1.19/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_2)).
% 1.19/0.70  fof(f98,plain,(
% 1.19/0.70    spl9_7),
% 1.19/0.70    inference(avatar_split_clause,[],[f33,f96])).
% 1.19/0.70  fof(f33,plain,(
% 1.19/0.70    v1_funct_2(sK3,sK0,sK1)),
% 1.19/0.70    inference(cnf_transformation,[],[f23])).
% 1.19/0.70  fof(f94,plain,(
% 1.19/0.70    spl9_6),
% 1.19/0.70    inference(avatar_split_clause,[],[f34,f92])).
% 1.19/0.70  fof(f34,plain,(
% 1.19/0.70    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.19/0.70    inference(cnf_transformation,[],[f23])).
% 1.19/0.70  fof(f90,plain,(
% 1.19/0.70    ~spl9_5),
% 1.19/0.70    inference(avatar_split_clause,[],[f35,f88])).
% 1.19/0.70  fof(f35,plain,(
% 1.19/0.70    k1_xboole_0 != sK1),
% 1.19/0.70    inference(cnf_transformation,[],[f23])).
% 1.19/0.70  fof(f86,plain,(
% 1.19/0.70    spl9_4),
% 1.19/0.70    inference(avatar_split_clause,[],[f36,f84])).
% 1.19/0.70  fof(f84,plain,(
% 1.19/0.70    spl9_4 <=> r2_hidden(sK5,sK0)),
% 1.19/0.70    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 1.19/0.70  fof(f36,plain,(
% 1.19/0.70    r2_hidden(sK5,sK0)),
% 1.19/0.70    inference(cnf_transformation,[],[f23])).
% 1.19/0.70  fof(f82,plain,(
% 1.19/0.70    spl9_3),
% 1.19/0.70    inference(avatar_split_clause,[],[f37,f80])).
% 1.19/0.70  fof(f37,plain,(
% 1.19/0.70    r2_hidden(sK5,sK2)),
% 1.19/0.70    inference(cnf_transformation,[],[f23])).
% 1.19/0.70  fof(f78,plain,(
% 1.19/0.70    spl9_2),
% 1.19/0.70    inference(avatar_split_clause,[],[f38,f76])).
% 1.19/0.70  fof(f38,plain,(
% 1.19/0.70    sK4 = k1_funct_1(sK3,sK5)),
% 1.19/0.70    inference(cnf_transformation,[],[f23])).
% 1.19/0.70  fof(f74,plain,(
% 1.19/0.70    ~spl9_1),
% 1.19/0.70    inference(avatar_split_clause,[],[f39,f72])).
% 1.19/0.70  fof(f39,plain,(
% 1.19/0.70    ~r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))),
% 1.19/0.70    inference(cnf_transformation,[],[f23])).
% 1.19/0.70  % SZS output end Proof for theBenchmark
% 1.19/0.70  % (7603)------------------------------
% 1.19/0.70  % (7603)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.19/0.70  % (7603)Termination reason: Refutation
% 1.19/0.70  
% 1.19/0.70  % (7603)Memory used [KB]: 10746
% 1.19/0.70  % (7603)Time elapsed: 0.068 s
% 1.19/0.70  % (7603)------------------------------
% 1.19/0.70  % (7603)------------------------------
% 1.19/0.71  % (7427)Success in time 0.334 s
%------------------------------------------------------------------------------
