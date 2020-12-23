%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0995+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:01 EST 2020

% Result     : Theorem 8.09s
% Output     : Refutation 8.09s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 180 expanded)
%              Number of leaves         :   29 (  80 expanded)
%              Depth                    :   10
%              Number of atoms          :  382 ( 924 expanded)
%              Number of equality atoms :   82 ( 212 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20257,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f4542,f4547,f4552,f4557,f4562,f4567,f4572,f4577,f6655,f6689,f6839,f6867,f6873,f6926,f20249])).

fof(f20249,plain,
    ( ~ spl333_3
    | ~ spl333_9
    | ~ spl333_178
    | spl333_207 ),
    inference(avatar_contradiction_clause,[],[f20248])).

fof(f20248,plain,
    ( $false
    | ~ spl333_3
    | ~ spl333_9
    | ~ spl333_178
    | spl333_207 ),
    inference(subsumption_resolution,[],[f19926,f6686])).

fof(f6686,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl333_178 ),
    inference(avatar_component_clause,[],[f6684])).

fof(f6684,plain,
    ( spl333_178
  <=> r2_hidden(k4_tarski(sK5,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl333_178])])).

fof(f19926,plain,
    ( ~ r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ spl333_3
    | ~ spl333_9
    | spl333_207 ),
    inference(unit_resulting_resolution,[],[f4595,f4551,f6838,f4127])).

fof(f4127,plain,(
    ! [X6,X0,X7,X1] :
      ( r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f3174])).

fof(f3174,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(k4_tarski(X7,X6),X0)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f2427])).

fof(f2427,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(k4_tarski(X4,sK58(X0,X1,X2)),X0) )
                | ~ r2_hidden(sK58(X0,X1,X2),X2) )
              & ( ( r2_hidden(sK59(X0,X1,X2),X1)
                  & r2_hidden(k4_tarski(sK59(X0,X1,X2),sK58(X0,X1,X2)),X0) )
                | r2_hidden(sK58(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(k4_tarski(X7,X6),X0) ) )
                & ( ( r2_hidden(sK60(X0,X1,X6),X1)
                    & r2_hidden(k4_tarski(sK60(X0,X1,X6),X6),X0) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK58,sK59,sK60])],[f2423,f2426,f2425,f2424])).

fof(f2424,plain,(
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
              | ~ r2_hidden(k4_tarski(X4,sK58(X0,X1,X2)),X0) )
          | ~ r2_hidden(sK58(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( r2_hidden(X5,X1)
              & r2_hidden(k4_tarski(X5,sK58(X0,X1,X2)),X0) )
          | r2_hidden(sK58(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f2425,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( r2_hidden(X5,X1)
          & r2_hidden(k4_tarski(X5,sK58(X0,X1,X2)),X0) )
     => ( r2_hidden(sK59(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK59(X0,X1,X2),sK58(X0,X1,X2)),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2426,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( r2_hidden(X8,X1)
          & r2_hidden(k4_tarski(X8,X6),X0) )
     => ( r2_hidden(sK60(X0,X1,X6),X1)
        & r2_hidden(k4_tarski(sK60(X0,X1,X6),X6),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f2423,plain,(
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
    inference(rectify,[],[f2422])).

fof(f2422,plain,(
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
    inference(nnf_transformation,[],[f1703])).

fof(f1703,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( r2_hidden(X4,X1)
                  & r2_hidden(k4_tarski(X4,X3),X0) ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f647])).

fof(f647,axiom,(
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

fof(f6838,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl333_207 ),
    inference(avatar_component_clause,[],[f6836])).

fof(f6836,plain,
    ( spl333_207
  <=> r2_hidden(sK4,k9_relat_1(sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl333_207])])).

fof(f4551,plain,
    ( r2_hidden(sK5,sK2)
    | ~ spl333_3 ),
    inference(avatar_component_clause,[],[f4549])).

fof(f4549,plain,
    ( spl333_3
  <=> r2_hidden(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl333_3])])).

fof(f4595,plain,
    ( v1_relat_1(sK3)
    | ~ spl333_9 ),
    inference(avatar_component_clause,[],[f4594])).

fof(f4594,plain,
    ( spl333_9
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl333_9])])).

fof(f6926,plain,
    ( k1_relat_1(sK3) != k1_relset_1(sK0,sK1,sK3)
    | sK0 != k1_relset_1(sK0,sK1,sK3)
    | r2_hidden(sK5,k1_relat_1(sK3))
    | ~ r2_hidden(sK5,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f6873,plain,
    ( spl333_200
    | ~ spl333_6 ),
    inference(avatar_split_clause,[],[f6513,f4564,f6797])).

fof(f6797,plain,
    ( spl333_200
  <=> k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl333_200])])).

fof(f4564,plain,
    ( spl333_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl333_6])])).

fof(f6513,plain,
    ( k1_relat_1(sK3) = k1_relset_1(sK0,sK1,sK3)
    | ~ spl333_6 ),
    inference(unit_resulting_resolution,[],[f4566,f3199])).

fof(f3199,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f1718])).

fof(f1718,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f4566,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl333_6 ),
    inference(avatar_component_clause,[],[f4564])).

fof(f6867,plain,
    ( spl333_192
    | spl333_5
    | ~ spl333_6
    | ~ spl333_7 ),
    inference(avatar_split_clause,[],[f6511,f4569,f4564,f4559,f6759])).

fof(f6759,plain,
    ( spl333_192
  <=> sK0 = k1_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl333_192])])).

fof(f4559,plain,
    ( spl333_5
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl333_5])])).

fof(f4569,plain,
    ( spl333_7
  <=> v1_funct_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl333_7])])).

fof(f6511,plain,
    ( sK0 = k1_relset_1(sK0,sK1,sK3)
    | spl333_5
    | ~ spl333_6
    | ~ spl333_7 ),
    inference(unit_resulting_resolution,[],[f4561,f4571,f4566,f3192])).

fof(f3192,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f2433])).

fof(f2433,plain,(
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
    inference(nnf_transformation,[],[f1716])).

fof(f1716,plain,(
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
    inference(flattening,[],[f1715])).

fof(f1715,plain,(
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
    inference(ennf_transformation,[],[f1472])).

fof(f1472,axiom,(
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

fof(f4571,plain,
    ( v1_funct_2(sK3,sK0,sK1)
    | ~ spl333_7 ),
    inference(avatar_component_clause,[],[f4569])).

fof(f4561,plain,
    ( k1_xboole_0 != sK1
    | spl333_5 ),
    inference(avatar_component_clause,[],[f4559])).

fof(f6839,plain,
    ( ~ spl333_207
    | spl333_1
    | ~ spl333_6 ),
    inference(avatar_split_clause,[],[f6834,f4564,f4539,f6836])).

fof(f4539,plain,
    ( spl333_1
  <=> r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl333_1])])).

fof(f6834,plain,
    ( ~ r2_hidden(sK4,k9_relat_1(sK3,sK2))
    | spl333_1
    | ~ spl333_6 ),
    inference(backward_demodulation,[],[f4541,f6576])).

fof(f6576,plain,
    ( ! [X0] : k9_relat_1(sK3,X0) = k7_relset_1(sK0,sK1,sK3,X0)
    | ~ spl333_6 ),
    inference(resolution,[],[f4566,f2764])).

fof(f2764,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f1541])).

fof(f1541,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1233])).

fof(f1233,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f4541,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    | spl333_1 ),
    inference(avatar_component_clause,[],[f4539])).

fof(f6689,plain,
    ( ~ spl333_9
    | ~ spl333_175
    | spl333_178
    | ~ spl333_2
    | ~ spl333_8 ),
    inference(avatar_split_clause,[],[f6688,f4574,f4544,f6684,f6669,f4594])).

fof(f6669,plain,
    ( spl333_175
  <=> r2_hidden(sK5,k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl333_175])])).

fof(f4544,plain,
    ( spl333_2
  <=> sK4 = k1_funct_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl333_2])])).

fof(f4574,plain,
    ( spl333_8
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl333_8])])).

fof(f6688,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl333_2
    | ~ spl333_8 ),
    inference(subsumption_resolution,[],[f6466,f4576])).

fof(f4576,plain,
    ( v1_funct_1(sK3)
    | ~ spl333_8 ),
    inference(avatar_component_clause,[],[f4574])).

fof(f6466,plain,
    ( r2_hidden(k4_tarski(sK5,sK4),sK3)
    | ~ r2_hidden(sK5,k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl333_2 ),
    inference(superposition,[],[f4096,f4546])).

fof(f4546,plain,
    ( sK4 = k1_funct_1(sK3,sK5)
    | ~ spl333_2 ),
    inference(avatar_component_clause,[],[f4544])).

fof(f4096,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f2776])).

fof(f2776,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f2313])).

fof(f2313,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f2312])).

fof(f2312,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f1547])).

fof(f1547,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f1546])).

fof(f1546,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1050])).

fof(f1050,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_1)).

fof(f6655,plain,
    ( spl333_9
    | ~ spl333_6 ),
    inference(avatar_split_clause,[],[f6535,f4564,f4594])).

fof(f6535,plain,
    ( v1_relat_1(sK3)
    | ~ spl333_6 ),
    inference(unit_resulting_resolution,[],[f3101,f4566,f3069])).

fof(f3069,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1626])).

fof(f1626,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f3101,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f696])).

fof(f696,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f4577,plain,(
    spl333_8 ),
    inference(avatar_split_clause,[],[f2756,f4574])).

fof(f2756,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f2307])).

fof(f2307,plain,
    ( ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2))
    & sK4 = k1_funct_1(sK3,sK5)
    & r2_hidden(sK5,sK2)
    & r2_hidden(sK5,sK0)
    & k1_xboole_0 != sK1
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f1540,f2306,f2305,f2304])).

fof(f2304,plain,
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

fof(f2305,plain,
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

fof(f2306,plain,
    ( ? [X5] :
        ( k1_funct_1(sK3,X5) = sK4
        & r2_hidden(X5,sK2)
        & r2_hidden(X5,sK0) )
   => ( sK4 = k1_funct_1(sK3,sK5)
      & r2_hidden(sK5,sK2)
      & r2_hidden(sK5,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f1540,plain,(
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
    inference(flattening,[],[f1539])).

fof(f1539,plain,(
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
    inference(ennf_transformation,[],[f1521])).

fof(f1521,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1520])).

fof(f1520,conjecture,(
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

fof(f4572,plain,(
    spl333_7 ),
    inference(avatar_split_clause,[],[f2757,f4569])).

fof(f2757,plain,(
    v1_funct_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f2307])).

fof(f4567,plain,(
    spl333_6 ),
    inference(avatar_split_clause,[],[f2758,f4564])).

fof(f2758,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f2307])).

fof(f4562,plain,(
    ~ spl333_5 ),
    inference(avatar_split_clause,[],[f2759,f4559])).

fof(f2759,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f2307])).

fof(f4557,plain,(
    spl333_4 ),
    inference(avatar_split_clause,[],[f2760,f4554])).

fof(f4554,plain,
    ( spl333_4
  <=> r2_hidden(sK5,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl333_4])])).

fof(f2760,plain,(
    r2_hidden(sK5,sK0) ),
    inference(cnf_transformation,[],[f2307])).

fof(f4552,plain,(
    spl333_3 ),
    inference(avatar_split_clause,[],[f2761,f4549])).

fof(f2761,plain,(
    r2_hidden(sK5,sK2) ),
    inference(cnf_transformation,[],[f2307])).

fof(f4547,plain,(
    spl333_2 ),
    inference(avatar_split_clause,[],[f2762,f4544])).

fof(f2762,plain,(
    sK4 = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f2307])).

fof(f4542,plain,(
    ~ spl333_1 ),
    inference(avatar_split_clause,[],[f2763,f4539])).

fof(f2763,plain,(
    ~ r2_hidden(sK4,k7_relset_1(sK0,sK1,sK3,sK2)) ),
    inference(cnf_transformation,[],[f2307])).
%------------------------------------------------------------------------------
