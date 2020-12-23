%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:27 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  313 (1394 expanded)
%              Number of leaves         :   46 ( 453 expanded)
%              Depth                    :   18
%              Number of atoms          : 1250 (16347 expanded)
%              Number of equality atoms :  245 (6421 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2985,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f884,f892,f1046,f1056,f1238,f1448,f1453,f1499,f1526,f1937,f1940,f1960,f1966,f2604,f2609,f2875,f2888,f2905,f2984])).

fof(f2984,plain,(
    ~ spl15_45 ),
    inference(avatar_contradiction_clause,[],[f2983])).

fof(f2983,plain,
    ( $false
    | ~ spl15_45 ),
    inference(subsumption_resolution,[],[f2982,f88])).

fof(f88,plain,(
    k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( k2_funct_1(sK10) != sK11
    & k1_xboole_0 != sK9
    & k1_xboole_0 != sK8
    & ! [X4,X5] :
        ( ( ( k1_funct_1(sK11,X4) = X5
            & r2_hidden(X4,sK9) )
          | k1_funct_1(sK10,X5) != X4
          | ~ r2_hidden(X5,sK8) )
        & ( ( k1_funct_1(sK10,X5) = X4
            & r2_hidden(X5,sK8) )
          | k1_funct_1(sK11,X4) != X5
          | ~ r2_hidden(X4,sK9) ) )
    & v2_funct_1(sK10)
    & sK9 = k2_relset_1(sK8,sK9,sK10)
    & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8)))
    & v1_funct_2(sK11,sK9,sK8)
    & v1_funct_1(sK11)
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
    & v1_funct_2(sK10,sK8,sK9)
    & v1_funct_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f19,f54,f53])).

fof(f53,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( k2_funct_1(X2) != X3
            & k1_xboole_0 != X1
            & k1_xboole_0 != X0
            & ! [X4,X5] :
                ( ( ( k1_funct_1(X3,X4) = X5
                    & r2_hidden(X4,X1) )
                  | k1_funct_1(X2,X5) != X4
                  | ~ r2_hidden(X5,X0) )
                & ( ( k1_funct_1(X2,X5) = X4
                    & r2_hidden(X5,X0) )
                  | k1_funct_1(X3,X4) != X5
                  | ~ r2_hidden(X4,X1) ) )
            & v2_funct_1(X2)
            & k2_relset_1(X0,X1,X2) = X1
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK10) != X3
          & k1_xboole_0 != sK9
          & k1_xboole_0 != sK8
          & ! [X5,X4] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,sK9) )
                | k1_funct_1(sK10,X5) != X4
                | ~ r2_hidden(X5,sK8) )
              & ( ( k1_funct_1(sK10,X5) = X4
                  & r2_hidden(X5,sK8) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,sK9) ) )
          & v2_funct_1(sK10)
          & sK9 = k2_relset_1(sK8,sK9,sK10)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8)))
          & v1_funct_2(X3,sK9,sK8)
          & v1_funct_1(X3) )
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))
      & v1_funct_2(sK10,sK8,sK9)
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ? [X3] :
        ( k2_funct_1(sK10) != X3
        & k1_xboole_0 != sK9
        & k1_xboole_0 != sK8
        & ! [X5,X4] :
            ( ( ( k1_funct_1(X3,X4) = X5
                & r2_hidden(X4,sK9) )
              | k1_funct_1(sK10,X5) != X4
              | ~ r2_hidden(X5,sK8) )
            & ( ( k1_funct_1(sK10,X5) = X4
                & r2_hidden(X5,sK8) )
              | k1_funct_1(X3,X4) != X5
              | ~ r2_hidden(X4,sK9) ) )
        & v2_funct_1(sK10)
        & sK9 = k2_relset_1(sK8,sK9,sK10)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8)))
        & v1_funct_2(X3,sK9,sK8)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK10) != sK11
      & k1_xboole_0 != sK9
      & k1_xboole_0 != sK8
      & ! [X5,X4] :
          ( ( ( k1_funct_1(sK11,X4) = X5
              & r2_hidden(X4,sK9) )
            | k1_funct_1(sK10,X5) != X4
            | ~ r2_hidden(X5,sK8) )
          & ( ( k1_funct_1(sK10,X5) = X4
              & r2_hidden(X5,sK8) )
            | k1_funct_1(sK11,X4) != X5
            | ~ r2_hidden(X4,sK9) ) )
      & v2_funct_1(sK10)
      & sK9 = k2_relset_1(sK8,sK9,sK10)
      & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8)))
      & v1_funct_2(sK11,sK9,sK8)
      & v1_funct_1(sK11) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & ! [X4,X5] :
              ( ( ( k1_funct_1(X3,X4) = X5
                  & r2_hidden(X4,X1) )
                | k1_funct_1(X2,X5) != X4
                | ~ r2_hidden(X5,X0) )
              & ( ( k1_funct_1(X2,X5) = X4
                  & r2_hidden(X5,X0) )
                | k1_funct_1(X3,X4) != X5
                | ~ r2_hidden(X4,X1) ) )
          & v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( ! [X4,X5] :
                    ( ( ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) )
                     => ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) ) )
                    & ( ( k1_funct_1(X3,X4) = X5
                        & r2_hidden(X4,X1) )
                     => ( k1_funct_1(X2,X5) = X4
                        & r2_hidden(X5,X0) ) ) )
                & v2_funct_1(X2)
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( ! [X4,X5] :
                  ( ( ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) )
                   => ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) ) )
                  & ( ( k1_funct_1(X3,X4) = X5
                      & r2_hidden(X4,X1) )
                   => ( k1_funct_1(X2,X5) = X4
                      & r2_hidden(X5,X0) ) ) )
              & v2_funct_1(X2)
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_2)).

fof(f2982,plain,
    ( k1_xboole_0 = sK9
    | ~ spl15_45 ),
    inference(resolution,[],[f1045,f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( ~ sP3(X0,X1)
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP3(X0,X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ sP3(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f1045,plain,
    ( sP3(sK8,sK9)
    | ~ spl15_45 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f1043,plain,
    ( spl15_45
  <=> sP3(sK8,sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_45])])).

fof(f2905,plain,
    ( ~ spl15_92
    | ~ spl15_96
    | ~ spl15_98 ),
    inference(avatar_contradiction_clause,[],[f2904])).

fof(f2904,plain,
    ( $false
    | ~ spl15_92
    | ~ spl15_96
    | ~ spl15_98 ),
    inference(subsumption_resolution,[],[f2903,f2553])).

fof(f2553,plain,
    ( sP2(sK10,sK11)
    | ~ spl15_92 ),
    inference(avatar_component_clause,[],[f2551])).

fof(f2551,plain,
    ( spl15_92
  <=> sP2(sK10,sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_92])])).

fof(f2903,plain,
    ( ~ sP2(sK10,sK11)
    | ~ spl15_96
    | ~ spl15_98 ),
    inference(subsumption_resolution,[],[f2902,f2590])).

fof(f2590,plain,
    ( sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11))
    | ~ spl15_96 ),
    inference(avatar_component_clause,[],[f2588])).

fof(f2588,plain,
    ( spl15_96
  <=> sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_96])])).

fof(f2902,plain,
    ( sK13(sK10,sK11) != k1_funct_1(sK10,sK12(sK10,sK11))
    | ~ sP2(sK10,sK11)
    | ~ spl15_98 ),
    inference(resolution,[],[f2883,f101])).

fof(f101,plain,(
    ! [X0,X1] :
      ( sP1(sK12(X0,X1),sK13(X0,X1),X1,X0)
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( sP1(sK12(X0,X1),sK13(X0,X1),X1,X0)
        & r2_hidden(sK13(X0,X1),k1_relat_1(X1))
        & r2_hidden(sK12(X0,X1),k1_relat_1(X0)) )
      | ~ sP2(X0,X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f57,f58])).

fof(f58,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( sP1(X2,X3,X1,X0)
          & r2_hidden(X3,k1_relat_1(X1))
          & r2_hidden(X2,k1_relat_1(X0)) )
     => ( sP1(sK12(X0,X1),sK13(X0,X1),X1,X0)
        & r2_hidden(sK13(X0,X1),k1_relat_1(X1))
        & r2_hidden(sK12(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( sP1(X2,X3,X1,X0)
          & r2_hidden(X3,k1_relat_1(X1))
          & r2_hidden(X2,k1_relat_1(X0)) )
      | ~ sP2(X0,X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( sP1(X2,X3,X1,X0)
          & r2_hidden(X3,k1_relat_1(X1))
          & r2_hidden(X2,k1_relat_1(X0)) )
      | ~ sP2(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f2883,plain,
    ( ! [X1] :
        ( ~ sP1(sK12(sK10,sK11),sK13(sK10,sK11),sK11,X1)
        | sK13(sK10,sK11) != k1_funct_1(X1,sK12(sK10,sK11)) )
    | ~ spl15_98 ),
    inference(superposition,[],[f136,f2608])).

fof(f2608,plain,
    ( sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11))
    | ~ spl15_98 ),
    inference(avatar_component_clause,[],[f2606])).

fof(f2606,plain,
    ( spl15_98
  <=> sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_98])])).

fof(f136,plain,(
    ! [X2,X3,X1] :
      ( ~ sP1(k1_funct_1(X2,X1),X1,X2,X3)
      | k1_funct_1(X3,k1_funct_1(X2,X1)) != X1 ) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(X2,X1) != X0
      | k1_funct_1(X3,X0) != X1
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( k1_funct_1(X2,X1) != X0
          | k1_funct_1(X3,X0) != X1 )
        & ( k1_funct_1(X2,X1) = X0
          | k1_funct_1(X3,X0) = X1 ) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f60])).

fof(f60,plain,(
    ! [X2,X3,X1,X0] :
      ( ( ( k1_funct_1(X1,X3) != X2
          | k1_funct_1(X0,X2) != X3 )
        & ( k1_funct_1(X1,X3) = X2
          | k1_funct_1(X0,X2) = X3 ) )
      | ~ sP1(X2,X3,X1,X0) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X2,X3,X1,X0] :
      ( ( k1_funct_1(X0,X2) = X3
      <~> k1_funct_1(X1,X3) = X2 )
      | ~ sP1(X2,X3,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f2888,plain,
    ( spl15_96
    | ~ spl15_94
    | ~ spl15_98 ),
    inference(avatar_split_clause,[],[f2887,f2606,f2580,f2588])).

fof(f2580,plain,
    ( spl15_94
  <=> r2_hidden(sK13(sK10,sK11),sK9) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_94])])).

fof(f2887,plain,
    ( sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11))
    | ~ spl15_94
    | ~ spl15_98 ),
    inference(subsumption_resolution,[],[f2881,f2581])).

fof(f2581,plain,
    ( r2_hidden(sK13(sK10,sK11),sK9)
    | ~ spl15_94 ),
    inference(avatar_component_clause,[],[f2580])).

fof(f2881,plain,
    ( sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11))
    | ~ r2_hidden(sK13(sK10,sK11),sK9)
    | ~ spl15_98 ),
    inference(superposition,[],[f134,f2608])).

fof(f134,plain,(
    ! [X4] :
      ( k1_funct_1(sK10,k1_funct_1(sK11,X4)) = X4
      | ~ r2_hidden(X4,sK9) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK10,X5) = X4
      | k1_funct_1(sK11,X4) != X5
      | ~ r2_hidden(X4,sK9) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2875,plain,
    ( spl15_92
    | ~ spl15_16
    | ~ spl15_44
    | ~ spl15_46 ),
    inference(avatar_split_clause,[],[f2874,f1049,f1039,f350,f2551])).

fof(f350,plain,
    ( spl15_16
  <=> sK8 = k2_relat_1(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).

fof(f1039,plain,
    ( spl15_44
  <=> sK8 = k1_relat_1(sK10) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_44])])).

fof(f1049,plain,
    ( spl15_46
  <=> sK9 = k1_relat_1(sK11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_46])])).

fof(f2874,plain,
    ( sP2(sK10,sK11)
    | ~ spl15_16
    | ~ spl15_44
    | ~ spl15_46 ),
    inference(subsumption_resolution,[],[f2873,f154])).

fof(f154,plain,(
    v1_relat_1(sK10) ),
    inference(subsumption_resolution,[],[f151,f105])).

fof(f105,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f151,plain,
    ( v1_relat_1(sK10)
    | ~ v1_relat_1(k2_zfmisc_1(sK8,sK9)) ),
    inference(resolution,[],[f90,f77])).

fof(f77,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
    inference(cnf_transformation,[],[f55])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f2873,plain,
    ( sP2(sK10,sK11)
    | ~ v1_relat_1(sK10)
    | ~ spl15_16
    | ~ spl15_44
    | ~ spl15_46 ),
    inference(subsumption_resolution,[],[f2872,f75])).

fof(f75,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f55])).

fof(f2872,plain,
    ( sP2(sK10,sK11)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | ~ spl15_16
    | ~ spl15_44
    | ~ spl15_46 ),
    inference(subsumption_resolution,[],[f2871,f82])).

fof(f82,plain,(
    v2_funct_1(sK10) ),
    inference(cnf_transformation,[],[f55])).

fof(f2871,plain,
    ( sP2(sK10,sK11)
    | ~ v2_funct_1(sK10)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | ~ spl15_16
    | ~ spl15_44
    | ~ spl15_46 ),
    inference(subsumption_resolution,[],[f2823,f234])).

fof(f234,plain,(
    sK9 = k2_relat_1(sK10) ),
    inference(subsumption_resolution,[],[f232,f77])).

fof(f232,plain,
    ( sK9 = k2_relat_1(sK10)
    | ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) ),
    inference(superposition,[],[f113,f81])).

fof(f81,plain,(
    sK9 = k2_relset_1(sK8,sK9,sK10) ),
    inference(cnf_transformation,[],[f55])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f2823,plain,
    ( sP2(sK10,sK11)
    | sK9 != k2_relat_1(sK10)
    | ~ v2_funct_1(sK10)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | ~ spl15_16
    | ~ spl15_44
    | ~ spl15_46 ),
    inference(subsumption_resolution,[],[f2821,f1041])).

fof(f1041,plain,
    ( sK8 = k1_relat_1(sK10)
    | ~ spl15_44 ),
    inference(avatar_component_clause,[],[f1039])).

fof(f2821,plain,
    ( sK8 != k1_relat_1(sK10)
    | sP2(sK10,sK11)
    | sK9 != k2_relat_1(sK10)
    | ~ v2_funct_1(sK10)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | ~ spl15_16
    | ~ spl15_46 ),
    inference(trivial_inequality_removal,[],[f2739])).

fof(f2739,plain,
    ( sK11 != sK11
    | sK8 != k1_relat_1(sK10)
    | sP2(sK10,sK11)
    | sK9 != k2_relat_1(sK10)
    | ~ v2_funct_1(sK10)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | ~ spl15_16
    | ~ spl15_46 ),
    inference(superposition,[],[f89,f2017])).

fof(f2017,plain,
    ( ! [X0] :
        ( k2_funct_1(X0) = sK11
        | k1_relat_1(X0) != sK8
        | sP2(X0,sK11)
        | k2_relat_1(X0) != sK9
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl15_16
    | ~ spl15_46 ),
    inference(forward_demodulation,[],[f2016,f1051])).

fof(f1051,plain,
    ( sK9 = k1_relat_1(sK11)
    | ~ spl15_46 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f2016,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK8
        | sP2(X0,sK11)
        | k2_relat_1(X0) != k1_relat_1(sK11)
        | k2_funct_1(X0) = sK11
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl15_16 ),
    inference(subsumption_resolution,[],[f2015,f155])).

fof(f155,plain,(
    v1_relat_1(sK11) ),
    inference(subsumption_resolution,[],[f152,f105])).

fof(f152,plain,
    ( v1_relat_1(sK11)
    | ~ v1_relat_1(k2_zfmisc_1(sK9,sK8)) ),
    inference(resolution,[],[f90,f80])).

fof(f80,plain,(
    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8))) ),
    inference(cnf_transformation,[],[f55])).

fof(f2015,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK8
        | sP2(X0,sK11)
        | k2_relat_1(X0) != k1_relat_1(sK11)
        | k2_funct_1(X0) = sK11
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(sK11)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl15_16 ),
    inference(subsumption_resolution,[],[f1989,f78])).

fof(f78,plain,(
    v1_funct_1(sK11) ),
    inference(cnf_transformation,[],[f55])).

fof(f1989,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) != sK8
        | sP2(X0,sK11)
        | k2_relat_1(X0) != k1_relat_1(sK11)
        | k2_funct_1(X0) = sK11
        | ~ v2_funct_1(X0)
        | ~ v1_funct_1(sK11)
        | ~ v1_relat_1(sK11)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl15_16 ),
    inference(superposition,[],[f104,f352])).

fof(f352,plain,
    ( sK8 = k2_relat_1(sK11)
    | ~ spl15_16 ),
    inference(avatar_component_clause,[],[f350])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X1) != k1_relat_1(X0)
      | sP2(X0,X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | k2_funct_1(X0) = X1
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | sP2(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f28,f43,f42])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | ? [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <~> k1_funct_1(X1,X3) = X2 )
              & r2_hidden(X3,k1_relat_1(X1))
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k2_relat_1(X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | ? [X2,X3] :
              ( ( k1_funct_1(X0,X2) = X3
              <~> k1_funct_1(X1,X3) = X2 )
              & r2_hidden(X3,k1_relat_1(X1))
              & r2_hidden(X2,k1_relat_1(X0)) )
          | k1_relat_1(X1) != k2_relat_1(X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( ! [X2,X3] :
                  ( ( r2_hidden(X3,k1_relat_1(X1))
                    & r2_hidden(X2,k1_relat_1(X0)) )
                 => ( k1_funct_1(X0,X2) = X3
                  <=> k1_funct_1(X1,X3) = X2 ) )
              & k1_relat_1(X1) = k2_relat_1(X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).

fof(f89,plain,(
    k2_funct_1(sK10) != sK11 ),
    inference(cnf_transformation,[],[f55])).

fof(f2609,plain,
    ( ~ spl15_92
    | spl15_98
    | ~ spl15_44 ),
    inference(avatar_split_clause,[],[f2568,f1039,f2606,f2551])).

fof(f2568,plain,
    ( sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11))
    | ~ sP2(sK10,sK11)
    | ~ spl15_44 ),
    inference(trivial_inequality_removal,[],[f2567])).

fof(f2567,plain,
    ( sK12(sK10,sK11) != sK12(sK10,sK11)
    | sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11))
    | ~ sP2(sK10,sK11)
    | ~ spl15_44 ),
    inference(equality_factoring,[],[f1733])).

fof(f1733,plain,
    ( ! [X2] :
        ( sK12(sK10,X2) = k1_funct_1(sK11,sK13(sK10,X2))
        | sK12(sK10,X2) = k1_funct_1(X2,sK13(sK10,X2))
        | ~ sP2(sK10,X2) )
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f1723,f1087])).

fof(f1087,plain,
    ( ! [X0] :
        ( r2_hidden(sK12(sK10,X0),sK8)
        | ~ sP2(sK10,X0) )
    | ~ spl15_44 ),
    inference(superposition,[],[f99,f1041])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK12(X0,X1),k1_relat_1(X0))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f1723,plain,(
    ! [X2] :
      ( sK12(sK10,X2) = k1_funct_1(sK11,sK13(sK10,X2))
      | ~ r2_hidden(sK12(sK10,X2),sK8)
      | sK12(sK10,X2) = k1_funct_1(X2,sK13(sK10,X2))
      | ~ sP2(sK10,X2) ) ),
    inference(superposition,[],[f132,f388])).

fof(f388,plain,(
    ! [X0,X1] :
      ( sK13(X0,X1) = k1_funct_1(X0,sK12(X0,X1))
      | sK12(X0,X1) = k1_funct_1(X1,sK13(X0,X1))
      | ~ sP2(X0,X1) ) ),
    inference(resolution,[],[f102,f101])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | k1_funct_1(X3,X0) = X1
      | k1_funct_1(X2,X1) = X0 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f132,plain,(
    ! [X5] :
      ( k1_funct_1(sK11,k1_funct_1(sK10,X5)) = X5
      | ~ r2_hidden(X5,sK8) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X5] :
      ( k1_funct_1(sK11,X4) = X5
      | k1_funct_1(sK10,X5) != X4
      | ~ r2_hidden(X5,sK8) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f2604,plain,
    ( ~ spl15_46
    | ~ spl15_92
    | spl15_94 ),
    inference(avatar_contradiction_clause,[],[f2603])).

fof(f2603,plain,
    ( $false
    | ~ spl15_46
    | ~ spl15_92
    | spl15_94 ),
    inference(subsumption_resolution,[],[f2602,f2553])).

fof(f2602,plain,
    ( ~ sP2(sK10,sK11)
    | ~ spl15_46
    | spl15_94 ),
    inference(resolution,[],[f2582,f1270])).

fof(f1270,plain,
    ( ! [X1] :
        ( r2_hidden(sK13(X1,sK11),sK9)
        | ~ sP2(X1,sK11) )
    | ~ spl15_46 ),
    inference(superposition,[],[f100,f1051])).

fof(f100,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK13(X0,X1),k1_relat_1(X1))
      | ~ sP2(X0,X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f2582,plain,
    ( ~ r2_hidden(sK13(sK10,sK11),sK9)
    | spl15_94 ),
    inference(avatar_component_clause,[],[f2580])).

fof(f1966,plain,
    ( spl15_16
    | ~ spl15_15 ),
    inference(avatar_split_clause,[],[f1965,f346,f350])).

fof(f346,plain,
    ( spl15_15
  <=> r1_tarski(sK8,k2_relat_1(sK11)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).

fof(f1965,plain,
    ( sK8 = k2_relat_1(sK11)
    | ~ spl15_15 ),
    inference(subsumption_resolution,[],[f1963,f331])).

fof(f331,plain,(
    r1_tarski(k2_relat_1(sK11),sK8) ),
    inference(resolution,[],[f325,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f325,plain,(
    m1_subset_1(k2_relat_1(sK11),k1_zfmisc_1(sK8)) ),
    inference(resolution,[],[f282,f80])).

fof(f282,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) ) ),
    inference(duplicate_literal_removal,[],[f281])).

fof(f281,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(superposition,[],[f114,f113])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

fof(f1963,plain,
    ( sK8 = k2_relat_1(sK11)
    | ~ r1_tarski(k2_relat_1(sK11),sK8)
    | ~ spl15_15 ),
    inference(resolution,[],[f347,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f347,plain,
    ( r1_tarski(sK8,k2_relat_1(sK11))
    | ~ spl15_15 ),
    inference(avatar_component_clause,[],[f346])).

fof(f1960,plain,
    ( spl15_15
    | ~ spl15_67
    | ~ spl15_77 ),
    inference(avatar_split_clause,[],[f1957,f1934,f1478,f346])).

fof(f1478,plain,
    ( spl15_67
  <=> sK8 = k2_relat_1(k2_funct_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_67])])).

fof(f1934,plain,
    ( spl15_77
  <=> sP6(k2_relat_1(sK11),sK9,k2_funct_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_77])])).

fof(f1957,plain,
    ( r1_tarski(sK8,k2_relat_1(sK11))
    | ~ spl15_67
    | ~ spl15_77 ),
    inference(forward_demodulation,[],[f1956,f1480])).

fof(f1480,plain,
    ( sK8 = k2_relat_1(k2_funct_1(sK10))
    | ~ spl15_67 ),
    inference(avatar_component_clause,[],[f1478])).

fof(f1956,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK10)),k2_relat_1(sK11))
    | ~ spl15_77 ),
    inference(resolution,[],[f1936,f361])).

fof(f361,plain,(
    ! [X4,X5,X3] :
      ( ~ sP6(X3,X4,X5)
      | r1_tarski(k2_relat_1(X5),X3) ) ),
    inference(resolution,[],[f321,f110])).

fof(f321,plain,(
    ! [X2,X3,X1] :
      ( m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2))
      | ~ sP6(X2,X3,X1) ) ),
    inference(resolution,[],[f282,f125])).

fof(f125,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP6(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(X2,X1,X0)
        & v1_funct_1(X2) )
      | ~ sP6(X0,X1,X2) ) ),
    inference(rectify,[],[f70])).

fof(f70,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP6(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X1,X0,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ sP6(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).

fof(f1936,plain,
    ( sP6(k2_relat_1(sK11),sK9,k2_funct_1(sK10))
    | ~ spl15_77 ),
    inference(avatar_component_clause,[],[f1934])).

fof(f1940,plain,
    ( spl15_77
    | ~ spl15_42
    | ~ spl15_43
    | ~ spl15_44
    | spl15_47
    | ~ spl15_67
    | spl15_76 ),
    inference(avatar_split_clause,[],[f1939,f1930,f1478,f1053,f1039,f881,f859,f1934])).

fof(f859,plain,
    ( spl15_42
  <=> sP0(k2_funct_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_42])])).

fof(f881,plain,
    ( spl15_43
  <=> v1_funct_2(k2_funct_1(sK10),sK9,k2_relat_1(k2_funct_1(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_43])])).

fof(f1053,plain,
    ( spl15_47
  <=> sP3(sK9,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_47])])).

fof(f1930,plain,
    ( spl15_76
  <=> r2_hidden(k1_funct_1(k2_funct_1(sK10),sK14(sK9,k2_relat_1(sK11),k2_funct_1(sK10))),sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_76])])).

fof(f1939,plain,
    ( sP6(k2_relat_1(sK11),sK9,k2_funct_1(sK10))
    | ~ spl15_42
    | ~ spl15_43
    | ~ spl15_44
    | spl15_47
    | ~ spl15_67
    | spl15_76 ),
    inference(resolution,[],[f1938,f1863])).

fof(f1863,plain,(
    ! [X3] :
      ( r2_hidden(sK14(sK9,X3,k2_funct_1(sK10)),sK9)
      | sP6(X3,sK9,k2_funct_1(sK10)) ) ),
    inference(subsumption_resolution,[],[f1862,f154])).

fof(f1862,plain,(
    ! [X3] :
      ( r2_hidden(sK14(sK9,X3,k2_funct_1(sK10)),sK9)
      | sP6(X3,sK9,k2_funct_1(sK10))
      | ~ v1_relat_1(sK10) ) ),
    inference(subsumption_resolution,[],[f1861,f75])).

fof(f1861,plain,(
    ! [X3] :
      ( r2_hidden(sK14(sK9,X3,k2_funct_1(sK10)),sK9)
      | sP6(X3,sK9,k2_funct_1(sK10))
      | ~ v1_funct_1(sK10)
      | ~ v1_relat_1(sK10) ) ),
    inference(subsumption_resolution,[],[f1858,f82])).

fof(f1858,plain,(
    ! [X3] :
      ( r2_hidden(sK14(sK9,X3,k2_funct_1(sK10)),sK9)
      | sP6(X3,sK9,k2_funct_1(sK10))
      | ~ v2_funct_1(sK10)
      | ~ v1_funct_1(sK10)
      | ~ v1_relat_1(sK10) ) ),
    inference(superposition,[],[f463,f234])).

fof(f463,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK14(k2_relat_1(X0),X1,k2_funct_1(X0)),k2_relat_1(X0))
      | sP6(X1,k2_relat_1(X0),k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f462,f95])).

fof(f95,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f462,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK14(k2_relat_1(X0),X1,k2_funct_1(X0)),k2_relat_1(X0))
      | sP6(X1,k2_relat_1(X0),k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f461,f96])).

fof(f96,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f461,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK14(k2_relat_1(X0),X1,k2_funct_1(X0)),k2_relat_1(X0))
      | sP6(X1,k2_relat_1(X0),k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f144,f97])).

fof(f97,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f144,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK14(k1_relat_1(X2),X1,X2),k1_relat_1(X2))
      | sP6(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( sP6(X1,X0,X2)
      | r2_hidden(sK14(X0,X1,X2),X0)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( sP6(X1,X0,X2)
      | ( ~ r2_hidden(k1_funct_1(X2,sK14(X0,X1,X2)),X1)
        & r2_hidden(sK14(X0,X1,X2),X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f50,f72])).

fof(f72,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
     => ( ~ r2_hidden(k1_funct_1(X2,sK14(X0,X1,X2)),X1)
        & r2_hidden(sK14(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( sP6(X1,X0,X2)
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(definition_folding,[],[f37,f49])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ? [X3] :
          ( ~ r2_hidden(k1_funct_1(X2,X3),X1)
          & r2_hidden(X3,X0) )
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( ( ! [X3] :
              ( r2_hidden(X3,X0)
             => r2_hidden(k1_funct_1(X2,X3),X1) )
          & k1_relat_1(X2) = X0 )
       => ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).

fof(f1938,plain,
    ( ~ r2_hidden(sK14(sK9,k2_relat_1(sK11),k2_funct_1(sK10)),sK9)
    | ~ spl15_42
    | ~ spl15_43
    | ~ spl15_44
    | spl15_47
    | ~ spl15_67
    | spl15_76 ),
    inference(resolution,[],[f1932,f1774])).

fof(f1774,plain,
    ( ! [X2] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK10),X2),sK8)
        | ~ r2_hidden(X2,sK9) )
    | ~ spl15_42
    | ~ spl15_43
    | ~ spl15_44
    | spl15_47
    | ~ spl15_67 ),
    inference(backward_demodulation,[],[f1436,f1659])).

fof(f1659,plain,
    ( sK9 = k1_relat_1(k2_funct_1(sK10))
    | ~ spl15_42
    | ~ spl15_43
    | ~ spl15_44
    | spl15_47
    | ~ spl15_67 ),
    inference(subsumption_resolution,[],[f1658,f1054])).

fof(f1054,plain,
    ( ~ sP3(sK9,sK8)
    | spl15_47 ),
    inference(avatar_component_clause,[],[f1053])).

fof(f1658,plain,
    ( sP3(sK9,sK8)
    | sK9 = k1_relat_1(k2_funct_1(sK10))
    | ~ spl15_42
    | ~ spl15_43
    | ~ spl15_44
    | ~ spl15_67 ),
    inference(subsumption_resolution,[],[f1653,f1081])).

fof(f1081,plain,
    ( v1_funct_2(k2_funct_1(sK10),sK9,sK8)
    | ~ spl15_43
    | ~ spl15_44 ),
    inference(backward_demodulation,[],[f900,f1041])).

fof(f900,plain,
    ( v1_funct_2(k2_funct_1(sK10),sK9,k1_relat_1(sK10))
    | ~ spl15_43 ),
    inference(subsumption_resolution,[],[f899,f154])).

fof(f899,plain,
    ( v1_funct_2(k2_funct_1(sK10),sK9,k1_relat_1(sK10))
    | ~ v1_relat_1(sK10)
    | ~ spl15_43 ),
    inference(subsumption_resolution,[],[f898,f75])).

fof(f898,plain,
    ( v1_funct_2(k2_funct_1(sK10),sK9,k1_relat_1(sK10))
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | ~ spl15_43 ),
    inference(subsumption_resolution,[],[f896,f82])).

fof(f896,plain,
    ( v1_funct_2(k2_funct_1(sK10),sK9,k1_relat_1(sK10))
    | ~ v2_funct_1(sK10)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | ~ spl15_43 ),
    inference(superposition,[],[f883,f98])).

fof(f98,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f883,plain,
    ( v1_funct_2(k2_funct_1(sK10),sK9,k2_relat_1(k2_funct_1(sK10)))
    | ~ spl15_43 ),
    inference(avatar_component_clause,[],[f881])).

fof(f1653,plain,
    ( ~ v1_funct_2(k2_funct_1(sK10),sK9,sK8)
    | sP3(sK9,sK8)
    | sK9 = k1_relat_1(k2_funct_1(sK10))
    | ~ spl15_42
    | ~ spl15_67 ),
    inference(resolution,[],[f1577,f418])).

fof(f418,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_2(X5,X3,X4)
      | sP3(X3,X4)
      | k1_relat_1(X5) = X3 ) ),
    inference(subsumption_resolution,[],[f416,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | sP4(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( sP5(X2,X1,X0)
        & sP4(X0,X2,X1) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(definition_folding,[],[f35,f47,f46,f45])).

fof(f46,plain,(
    ! [X0,X2,X1] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_relset_1(X0,X1,X2) = X0 )
      | sP3(X0,X1)
      | ~ sP4(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ( v1_funct_2(X2,X0,X1)
      <=> k1_xboole_0 = X2 )
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ sP5(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f416,plain,(
    ! [X4,X5,X3] :
      ( k1_relat_1(X5) = X3
      | ~ v1_funct_2(X5,X3,X4)
      | sP3(X3,X4)
      | ~ sP4(X3,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) ) ),
    inference(superposition,[],[f117,f112])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X2,X1) = X0
      | ~ v1_funct_2(X1,X0,X2)
      | sP3(X0,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( ( ( v1_funct_2(X1,X0,X2)
          | k1_relset_1(X0,X2,X1) != X0 )
        & ( k1_relset_1(X0,X2,X1) = X0
          | ~ v1_funct_2(X1,X0,X2) ) )
      | sP3(X0,X2)
      | ~ sP4(X0,X1,X2) ) ),
    inference(rectify,[],[f67])).

fof(f67,plain,(
    ! [X0,X2,X1] :
      ( ( ( v1_funct_2(X2,X0,X1)
          | k1_relset_1(X0,X1,X2) != X0 )
        & ( k1_relset_1(X0,X1,X2) = X0
          | ~ v1_funct_2(X2,X0,X1) ) )
      | sP3(X0,X1)
      | ~ sP4(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f1577,plain,
    ( m1_subset_1(k2_funct_1(sK10),k1_zfmisc_1(k2_zfmisc_1(sK9,sK8)))
    | ~ spl15_42
    | ~ spl15_67 ),
    inference(forward_demodulation,[],[f1576,f234])).

fof(f1576,plain,
    ( m1_subset_1(k2_funct_1(sK10),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK10),sK8)))
    | ~ spl15_42
    | ~ spl15_67 ),
    inference(subsumption_resolution,[],[f1575,f154])).

fof(f1575,plain,
    ( m1_subset_1(k2_funct_1(sK10),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK10),sK8)))
    | ~ v1_relat_1(sK10)
    | ~ spl15_42
    | ~ spl15_67 ),
    inference(subsumption_resolution,[],[f1574,f75])).

fof(f1574,plain,
    ( m1_subset_1(k2_funct_1(sK10),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK10),sK8)))
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | ~ spl15_42
    | ~ spl15_67 ),
    inference(subsumption_resolution,[],[f1573,f82])).

fof(f1573,plain,
    ( m1_subset_1(k2_funct_1(sK10),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK10),sK8)))
    | ~ v2_funct_1(sK10)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | ~ spl15_42
    | ~ spl15_67 ),
    inference(subsumption_resolution,[],[f1545,f860])).

fof(f860,plain,
    ( sP0(k2_funct_1(sK10))
    | ~ spl15_42 ),
    inference(avatar_component_clause,[],[f859])).

fof(f1545,plain,
    ( m1_subset_1(k2_funct_1(sK10),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK10),sK8)))
    | ~ sP0(k2_funct_1(sK10))
    | ~ v2_funct_1(sK10)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | ~ spl15_67 ),
    inference(superposition,[],[f221,f1480])).

fof(f221,plain,(
    ! [X1] :
      ( m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1)))))
      | ~ sP0(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f93,f97])).

fof(f93,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ sP0(X0) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ sP0(X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1436,plain,
    ( ! [X2] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK10),X2),sK8)
        | ~ r2_hidden(X2,k1_relat_1(k2_funct_1(sK10))) )
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f1435,f154])).

fof(f1435,plain,
    ( ! [X2] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK10),X2),sK8)
        | ~ r2_hidden(X2,k1_relat_1(k2_funct_1(sK10)))
        | ~ v1_relat_1(sK10) )
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f1434,f75])).

fof(f1434,plain,
    ( ! [X2] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK10),X2),sK8)
        | ~ r2_hidden(X2,k1_relat_1(k2_funct_1(sK10)))
        | ~ v1_funct_1(sK10)
        | ~ v1_relat_1(sK10) )
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f1427,f82])).

fof(f1427,plain,
    ( ! [X2] :
        ( r2_hidden(k1_funct_1(k2_funct_1(sK10),X2),sK8)
        | ~ r2_hidden(X2,k1_relat_1(k2_funct_1(sK10)))
        | ~ v2_funct_1(sK10)
        | ~ v1_funct_1(sK10)
        | ~ v1_relat_1(sK10) )
    | ~ spl15_44 ),
    inference(superposition,[],[f313,f1041])).

fof(f313,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(k2_funct_1(X0),X1),k1_relat_1(X0))
      | ~ r2_hidden(X1,k1_relat_1(k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f312,f95])).

fof(f312,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(k2_funct_1(X0),X1),k1_relat_1(X0))
      | ~ r2_hidden(X1,k1_relat_1(k2_funct_1(X0)))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f305,f96])).

fof(f305,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(k2_funct_1(X0),X1),k1_relat_1(X0))
      | ~ r2_hidden(X1,k1_relat_1(k2_funct_1(X0)))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f106,f98])).

fof(f106,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r2_hidden(X0,k1_relat_1(X1))
       => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).

fof(f1932,plain,
    ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK10),sK14(sK9,k2_relat_1(sK11),k2_funct_1(sK10))),sK8)
    | spl15_76 ),
    inference(avatar_component_clause,[],[f1930])).

fof(f1937,plain,
    ( ~ spl15_76
    | spl15_77
    | ~ spl15_46 ),
    inference(avatar_split_clause,[],[f1921,f1049,f1934,f1930])).

fof(f1921,plain,
    ( sP6(k2_relat_1(sK11),sK9,k2_funct_1(sK10))
    | ~ r2_hidden(k1_funct_1(k2_funct_1(sK10),sK14(sK9,k2_relat_1(sK11),k2_funct_1(sK10))),sK8)
    | ~ spl15_46 ),
    inference(resolution,[],[f1902,f1355])).

fof(f1355,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_relat_1(sK11))
        | ~ r2_hidden(X0,sK8) )
    | ~ spl15_46 ),
    inference(subsumption_resolution,[],[f1354,f133])).

fof(f133,plain,(
    ! [X5] :
      ( r2_hidden(k1_funct_1(sK10,X5),sK9)
      | ~ r2_hidden(X5,sK8) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X4,X5] :
      ( r2_hidden(X4,sK9)
      | k1_funct_1(sK10,X5) != X4
      | ~ r2_hidden(X5,sK8) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f1354,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_funct_1(sK10,X0),sK9)
        | r2_hidden(X0,k2_relat_1(sK11))
        | ~ r2_hidden(X0,sK8) )
    | ~ spl15_46 ),
    inference(forward_demodulation,[],[f308,f1051])).

fof(f308,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_funct_1(sK10,X0),k1_relat_1(sK11))
      | r2_hidden(X0,k2_relat_1(sK11))
      | ~ r2_hidden(X0,sK8) ) ),
    inference(subsumption_resolution,[],[f307,f155])).

fof(f307,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK11))
      | ~ r2_hidden(k1_funct_1(sK10,X0),k1_relat_1(sK11))
      | ~ v1_relat_1(sK11)
      | ~ r2_hidden(X0,sK8) ) ),
    inference(subsumption_resolution,[],[f303,f78])).

fof(f303,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_relat_1(sK11))
      | ~ r2_hidden(k1_funct_1(sK10,X0),k1_relat_1(sK11))
      | ~ v1_funct_1(sK11)
      | ~ v1_relat_1(sK11)
      | ~ r2_hidden(X0,sK8) ) ),
    inference(superposition,[],[f106,f132])).

fof(f1902,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK10),sK14(sK9,X3,k2_funct_1(sK10))),X3)
      | sP6(X3,sK9,k2_funct_1(sK10)) ) ),
    inference(subsumption_resolution,[],[f1901,f154])).

fof(f1901,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK10),sK14(sK9,X3,k2_funct_1(sK10))),X3)
      | sP6(X3,sK9,k2_funct_1(sK10))
      | ~ v1_relat_1(sK10) ) ),
    inference(subsumption_resolution,[],[f1900,f75])).

fof(f1900,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK10),sK14(sK9,X3,k2_funct_1(sK10))),X3)
      | sP6(X3,sK9,k2_funct_1(sK10))
      | ~ v1_funct_1(sK10)
      | ~ v1_relat_1(sK10) ) ),
    inference(subsumption_resolution,[],[f1894,f82])).

fof(f1894,plain,(
    ! [X3] :
      ( ~ r2_hidden(k1_funct_1(k2_funct_1(sK10),sK14(sK9,X3,k2_funct_1(sK10))),X3)
      | sP6(X3,sK9,k2_funct_1(sK10))
      | ~ v2_funct_1(sK10)
      | ~ v1_funct_1(sK10)
      | ~ v1_relat_1(sK10) ) ),
    inference(superposition,[],[f563,f234])).

fof(f563,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_funct_1(k2_funct_1(X0),sK14(k2_relat_1(X0),X1,k2_funct_1(X0))),X1)
      | sP6(X1,k2_relat_1(X0),k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f562,f95])).

fof(f562,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_funct_1(k2_funct_1(X0),sK14(k2_relat_1(X0),X1,k2_funct_1(X0))),X1)
      | sP6(X1,k2_relat_1(X0),k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f515,f96])).

fof(f515,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(k1_funct_1(k2_funct_1(X0),sK14(k2_relat_1(X0),X1,k2_funct_1(X0))),X1)
      | sP6(X1,k2_relat_1(X0),k2_funct_1(X0))
      | ~ v1_funct_1(k2_funct_1(X0))
      | ~ v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f143,f97])).

fof(f143,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(k1_funct_1(X2,sK14(k1_relat_1(X2),X1,X2)),X1)
      | sP6(X1,k1_relat_1(X2),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( sP6(X1,X0,X2)
      | ~ r2_hidden(k1_funct_1(X2,sK14(X0,X1,X2)),X1)
      | k1_relat_1(X2) != X0
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f1526,plain,
    ( spl15_67
    | ~ spl15_64
    | ~ spl15_66 ),
    inference(avatar_split_clause,[],[f1525,f1474,f1441,f1478])).

fof(f1441,plain,
    ( spl15_64
  <=> sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_64])])).

fof(f1474,plain,
    ( spl15_66
  <=> r1_tarski(sK8,k2_relat_1(k2_funct_1(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_66])])).

fof(f1525,plain,
    ( sK8 = k2_relat_1(k2_funct_1(sK10))
    | ~ spl15_64
    | ~ spl15_66 ),
    inference(subsumption_resolution,[],[f1522,f1464])).

fof(f1464,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK10)),sK8)
    | ~ spl15_64 ),
    inference(resolution,[],[f1443,f361])).

fof(f1443,plain,
    ( sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10))
    | ~ spl15_64 ),
    inference(avatar_component_clause,[],[f1441])).

fof(f1522,plain,
    ( sK8 = k2_relat_1(k2_funct_1(sK10))
    | ~ r1_tarski(k2_relat_1(k2_funct_1(sK10)),sK8)
    | ~ spl15_66 ),
    inference(resolution,[],[f1475,f109])).

fof(f1475,plain,
    ( r1_tarski(sK8,k2_relat_1(k2_funct_1(sK10)))
    | ~ spl15_66 ),
    inference(avatar_component_clause,[],[f1474])).

fof(f1499,plain,
    ( ~ spl15_44
    | spl15_66 ),
    inference(avatar_contradiction_clause,[],[f1498])).

fof(f1498,plain,
    ( $false
    | ~ spl15_44
    | spl15_66 ),
    inference(subsumption_resolution,[],[f1497,f137])).

fof(f137,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f63])).

fof(f1497,plain,
    ( ~ r1_tarski(sK8,sK8)
    | ~ spl15_44
    | spl15_66 ),
    inference(forward_demodulation,[],[f1496,f1041])).

fof(f1496,plain,
    ( ~ r1_tarski(sK8,k1_relat_1(sK10))
    | spl15_66 ),
    inference(subsumption_resolution,[],[f1495,f154])).

fof(f1495,plain,
    ( ~ r1_tarski(sK8,k1_relat_1(sK10))
    | ~ v1_relat_1(sK10)
    | spl15_66 ),
    inference(subsumption_resolution,[],[f1494,f75])).

fof(f1494,plain,
    ( ~ r1_tarski(sK8,k1_relat_1(sK10))
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | spl15_66 ),
    inference(subsumption_resolution,[],[f1493,f82])).

fof(f1493,plain,
    ( ~ r1_tarski(sK8,k1_relat_1(sK10))
    | ~ v2_funct_1(sK10)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10)
    | spl15_66 ),
    inference(superposition,[],[f1476,f98])).

fof(f1476,plain,
    ( ~ r1_tarski(sK8,k2_relat_1(k2_funct_1(sK10)))
    | spl15_66 ),
    inference(avatar_component_clause,[],[f1474])).

fof(f1453,plain,
    ( spl15_64
    | spl15_65 ),
    inference(avatar_split_clause,[],[f1452,f1445,f1441])).

fof(f1445,plain,
    ( spl15_65
  <=> r2_hidden(sK14(k1_relat_1(k2_funct_1(sK10)),sK8,k2_funct_1(sK10)),k1_relat_1(k2_funct_1(sK10))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl15_65])])).

fof(f1452,plain,
    ( sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10))
    | spl15_65 ),
    inference(subsumption_resolution,[],[f1451,f618])).

fof(f618,plain,(
    v1_relat_1(k2_funct_1(sK10)) ),
    inference(resolution,[],[f601,f215])).

fof(f215,plain,(
    ! [X6,X8,X7] :
      ( ~ sP7(X6,X7,X8)
      | v1_relat_1(k2_funct_1(X8)) ) ),
    inference(subsumption_resolution,[],[f213,f105])).

fof(f213,plain,(
    ! [X6,X8,X7] :
      ( ~ sP7(X6,X7,X8)
      | v1_relat_1(k2_funct_1(X8))
      | ~ v1_relat_1(k2_zfmisc_1(X7,X6)) ) ),
    inference(resolution,[],[f130,f90])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ sP7(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP7(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | ~ sP7(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).

fof(f601,plain,(
    sP7(sK8,sK9,sK10) ),
    inference(subsumption_resolution,[],[f600,f75])).

fof(f600,plain,
    ( sP7(sK8,sK9,sK10)
    | ~ v1_funct_1(sK10) ),
    inference(subsumption_resolution,[],[f599,f76])).

fof(f76,plain,(
    v1_funct_2(sK10,sK8,sK9) ),
    inference(cnf_transformation,[],[f55])).

fof(f599,plain,
    ( sP7(sK8,sK9,sK10)
    | ~ v1_funct_2(sK10,sK8,sK9)
    | ~ v1_funct_1(sK10) ),
    inference(subsumption_resolution,[],[f598,f82])).

fof(f598,plain,
    ( ~ v2_funct_1(sK10)
    | sP7(sK8,sK9,sK10)
    | ~ v1_funct_2(sK10,sK8,sK9)
    | ~ v1_funct_1(sK10) ),
    inference(subsumption_resolution,[],[f584,f81])).

fof(f584,plain,
    ( sK9 != k2_relset_1(sK8,sK9,sK10)
    | ~ v2_funct_1(sK10)
    | sP7(sK8,sK9,sK10)
    | ~ v1_funct_2(sK10,sK8,sK9)
    | ~ v1_funct_1(sK10) ),
    inference(resolution,[],[f131,f77])).

fof(f131,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | sP7(X0,X1,X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( sP7(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f39,f51])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f1451,plain,
    ( sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10))
    | ~ v1_relat_1(k2_funct_1(sK10))
    | spl15_65 ),
    inference(subsumption_resolution,[],[f1449,f619])).

fof(f619,plain,(
    v1_funct_1(k2_funct_1(sK10)) ),
    inference(resolution,[],[f601,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ sP7(X0,X1,X2)
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f1449,plain,
    ( sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10))
    | ~ v1_funct_1(k2_funct_1(sK10))
    | ~ v1_relat_1(k2_funct_1(sK10))
    | spl15_65 ),
    inference(resolution,[],[f1447,f144])).

fof(f1447,plain,
    ( ~ r2_hidden(sK14(k1_relat_1(k2_funct_1(sK10)),sK8,k2_funct_1(sK10)),k1_relat_1(k2_funct_1(sK10)))
    | spl15_65 ),
    inference(avatar_component_clause,[],[f1445])).

fof(f1448,plain,
    ( spl15_64
    | ~ spl15_65
    | ~ spl15_44 ),
    inference(avatar_split_clause,[],[f1439,f1039,f1445,f1441])).

fof(f1439,plain,
    ( ~ r2_hidden(sK14(k1_relat_1(k2_funct_1(sK10)),sK8,k2_funct_1(sK10)),k1_relat_1(k2_funct_1(sK10)))
    | sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10))
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f1438,f618])).

fof(f1438,plain,
    ( ~ r2_hidden(sK14(k1_relat_1(k2_funct_1(sK10)),sK8,k2_funct_1(sK10)),k1_relat_1(k2_funct_1(sK10)))
    | sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10))
    | ~ v1_relat_1(k2_funct_1(sK10))
    | ~ spl15_44 ),
    inference(subsumption_resolution,[],[f1437,f619])).

fof(f1437,plain,
    ( ~ r2_hidden(sK14(k1_relat_1(k2_funct_1(sK10)),sK8,k2_funct_1(sK10)),k1_relat_1(k2_funct_1(sK10)))
    | sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10))
    | ~ v1_funct_1(k2_funct_1(sK10))
    | ~ v1_relat_1(k2_funct_1(sK10))
    | ~ spl15_44 ),
    inference(resolution,[],[f1436,f143])).

fof(f1238,plain,(
    ~ spl15_47 ),
    inference(avatar_contradiction_clause,[],[f1237])).

fof(f1237,plain,
    ( $false
    | ~ spl15_47 ),
    inference(subsumption_resolution,[],[f1236,f87])).

fof(f87,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f55])).

fof(f1236,plain,
    ( k1_xboole_0 = sK8
    | ~ spl15_47 ),
    inference(resolution,[],[f1055,f119])).

fof(f1055,plain,
    ( sP3(sK9,sK8)
    | ~ spl15_47 ),
    inference(avatar_component_clause,[],[f1053])).

fof(f1056,plain,
    ( spl15_46
    | spl15_47 ),
    inference(avatar_split_clause,[],[f1047,f1053,f1049])).

fof(f1047,plain,
    ( sP3(sK9,sK8)
    | sK9 = k1_relat_1(sK11) ),
    inference(subsumption_resolution,[],[f1029,f79])).

fof(f79,plain,(
    v1_funct_2(sK11,sK9,sK8) ),
    inference(cnf_transformation,[],[f55])).

fof(f1029,plain,
    ( ~ v1_funct_2(sK11,sK9,sK8)
    | sP3(sK9,sK8)
    | sK9 = k1_relat_1(sK11) ),
    inference(resolution,[],[f418,f80])).

fof(f1046,plain,
    ( spl15_44
    | spl15_45 ),
    inference(avatar_split_clause,[],[f1037,f1043,f1039])).

fof(f1037,plain,
    ( sP3(sK8,sK9)
    | sK8 = k1_relat_1(sK10) ),
    inference(subsumption_resolution,[],[f1027,f76])).

fof(f1027,plain,
    ( ~ v1_funct_2(sK10,sK8,sK9)
    | sP3(sK8,sK9)
    | sK8 = k1_relat_1(sK10) ),
    inference(resolution,[],[f418,f77])).

fof(f892,plain,(
    spl15_42 ),
    inference(avatar_contradiction_clause,[],[f891])).

fof(f891,plain,
    ( $false
    | spl15_42 ),
    inference(subsumption_resolution,[],[f890,f618])).

fof(f890,plain,
    ( ~ v1_relat_1(k2_funct_1(sK10))
    | spl15_42 ),
    inference(subsumption_resolution,[],[f889,f619])).

fof(f889,plain,
    ( ~ v1_funct_1(k2_funct_1(sK10))
    | ~ v1_relat_1(k2_funct_1(sK10))
    | spl15_42 ),
    inference(resolution,[],[f861,f94])).

fof(f94,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( sP0(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_folding,[],[f22,f40])).

fof(f22,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f861,plain,
    ( ~ sP0(k2_funct_1(sK10))
    | spl15_42 ),
    inference(avatar_component_clause,[],[f859])).

fof(f884,plain,
    ( ~ spl15_42
    | spl15_43 ),
    inference(avatar_split_clause,[],[f879,f881,f859])).

fof(f879,plain,
    ( v1_funct_2(k2_funct_1(sK10),sK9,k2_relat_1(k2_funct_1(sK10)))
    | ~ sP0(k2_funct_1(sK10)) ),
    inference(subsumption_resolution,[],[f878,f154])).

fof(f878,plain,
    ( v1_funct_2(k2_funct_1(sK10),sK9,k2_relat_1(k2_funct_1(sK10)))
    | ~ sP0(k2_funct_1(sK10))
    | ~ v1_relat_1(sK10) ),
    inference(subsumption_resolution,[],[f877,f75])).

fof(f877,plain,
    ( v1_funct_2(k2_funct_1(sK10),sK9,k2_relat_1(k2_funct_1(sK10)))
    | ~ sP0(k2_funct_1(sK10))
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10) ),
    inference(subsumption_resolution,[],[f865,f82])).

fof(f865,plain,
    ( v1_funct_2(k2_funct_1(sK10),sK9,k2_relat_1(k2_funct_1(sK10)))
    | ~ sP0(k2_funct_1(sK10))
    | ~ v2_funct_1(sK10)
    | ~ v1_funct_1(sK10)
    | ~ v1_relat_1(sK10) ),
    inference(superposition,[],[f220,f234])).

fof(f220,plain,(
    ! [X0] :
      ( v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),k2_relat_1(k2_funct_1(X0)))
      | ~ sP0(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f92,f97])).

fof(f92,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ sP0(X0) ) ),
    inference(cnf_transformation,[],[f56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:55:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (8883)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.48  % (8891)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.50  % (8881)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (8898)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.50  % (8879)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (8890)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (8882)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.50  % (8876)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (8896)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (8897)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.51  % (8888)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (8880)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (8889)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (8886)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.51  % (8892)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.52  % (8877)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (8878)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.52  % (8884)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (8895)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (8900)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.53  % (8885)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.53  % (8899)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.55  % (8887)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.55  % (8901)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.55  % (8894)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.56  % (8893)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 2.18/0.66  % (8880)Refutation found. Thanks to Tanya!
% 2.18/0.66  % SZS status Theorem for theBenchmark
% 2.18/0.66  % SZS output start Proof for theBenchmark
% 2.18/0.66  fof(f2985,plain,(
% 2.18/0.66    $false),
% 2.18/0.66    inference(avatar_sat_refutation,[],[f884,f892,f1046,f1056,f1238,f1448,f1453,f1499,f1526,f1937,f1940,f1960,f1966,f2604,f2609,f2875,f2888,f2905,f2984])).
% 2.18/0.66  fof(f2984,plain,(
% 2.18/0.66    ~spl15_45),
% 2.18/0.66    inference(avatar_contradiction_clause,[],[f2983])).
% 2.18/0.66  fof(f2983,plain,(
% 2.18/0.66    $false | ~spl15_45),
% 2.18/0.66    inference(subsumption_resolution,[],[f2982,f88])).
% 2.18/0.66  fof(f88,plain,(
% 2.18/0.66    k1_xboole_0 != sK9),
% 2.18/0.66    inference(cnf_transformation,[],[f55])).
% 2.18/0.66  fof(f55,plain,(
% 2.18/0.66    (k2_funct_1(sK10) != sK11 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & ! [X4,X5] : (((k1_funct_1(sK11,X4) = X5 & r2_hidden(X4,sK9)) | k1_funct_1(sK10,X5) != X4 | ~r2_hidden(X5,sK8)) & ((k1_funct_1(sK10,X5) = X4 & r2_hidden(X5,sK8)) | k1_funct_1(sK11,X4) != X5 | ~r2_hidden(X4,sK9))) & v2_funct_1(sK10) & sK9 = k2_relset_1(sK8,sK9,sK10) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8))) & v1_funct_2(sK11,sK9,sK8) & v1_funct_1(sK11)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_2(sK10,sK8,sK9) & v1_funct_1(sK10)),
% 2.18/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11])],[f19,f54,f53])).
% 2.18/0.66  fof(f53,plain,(
% 2.18/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK10) != X3 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & ! [X5,X4] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,sK9)) | k1_funct_1(sK10,X5) != X4 | ~r2_hidden(X5,sK8)) & ((k1_funct_1(sK10,X5) = X4 & r2_hidden(X5,sK8)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,sK9))) & v2_funct_1(sK10) & sK9 = k2_relset_1(sK8,sK9,sK10) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8))) & v1_funct_2(X3,sK9,sK8) & v1_funct_1(X3)) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9))) & v1_funct_2(sK10,sK8,sK9) & v1_funct_1(sK10))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f54,plain,(
% 2.18/0.66    ? [X3] : (k2_funct_1(sK10) != X3 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & ! [X5,X4] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,sK9)) | k1_funct_1(sK10,X5) != X4 | ~r2_hidden(X5,sK8)) & ((k1_funct_1(sK10,X5) = X4 & r2_hidden(X5,sK8)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,sK9))) & v2_funct_1(sK10) & sK9 = k2_relset_1(sK8,sK9,sK10) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8))) & v1_funct_2(X3,sK9,sK8) & v1_funct_1(X3)) => (k2_funct_1(sK10) != sK11 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & ! [X5,X4] : (((k1_funct_1(sK11,X4) = X5 & r2_hidden(X4,sK9)) | k1_funct_1(sK10,X5) != X4 | ~r2_hidden(X5,sK8)) & ((k1_funct_1(sK10,X5) = X4 & r2_hidden(X5,sK8)) | k1_funct_1(sK11,X4) != X5 | ~r2_hidden(X4,sK9))) & v2_funct_1(sK10) & sK9 = k2_relset_1(sK8,sK9,sK10) & m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8))) & v1_funct_2(sK11,sK9,sK8) & v1_funct_1(sK11))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f19,plain,(
% 2.18/0.66    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0)) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.18/0.66    inference(flattening,[],[f18])).
% 2.18/0.66  fof(f18,plain,(
% 2.18/0.66    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (! [X4,X5] : (((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) | (k1_funct_1(X2,X5) != X4 | ~r2_hidden(X5,X0))) & ((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) | (k1_funct_1(X3,X4) != X5 | ~r2_hidden(X4,X1)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.18/0.66    inference(ennf_transformation,[],[f17])).
% 2.18/0.66  fof(f17,negated_conjecture,(
% 2.18/0.66    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.18/0.66    inference(negated_conjecture,[],[f16])).
% 2.18/0.66  fof(f16,conjecture,(
% 2.18/0.66    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((! [X4,X5] : (((k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)) => (k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1))) & ((k1_funct_1(X3,X4) = X5 & r2_hidden(X4,X1)) => (k1_funct_1(X2,X5) = X4 & r2_hidden(X5,X0)))) & v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.18/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_funct_2)).
% 2.18/0.66  fof(f2982,plain,(
% 2.18/0.66    k1_xboole_0 = sK9 | ~spl15_45),
% 2.18/0.66    inference(resolution,[],[f1045,f119])).
% 2.18/0.66  fof(f119,plain,(
% 2.18/0.66    ( ! [X0,X1] : (~sP3(X0,X1) | k1_xboole_0 = X1) )),
% 2.18/0.66    inference(cnf_transformation,[],[f69])).
% 2.18/0.66  fof(f69,plain,(
% 2.18/0.66    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP3(X0,X1))),
% 2.18/0.66    inference(nnf_transformation,[],[f45])).
% 2.18/0.66  fof(f45,plain,(
% 2.18/0.66    ! [X0,X1] : ((k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~sP3(X0,X1))),
% 2.18/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 2.18/0.66  fof(f1045,plain,(
% 2.18/0.66    sP3(sK8,sK9) | ~spl15_45),
% 2.18/0.66    inference(avatar_component_clause,[],[f1043])).
% 2.18/0.66  fof(f1043,plain,(
% 2.18/0.66    spl15_45 <=> sP3(sK8,sK9)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl15_45])])).
% 2.18/0.66  fof(f2905,plain,(
% 2.18/0.66    ~spl15_92 | ~spl15_96 | ~spl15_98),
% 2.18/0.66    inference(avatar_contradiction_clause,[],[f2904])).
% 2.18/0.66  fof(f2904,plain,(
% 2.18/0.66    $false | (~spl15_92 | ~spl15_96 | ~spl15_98)),
% 2.18/0.66    inference(subsumption_resolution,[],[f2903,f2553])).
% 2.18/0.66  fof(f2553,plain,(
% 2.18/0.66    sP2(sK10,sK11) | ~spl15_92),
% 2.18/0.66    inference(avatar_component_clause,[],[f2551])).
% 2.18/0.66  fof(f2551,plain,(
% 2.18/0.66    spl15_92 <=> sP2(sK10,sK11)),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl15_92])])).
% 2.18/0.66  fof(f2903,plain,(
% 2.18/0.66    ~sP2(sK10,sK11) | (~spl15_96 | ~spl15_98)),
% 2.18/0.66    inference(subsumption_resolution,[],[f2902,f2590])).
% 2.18/0.66  fof(f2590,plain,(
% 2.18/0.66    sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11)) | ~spl15_96),
% 2.18/0.66    inference(avatar_component_clause,[],[f2588])).
% 2.18/0.66  fof(f2588,plain,(
% 2.18/0.66    spl15_96 <=> sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl15_96])])).
% 2.18/0.66  fof(f2902,plain,(
% 2.18/0.66    sK13(sK10,sK11) != k1_funct_1(sK10,sK12(sK10,sK11)) | ~sP2(sK10,sK11) | ~spl15_98),
% 2.18/0.66    inference(resolution,[],[f2883,f101])).
% 2.18/0.66  fof(f101,plain,(
% 2.18/0.66    ( ! [X0,X1] : (sP1(sK12(X0,X1),sK13(X0,X1),X1,X0) | ~sP2(X0,X1)) )),
% 2.18/0.66    inference(cnf_transformation,[],[f59])).
% 2.18/0.66  fof(f59,plain,(
% 2.18/0.66    ! [X0,X1] : ((sP1(sK12(X0,X1),sK13(X0,X1),X1,X0) & r2_hidden(sK13(X0,X1),k1_relat_1(X1)) & r2_hidden(sK12(X0,X1),k1_relat_1(X0))) | ~sP2(X0,X1))),
% 2.18/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK12,sK13])],[f57,f58])).
% 2.18/0.66  fof(f58,plain,(
% 2.18/0.66    ! [X1,X0] : (? [X2,X3] : (sP1(X2,X3,X1,X0) & r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (sP1(sK12(X0,X1),sK13(X0,X1),X1,X0) & r2_hidden(sK13(X0,X1),k1_relat_1(X1)) & r2_hidden(sK12(X0,X1),k1_relat_1(X0))))),
% 2.18/0.66    introduced(choice_axiom,[])).
% 2.18/0.66  fof(f57,plain,(
% 2.18/0.66    ! [X0,X1] : (? [X2,X3] : (sP1(X2,X3,X1,X0) & r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) | ~sP2(X0,X1))),
% 2.18/0.66    inference(nnf_transformation,[],[f43])).
% 2.18/0.66  fof(f43,plain,(
% 2.18/0.66    ! [X0,X1] : (? [X2,X3] : (sP1(X2,X3,X1,X0) & r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) | ~sP2(X0,X1))),
% 2.18/0.66    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 2.18/0.66  fof(f2883,plain,(
% 2.18/0.66    ( ! [X1] : (~sP1(sK12(sK10,sK11),sK13(sK10,sK11),sK11,X1) | sK13(sK10,sK11) != k1_funct_1(X1,sK12(sK10,sK11))) ) | ~spl15_98),
% 2.18/0.66    inference(superposition,[],[f136,f2608])).
% 2.18/0.66  fof(f2608,plain,(
% 2.18/0.66    sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11)) | ~spl15_98),
% 2.18/0.66    inference(avatar_component_clause,[],[f2606])).
% 2.18/0.66  fof(f2606,plain,(
% 2.18/0.66    spl15_98 <=> sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11))),
% 2.18/0.66    introduced(avatar_definition,[new_symbols(naming,[spl15_98])])).
% 2.18/0.68  fof(f136,plain,(
% 2.18/0.68    ( ! [X2,X3,X1] : (~sP1(k1_funct_1(X2,X1),X1,X2,X3) | k1_funct_1(X3,k1_funct_1(X2,X1)) != X1) )),
% 2.18/0.68    inference(equality_resolution,[],[f103])).
% 2.18/0.68  fof(f103,plain,(
% 2.18/0.68    ( ! [X2,X0,X3,X1] : (k1_funct_1(X2,X1) != X0 | k1_funct_1(X3,X0) != X1 | ~sP1(X0,X1,X2,X3)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f61])).
% 2.18/0.68  fof(f61,plain,(
% 2.18/0.68    ! [X0,X1,X2,X3] : (((k1_funct_1(X2,X1) != X0 | k1_funct_1(X3,X0) != X1) & (k1_funct_1(X2,X1) = X0 | k1_funct_1(X3,X0) = X1)) | ~sP1(X0,X1,X2,X3))),
% 2.18/0.68    inference(rectify,[],[f60])).
% 2.18/0.68  fof(f60,plain,(
% 2.18/0.68    ! [X2,X3,X1,X0] : (((k1_funct_1(X1,X3) != X2 | k1_funct_1(X0,X2) != X3) & (k1_funct_1(X1,X3) = X2 | k1_funct_1(X0,X2) = X3)) | ~sP1(X2,X3,X1,X0))),
% 2.18/0.68    inference(nnf_transformation,[],[f42])).
% 2.18/0.68  fof(f42,plain,(
% 2.18/0.68    ! [X2,X3,X1,X0] : ((k1_funct_1(X0,X2) = X3 <~> k1_funct_1(X1,X3) = X2) | ~sP1(X2,X3,X1,X0))),
% 2.18/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.18/0.68  fof(f2888,plain,(
% 2.18/0.68    spl15_96 | ~spl15_94 | ~spl15_98),
% 2.18/0.68    inference(avatar_split_clause,[],[f2887,f2606,f2580,f2588])).
% 2.18/0.68  fof(f2580,plain,(
% 2.18/0.68    spl15_94 <=> r2_hidden(sK13(sK10,sK11),sK9)),
% 2.18/0.68    introduced(avatar_definition,[new_symbols(naming,[spl15_94])])).
% 2.18/0.68  fof(f2887,plain,(
% 2.18/0.68    sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11)) | (~spl15_94 | ~spl15_98)),
% 2.18/0.68    inference(subsumption_resolution,[],[f2881,f2581])).
% 2.18/0.68  fof(f2581,plain,(
% 2.18/0.68    r2_hidden(sK13(sK10,sK11),sK9) | ~spl15_94),
% 2.18/0.68    inference(avatar_component_clause,[],[f2580])).
% 2.18/0.68  fof(f2881,plain,(
% 2.18/0.68    sK13(sK10,sK11) = k1_funct_1(sK10,sK12(sK10,sK11)) | ~r2_hidden(sK13(sK10,sK11),sK9) | ~spl15_98),
% 2.18/0.68    inference(superposition,[],[f134,f2608])).
% 2.18/0.68  fof(f134,plain,(
% 2.18/0.68    ( ! [X4] : (k1_funct_1(sK10,k1_funct_1(sK11,X4)) = X4 | ~r2_hidden(X4,sK9)) )),
% 2.18/0.68    inference(equality_resolution,[],[f84])).
% 2.18/0.68  fof(f84,plain,(
% 2.18/0.68    ( ! [X4,X5] : (k1_funct_1(sK10,X5) = X4 | k1_funct_1(sK11,X4) != X5 | ~r2_hidden(X4,sK9)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f55])).
% 2.18/0.68  fof(f2875,plain,(
% 2.18/0.68    spl15_92 | ~spl15_16 | ~spl15_44 | ~spl15_46),
% 2.18/0.68    inference(avatar_split_clause,[],[f2874,f1049,f1039,f350,f2551])).
% 2.18/0.68  fof(f350,plain,(
% 2.18/0.68    spl15_16 <=> sK8 = k2_relat_1(sK11)),
% 2.18/0.68    introduced(avatar_definition,[new_symbols(naming,[spl15_16])])).
% 2.18/0.68  fof(f1039,plain,(
% 2.18/0.68    spl15_44 <=> sK8 = k1_relat_1(sK10)),
% 2.18/0.68    introduced(avatar_definition,[new_symbols(naming,[spl15_44])])).
% 2.18/0.68  fof(f1049,plain,(
% 2.18/0.68    spl15_46 <=> sK9 = k1_relat_1(sK11)),
% 2.18/0.68    introduced(avatar_definition,[new_symbols(naming,[spl15_46])])).
% 2.18/0.68  fof(f2874,plain,(
% 2.18/0.68    sP2(sK10,sK11) | (~spl15_16 | ~spl15_44 | ~spl15_46)),
% 2.18/0.68    inference(subsumption_resolution,[],[f2873,f154])).
% 2.18/0.68  fof(f154,plain,(
% 2.18/0.68    v1_relat_1(sK10)),
% 2.18/0.68    inference(subsumption_resolution,[],[f151,f105])).
% 2.18/0.68  fof(f105,plain,(
% 2.18/0.68    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.18/0.68    inference(cnf_transformation,[],[f4])).
% 2.18/0.68  fof(f4,axiom,(
% 2.18/0.68    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.18/0.68  fof(f151,plain,(
% 2.18/0.68    v1_relat_1(sK10) | ~v1_relat_1(k2_zfmisc_1(sK8,sK9))),
% 2.18/0.68    inference(resolution,[],[f90,f77])).
% 2.18/0.68  fof(f77,plain,(
% 2.18/0.68    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))),
% 2.18/0.68    inference(cnf_transformation,[],[f55])).
% 2.18/0.68  fof(f90,plain,(
% 2.18/0.68    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f20])).
% 2.18/0.68  fof(f20,plain,(
% 2.18/0.68    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.18/0.68    inference(ennf_transformation,[],[f3])).
% 2.18/0.68  fof(f3,axiom,(
% 2.18/0.68    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.18/0.68  fof(f2873,plain,(
% 2.18/0.68    sP2(sK10,sK11) | ~v1_relat_1(sK10) | (~spl15_16 | ~spl15_44 | ~spl15_46)),
% 2.18/0.68    inference(subsumption_resolution,[],[f2872,f75])).
% 2.18/0.68  fof(f75,plain,(
% 2.18/0.68    v1_funct_1(sK10)),
% 2.18/0.68    inference(cnf_transformation,[],[f55])).
% 2.18/0.68  fof(f2872,plain,(
% 2.18/0.68    sP2(sK10,sK11) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | (~spl15_16 | ~spl15_44 | ~spl15_46)),
% 2.18/0.68    inference(subsumption_resolution,[],[f2871,f82])).
% 2.18/0.68  fof(f82,plain,(
% 2.18/0.68    v2_funct_1(sK10)),
% 2.18/0.68    inference(cnf_transformation,[],[f55])).
% 2.18/0.68  fof(f2871,plain,(
% 2.18/0.68    sP2(sK10,sK11) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | (~spl15_16 | ~spl15_44 | ~spl15_46)),
% 2.18/0.68    inference(subsumption_resolution,[],[f2823,f234])).
% 2.18/0.68  fof(f234,plain,(
% 2.18/0.68    sK9 = k2_relat_1(sK10)),
% 2.18/0.68    inference(subsumption_resolution,[],[f232,f77])).
% 2.18/0.68  fof(f232,plain,(
% 2.18/0.68    sK9 = k2_relat_1(sK10) | ~m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK8,sK9)))),
% 2.18/0.68    inference(superposition,[],[f113,f81])).
% 2.18/0.68  fof(f81,plain,(
% 2.18/0.68    sK9 = k2_relset_1(sK8,sK9,sK10)),
% 2.18/0.68    inference(cnf_transformation,[],[f55])).
% 2.18/0.68  fof(f113,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.68    inference(cnf_transformation,[],[f32])).
% 2.18/0.68  fof(f32,plain,(
% 2.18/0.68    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.68    inference(ennf_transformation,[],[f11])).
% 2.18/0.68  fof(f11,axiom,(
% 2.18/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.18/0.68  fof(f2823,plain,(
% 2.18/0.68    sP2(sK10,sK11) | sK9 != k2_relat_1(sK10) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | (~spl15_16 | ~spl15_44 | ~spl15_46)),
% 2.18/0.68    inference(subsumption_resolution,[],[f2821,f1041])).
% 2.18/0.68  fof(f1041,plain,(
% 2.18/0.68    sK8 = k1_relat_1(sK10) | ~spl15_44),
% 2.18/0.68    inference(avatar_component_clause,[],[f1039])).
% 2.18/0.68  fof(f2821,plain,(
% 2.18/0.68    sK8 != k1_relat_1(sK10) | sP2(sK10,sK11) | sK9 != k2_relat_1(sK10) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | (~spl15_16 | ~spl15_46)),
% 2.18/0.68    inference(trivial_inequality_removal,[],[f2739])).
% 2.18/0.68  fof(f2739,plain,(
% 2.18/0.68    sK11 != sK11 | sK8 != k1_relat_1(sK10) | sP2(sK10,sK11) | sK9 != k2_relat_1(sK10) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | (~spl15_16 | ~spl15_46)),
% 2.18/0.68    inference(superposition,[],[f89,f2017])).
% 2.18/0.68  fof(f2017,plain,(
% 2.18/0.68    ( ! [X0] : (k2_funct_1(X0) = sK11 | k1_relat_1(X0) != sK8 | sP2(X0,sK11) | k2_relat_1(X0) != sK9 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | (~spl15_16 | ~spl15_46)),
% 2.18/0.68    inference(forward_demodulation,[],[f2016,f1051])).
% 2.18/0.68  fof(f1051,plain,(
% 2.18/0.68    sK9 = k1_relat_1(sK11) | ~spl15_46),
% 2.18/0.68    inference(avatar_component_clause,[],[f1049])).
% 2.18/0.68  fof(f2016,plain,(
% 2.18/0.68    ( ! [X0] : (k1_relat_1(X0) != sK8 | sP2(X0,sK11) | k2_relat_1(X0) != k1_relat_1(sK11) | k2_funct_1(X0) = sK11 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl15_16),
% 2.18/0.68    inference(subsumption_resolution,[],[f2015,f155])).
% 2.18/0.68  fof(f155,plain,(
% 2.18/0.68    v1_relat_1(sK11)),
% 2.18/0.68    inference(subsumption_resolution,[],[f152,f105])).
% 2.18/0.68  fof(f152,plain,(
% 2.18/0.68    v1_relat_1(sK11) | ~v1_relat_1(k2_zfmisc_1(sK9,sK8))),
% 2.18/0.68    inference(resolution,[],[f90,f80])).
% 2.18/0.68  fof(f80,plain,(
% 2.18/0.68    m1_subset_1(sK11,k1_zfmisc_1(k2_zfmisc_1(sK9,sK8)))),
% 2.18/0.68    inference(cnf_transformation,[],[f55])).
% 2.18/0.68  fof(f2015,plain,(
% 2.18/0.68    ( ! [X0] : (k1_relat_1(X0) != sK8 | sP2(X0,sK11) | k2_relat_1(X0) != k1_relat_1(sK11) | k2_funct_1(X0) = sK11 | ~v2_funct_1(X0) | ~v1_relat_1(sK11) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl15_16),
% 2.18/0.68    inference(subsumption_resolution,[],[f1989,f78])).
% 2.18/0.68  fof(f78,plain,(
% 2.18/0.68    v1_funct_1(sK11)),
% 2.18/0.68    inference(cnf_transformation,[],[f55])).
% 2.18/0.68  fof(f1989,plain,(
% 2.18/0.68    ( ! [X0] : (k1_relat_1(X0) != sK8 | sP2(X0,sK11) | k2_relat_1(X0) != k1_relat_1(sK11) | k2_funct_1(X0) = sK11 | ~v2_funct_1(X0) | ~v1_funct_1(sK11) | ~v1_relat_1(sK11) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl15_16),
% 2.18/0.68    inference(superposition,[],[f104,f352])).
% 2.18/0.68  fof(f352,plain,(
% 2.18/0.68    sK8 = k2_relat_1(sK11) | ~spl15_16),
% 2.18/0.68    inference(avatar_component_clause,[],[f350])).
% 2.18/0.68  fof(f104,plain,(
% 2.18/0.68    ( ! [X0,X1] : (k2_relat_1(X1) != k1_relat_1(X0) | sP2(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | k2_funct_1(X0) = X1 | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f44])).
% 2.18/0.68  fof(f44,plain,(
% 2.18/0.68    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | sP2(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/0.68    inference(definition_folding,[],[f28,f43,f42])).
% 2.18/0.68  fof(f28,plain,(
% 2.18/0.68    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | ? [X2,X3] : ((k1_funct_1(X0,X2) = X3 <~> k1_funct_1(X1,X3) = X2) & r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) | k1_relat_1(X1) != k2_relat_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/0.68    inference(flattening,[],[f27])).
% 2.18/0.68  fof(f27,plain,(
% 2.18/0.68    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (? [X2,X3] : ((k1_funct_1(X0,X2) = X3 <~> k1_funct_1(X1,X3) = X2) & (r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0)))) | k1_relat_1(X1) != k2_relat_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.18/0.68    inference(ennf_transformation,[],[f8])).
% 2.18/0.68  fof(f8,axiom,(
% 2.18/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((! [X2,X3] : ((r2_hidden(X3,k1_relat_1(X1)) & r2_hidden(X2,k1_relat_1(X0))) => (k1_funct_1(X0,X2) = X3 <=> k1_funct_1(X1,X3) = X2)) & k1_relat_1(X1) = k2_relat_1(X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_funct_1)).
% 2.18/0.68  fof(f89,plain,(
% 2.18/0.68    k2_funct_1(sK10) != sK11),
% 2.18/0.68    inference(cnf_transformation,[],[f55])).
% 2.18/0.68  fof(f2609,plain,(
% 2.18/0.68    ~spl15_92 | spl15_98 | ~spl15_44),
% 2.18/0.68    inference(avatar_split_clause,[],[f2568,f1039,f2606,f2551])).
% 2.18/0.68  fof(f2568,plain,(
% 2.18/0.68    sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11)) | ~sP2(sK10,sK11) | ~spl15_44),
% 2.18/0.68    inference(trivial_inequality_removal,[],[f2567])).
% 2.18/0.68  fof(f2567,plain,(
% 2.18/0.68    sK12(sK10,sK11) != sK12(sK10,sK11) | sK12(sK10,sK11) = k1_funct_1(sK11,sK13(sK10,sK11)) | ~sP2(sK10,sK11) | ~spl15_44),
% 2.18/0.68    inference(equality_factoring,[],[f1733])).
% 2.18/0.68  fof(f1733,plain,(
% 2.18/0.68    ( ! [X2] : (sK12(sK10,X2) = k1_funct_1(sK11,sK13(sK10,X2)) | sK12(sK10,X2) = k1_funct_1(X2,sK13(sK10,X2)) | ~sP2(sK10,X2)) ) | ~spl15_44),
% 2.18/0.68    inference(subsumption_resolution,[],[f1723,f1087])).
% 2.18/0.68  fof(f1087,plain,(
% 2.18/0.68    ( ! [X0] : (r2_hidden(sK12(sK10,X0),sK8) | ~sP2(sK10,X0)) ) | ~spl15_44),
% 2.18/0.68    inference(superposition,[],[f99,f1041])).
% 2.18/0.68  fof(f99,plain,(
% 2.18/0.68    ( ! [X0,X1] : (r2_hidden(sK12(X0,X1),k1_relat_1(X0)) | ~sP2(X0,X1)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f59])).
% 2.18/0.68  fof(f1723,plain,(
% 2.18/0.68    ( ! [X2] : (sK12(sK10,X2) = k1_funct_1(sK11,sK13(sK10,X2)) | ~r2_hidden(sK12(sK10,X2),sK8) | sK12(sK10,X2) = k1_funct_1(X2,sK13(sK10,X2)) | ~sP2(sK10,X2)) )),
% 2.18/0.68    inference(superposition,[],[f132,f388])).
% 2.18/0.68  fof(f388,plain,(
% 2.18/0.68    ( ! [X0,X1] : (sK13(X0,X1) = k1_funct_1(X0,sK12(X0,X1)) | sK12(X0,X1) = k1_funct_1(X1,sK13(X0,X1)) | ~sP2(X0,X1)) )),
% 2.18/0.68    inference(resolution,[],[f102,f101])).
% 2.18/0.68  fof(f102,plain,(
% 2.18/0.68    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | k1_funct_1(X3,X0) = X1 | k1_funct_1(X2,X1) = X0) )),
% 2.18/0.68    inference(cnf_transformation,[],[f61])).
% 2.18/0.68  fof(f132,plain,(
% 2.18/0.68    ( ! [X5] : (k1_funct_1(sK11,k1_funct_1(sK10,X5)) = X5 | ~r2_hidden(X5,sK8)) )),
% 2.18/0.68    inference(equality_resolution,[],[f86])).
% 2.18/0.68  fof(f86,plain,(
% 2.18/0.68    ( ! [X4,X5] : (k1_funct_1(sK11,X4) = X5 | k1_funct_1(sK10,X5) != X4 | ~r2_hidden(X5,sK8)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f55])).
% 2.18/0.68  fof(f2604,plain,(
% 2.18/0.68    ~spl15_46 | ~spl15_92 | spl15_94),
% 2.18/0.68    inference(avatar_contradiction_clause,[],[f2603])).
% 2.18/0.68  fof(f2603,plain,(
% 2.18/0.68    $false | (~spl15_46 | ~spl15_92 | spl15_94)),
% 2.18/0.68    inference(subsumption_resolution,[],[f2602,f2553])).
% 2.18/0.68  fof(f2602,plain,(
% 2.18/0.68    ~sP2(sK10,sK11) | (~spl15_46 | spl15_94)),
% 2.18/0.68    inference(resolution,[],[f2582,f1270])).
% 2.18/0.68  fof(f1270,plain,(
% 2.18/0.68    ( ! [X1] : (r2_hidden(sK13(X1,sK11),sK9) | ~sP2(X1,sK11)) ) | ~spl15_46),
% 2.18/0.68    inference(superposition,[],[f100,f1051])).
% 2.18/0.68  fof(f100,plain,(
% 2.18/0.68    ( ! [X0,X1] : (r2_hidden(sK13(X0,X1),k1_relat_1(X1)) | ~sP2(X0,X1)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f59])).
% 2.18/0.68  fof(f2582,plain,(
% 2.18/0.68    ~r2_hidden(sK13(sK10,sK11),sK9) | spl15_94),
% 2.18/0.68    inference(avatar_component_clause,[],[f2580])).
% 2.18/0.68  fof(f1966,plain,(
% 2.18/0.68    spl15_16 | ~spl15_15),
% 2.18/0.68    inference(avatar_split_clause,[],[f1965,f346,f350])).
% 2.18/0.68  fof(f346,plain,(
% 2.18/0.68    spl15_15 <=> r1_tarski(sK8,k2_relat_1(sK11))),
% 2.18/0.68    introduced(avatar_definition,[new_symbols(naming,[spl15_15])])).
% 2.18/0.68  fof(f1965,plain,(
% 2.18/0.68    sK8 = k2_relat_1(sK11) | ~spl15_15),
% 2.18/0.68    inference(subsumption_resolution,[],[f1963,f331])).
% 2.18/0.68  fof(f331,plain,(
% 2.18/0.68    r1_tarski(k2_relat_1(sK11),sK8)),
% 2.18/0.68    inference(resolution,[],[f325,f110])).
% 2.18/0.68  fof(f110,plain,(
% 2.18/0.68    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f64])).
% 2.18/0.68  fof(f64,plain,(
% 2.18/0.68    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.18/0.68    inference(nnf_transformation,[],[f2])).
% 2.18/0.68  fof(f2,axiom,(
% 2.18/0.68    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.18/0.68  fof(f325,plain,(
% 2.18/0.68    m1_subset_1(k2_relat_1(sK11),k1_zfmisc_1(sK8))),
% 2.18/0.68    inference(resolution,[],[f282,f80])).
% 2.18/0.68  fof(f282,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1))) )),
% 2.18/0.68    inference(duplicate_literal_removal,[],[f281])).
% 2.18/0.68  fof(f281,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (m1_subset_1(k2_relat_1(X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.68    inference(superposition,[],[f114,f113])).
% 2.18/0.68  fof(f114,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.68    inference(cnf_transformation,[],[f33])).
% 2.18/0.68  fof(f33,plain,(
% 2.18/0.68    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.68    inference(ennf_transformation,[],[f9])).
% 2.18/0.68  fof(f9,axiom,(
% 2.18/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).
% 2.18/0.68  fof(f1963,plain,(
% 2.18/0.68    sK8 = k2_relat_1(sK11) | ~r1_tarski(k2_relat_1(sK11),sK8) | ~spl15_15),
% 2.18/0.68    inference(resolution,[],[f347,f109])).
% 2.18/0.68  fof(f109,plain,(
% 2.18/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f63])).
% 2.18/0.68  fof(f63,plain,(
% 2.18/0.68    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.18/0.68    inference(flattening,[],[f62])).
% 2.18/0.68  fof(f62,plain,(
% 2.18/0.68    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.18/0.68    inference(nnf_transformation,[],[f1])).
% 2.18/0.68  fof(f1,axiom,(
% 2.18/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.18/0.68  fof(f347,plain,(
% 2.18/0.68    r1_tarski(sK8,k2_relat_1(sK11)) | ~spl15_15),
% 2.18/0.68    inference(avatar_component_clause,[],[f346])).
% 2.18/0.68  fof(f1960,plain,(
% 2.18/0.68    spl15_15 | ~spl15_67 | ~spl15_77),
% 2.18/0.68    inference(avatar_split_clause,[],[f1957,f1934,f1478,f346])).
% 2.18/0.68  fof(f1478,plain,(
% 2.18/0.68    spl15_67 <=> sK8 = k2_relat_1(k2_funct_1(sK10))),
% 2.18/0.68    introduced(avatar_definition,[new_symbols(naming,[spl15_67])])).
% 2.18/0.68  fof(f1934,plain,(
% 2.18/0.68    spl15_77 <=> sP6(k2_relat_1(sK11),sK9,k2_funct_1(sK10))),
% 2.18/0.68    introduced(avatar_definition,[new_symbols(naming,[spl15_77])])).
% 2.18/0.68  fof(f1957,plain,(
% 2.18/0.68    r1_tarski(sK8,k2_relat_1(sK11)) | (~spl15_67 | ~spl15_77)),
% 2.18/0.68    inference(forward_demodulation,[],[f1956,f1480])).
% 2.18/0.68  fof(f1480,plain,(
% 2.18/0.68    sK8 = k2_relat_1(k2_funct_1(sK10)) | ~spl15_67),
% 2.18/0.68    inference(avatar_component_clause,[],[f1478])).
% 2.18/0.68  fof(f1956,plain,(
% 2.18/0.68    r1_tarski(k2_relat_1(k2_funct_1(sK10)),k2_relat_1(sK11)) | ~spl15_77),
% 2.18/0.68    inference(resolution,[],[f1936,f361])).
% 2.18/0.68  fof(f361,plain,(
% 2.18/0.68    ( ! [X4,X5,X3] : (~sP6(X3,X4,X5) | r1_tarski(k2_relat_1(X5),X3)) )),
% 2.18/0.68    inference(resolution,[],[f321,f110])).
% 2.18/0.68  fof(f321,plain,(
% 2.18/0.68    ( ! [X2,X3,X1] : (m1_subset_1(k2_relat_1(X1),k1_zfmisc_1(X2)) | ~sP6(X2,X3,X1)) )),
% 2.18/0.68    inference(resolution,[],[f282,f125])).
% 2.18/0.68  fof(f125,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP6(X0,X1,X2)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f71])).
% 2.18/0.68  fof(f71,plain,(
% 2.18/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X2,X1,X0) & v1_funct_1(X2)) | ~sP6(X0,X1,X2))),
% 2.18/0.68    inference(rectify,[],[f70])).
% 2.18/0.68  fof(f70,plain,(
% 2.18/0.68    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP6(X1,X0,X2))),
% 2.18/0.68    inference(nnf_transformation,[],[f49])).
% 2.18/0.68  fof(f49,plain,(
% 2.18/0.68    ! [X1,X0,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~sP6(X1,X0,X2))),
% 2.18/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP6])])).
% 2.18/0.68  fof(f1936,plain,(
% 2.18/0.68    sP6(k2_relat_1(sK11),sK9,k2_funct_1(sK10)) | ~spl15_77),
% 2.18/0.68    inference(avatar_component_clause,[],[f1934])).
% 2.18/0.68  fof(f1940,plain,(
% 2.18/0.68    spl15_77 | ~spl15_42 | ~spl15_43 | ~spl15_44 | spl15_47 | ~spl15_67 | spl15_76),
% 2.18/0.68    inference(avatar_split_clause,[],[f1939,f1930,f1478,f1053,f1039,f881,f859,f1934])).
% 2.18/0.68  fof(f859,plain,(
% 2.18/0.68    spl15_42 <=> sP0(k2_funct_1(sK10))),
% 2.18/0.68    introduced(avatar_definition,[new_symbols(naming,[spl15_42])])).
% 2.18/0.68  fof(f881,plain,(
% 2.18/0.68    spl15_43 <=> v1_funct_2(k2_funct_1(sK10),sK9,k2_relat_1(k2_funct_1(sK10)))),
% 2.18/0.68    introduced(avatar_definition,[new_symbols(naming,[spl15_43])])).
% 2.18/0.68  fof(f1053,plain,(
% 2.18/0.68    spl15_47 <=> sP3(sK9,sK8)),
% 2.18/0.68    introduced(avatar_definition,[new_symbols(naming,[spl15_47])])).
% 2.18/0.68  fof(f1930,plain,(
% 2.18/0.68    spl15_76 <=> r2_hidden(k1_funct_1(k2_funct_1(sK10),sK14(sK9,k2_relat_1(sK11),k2_funct_1(sK10))),sK8)),
% 2.18/0.68    introduced(avatar_definition,[new_symbols(naming,[spl15_76])])).
% 2.18/0.68  fof(f1939,plain,(
% 2.18/0.68    sP6(k2_relat_1(sK11),sK9,k2_funct_1(sK10)) | (~spl15_42 | ~spl15_43 | ~spl15_44 | spl15_47 | ~spl15_67 | spl15_76)),
% 2.18/0.68    inference(resolution,[],[f1938,f1863])).
% 2.18/0.68  fof(f1863,plain,(
% 2.18/0.68    ( ! [X3] : (r2_hidden(sK14(sK9,X3,k2_funct_1(sK10)),sK9) | sP6(X3,sK9,k2_funct_1(sK10))) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f1862,f154])).
% 2.18/0.68  fof(f1862,plain,(
% 2.18/0.68    ( ! [X3] : (r2_hidden(sK14(sK9,X3,k2_funct_1(sK10)),sK9) | sP6(X3,sK9,k2_funct_1(sK10)) | ~v1_relat_1(sK10)) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f1861,f75])).
% 2.18/0.68  fof(f1861,plain,(
% 2.18/0.68    ( ! [X3] : (r2_hidden(sK14(sK9,X3,k2_funct_1(sK10)),sK9) | sP6(X3,sK9,k2_funct_1(sK10)) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f1858,f82])).
% 2.18/0.68  fof(f1858,plain,(
% 2.18/0.68    ( ! [X3] : (r2_hidden(sK14(sK9,X3,k2_funct_1(sK10)),sK9) | sP6(X3,sK9,k2_funct_1(sK10)) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)) )),
% 2.18/0.68    inference(superposition,[],[f463,f234])).
% 2.18/0.68  fof(f463,plain,(
% 2.18/0.68    ( ! [X0,X1] : (r2_hidden(sK14(k2_relat_1(X0),X1,k2_funct_1(X0)),k2_relat_1(X0)) | sP6(X1,k2_relat_1(X0),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f462,f95])).
% 2.18/0.68  fof(f95,plain,(
% 2.18/0.68    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f24])).
% 2.18/0.68  fof(f24,plain,(
% 2.18/0.68    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/0.68    inference(flattening,[],[f23])).
% 2.18/0.68  fof(f23,plain,(
% 2.18/0.68    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.18/0.68    inference(ennf_transformation,[],[f5])).
% 2.18/0.68  fof(f5,axiom,(
% 2.18/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.18/0.68  fof(f462,plain,(
% 2.18/0.68    ( ! [X0,X1] : (r2_hidden(sK14(k2_relat_1(X0),X1,k2_funct_1(X0)),k2_relat_1(X0)) | sP6(X1,k2_relat_1(X0),k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f461,f96])).
% 2.18/0.68  fof(f96,plain,(
% 2.18/0.68    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f24])).
% 2.18/0.68  fof(f461,plain,(
% 2.18/0.68    ( ! [X0,X1] : (r2_hidden(sK14(k2_relat_1(X0),X1,k2_funct_1(X0)),k2_relat_1(X0)) | sP6(X1,k2_relat_1(X0),k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(superposition,[],[f144,f97])).
% 2.18/0.68  fof(f97,plain,(
% 2.18/0.68    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f26])).
% 2.18/0.68  fof(f26,plain,(
% 2.18/0.68    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/0.68    inference(flattening,[],[f25])).
% 2.18/0.68  fof(f25,plain,(
% 2.18/0.68    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.18/0.68    inference(ennf_transformation,[],[f7])).
% 2.18/0.68  fof(f7,axiom,(
% 2.18/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 2.18/0.68  fof(f144,plain,(
% 2.18/0.68    ( ! [X2,X1] : (r2_hidden(sK14(k1_relat_1(X2),X1,X2),k1_relat_1(X2)) | sP6(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.18/0.68    inference(equality_resolution,[],[f126])).
% 2.18/0.68  fof(f126,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (sP6(X1,X0,X2) | r2_hidden(sK14(X0,X1,X2),X0) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f73])).
% 2.18/0.68  fof(f73,plain,(
% 2.18/0.68    ! [X0,X1,X2] : (sP6(X1,X0,X2) | (~r2_hidden(k1_funct_1(X2,sK14(X0,X1,X2)),X1) & r2_hidden(sK14(X0,X1,X2),X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.18/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK14])],[f50,f72])).
% 2.18/0.68  fof(f72,plain,(
% 2.18/0.68    ! [X2,X1,X0] : (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) => (~r2_hidden(k1_funct_1(X2,sK14(X0,X1,X2)),X1) & r2_hidden(sK14(X0,X1,X2),X0)))),
% 2.18/0.68    introduced(choice_axiom,[])).
% 2.18/0.68  fof(f50,plain,(
% 2.18/0.68    ! [X0,X1,X2] : (sP6(X1,X0,X2) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.18/0.68    inference(definition_folding,[],[f37,f49])).
% 2.18/0.68  fof(f37,plain,(
% 2.18/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 2.18/0.68    inference(flattening,[],[f36])).
% 2.18/0.68  fof(f36,plain,(
% 2.18/0.68    ! [X0,X1,X2] : (((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (? [X3] : (~r2_hidden(k1_funct_1(X2,X3),X1) & r2_hidden(X3,X0)) | k1_relat_1(X2) != X0)) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 2.18/0.68    inference(ennf_transformation,[],[f15])).
% 2.18/0.68  fof(f15,axiom,(
% 2.18/0.68    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => ((! [X3] : (r2_hidden(X3,X0) => r2_hidden(k1_funct_1(X2,X3),X1)) & k1_relat_1(X2) = X0) => (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_funct_2)).
% 2.18/0.68  fof(f1938,plain,(
% 2.18/0.68    ~r2_hidden(sK14(sK9,k2_relat_1(sK11),k2_funct_1(sK10)),sK9) | (~spl15_42 | ~spl15_43 | ~spl15_44 | spl15_47 | ~spl15_67 | spl15_76)),
% 2.18/0.68    inference(resolution,[],[f1932,f1774])).
% 2.18/0.68  fof(f1774,plain,(
% 2.18/0.68    ( ! [X2] : (r2_hidden(k1_funct_1(k2_funct_1(sK10),X2),sK8) | ~r2_hidden(X2,sK9)) ) | (~spl15_42 | ~spl15_43 | ~spl15_44 | spl15_47 | ~spl15_67)),
% 2.18/0.68    inference(backward_demodulation,[],[f1436,f1659])).
% 2.18/0.68  fof(f1659,plain,(
% 2.18/0.68    sK9 = k1_relat_1(k2_funct_1(sK10)) | (~spl15_42 | ~spl15_43 | ~spl15_44 | spl15_47 | ~spl15_67)),
% 2.18/0.68    inference(subsumption_resolution,[],[f1658,f1054])).
% 2.18/0.68  fof(f1054,plain,(
% 2.18/0.68    ~sP3(sK9,sK8) | spl15_47),
% 2.18/0.68    inference(avatar_component_clause,[],[f1053])).
% 2.18/0.68  fof(f1658,plain,(
% 2.18/0.68    sP3(sK9,sK8) | sK9 = k1_relat_1(k2_funct_1(sK10)) | (~spl15_42 | ~spl15_43 | ~spl15_44 | ~spl15_67)),
% 2.18/0.68    inference(subsumption_resolution,[],[f1653,f1081])).
% 2.18/0.68  fof(f1081,plain,(
% 2.18/0.68    v1_funct_2(k2_funct_1(sK10),sK9,sK8) | (~spl15_43 | ~spl15_44)),
% 2.18/0.68    inference(backward_demodulation,[],[f900,f1041])).
% 2.18/0.68  fof(f900,plain,(
% 2.18/0.68    v1_funct_2(k2_funct_1(sK10),sK9,k1_relat_1(sK10)) | ~spl15_43),
% 2.18/0.68    inference(subsumption_resolution,[],[f899,f154])).
% 2.18/0.68  fof(f899,plain,(
% 2.18/0.68    v1_funct_2(k2_funct_1(sK10),sK9,k1_relat_1(sK10)) | ~v1_relat_1(sK10) | ~spl15_43),
% 2.18/0.68    inference(subsumption_resolution,[],[f898,f75])).
% 2.18/0.68  fof(f898,plain,(
% 2.18/0.68    v1_funct_2(k2_funct_1(sK10),sK9,k1_relat_1(sK10)) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | ~spl15_43),
% 2.18/0.68    inference(subsumption_resolution,[],[f896,f82])).
% 2.18/0.68  fof(f896,plain,(
% 2.18/0.68    v1_funct_2(k2_funct_1(sK10),sK9,k1_relat_1(sK10)) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | ~spl15_43),
% 2.18/0.68    inference(superposition,[],[f883,f98])).
% 2.18/0.68  fof(f98,plain,(
% 2.18/0.68    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f26])).
% 2.18/0.68  fof(f883,plain,(
% 2.18/0.68    v1_funct_2(k2_funct_1(sK10),sK9,k2_relat_1(k2_funct_1(sK10))) | ~spl15_43),
% 2.18/0.68    inference(avatar_component_clause,[],[f881])).
% 2.18/0.68  fof(f1653,plain,(
% 2.18/0.68    ~v1_funct_2(k2_funct_1(sK10),sK9,sK8) | sP3(sK9,sK8) | sK9 = k1_relat_1(k2_funct_1(sK10)) | (~spl15_42 | ~spl15_67)),
% 2.18/0.68    inference(resolution,[],[f1577,f418])).
% 2.18/0.68  fof(f418,plain,(
% 2.18/0.68    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | sP3(X3,X4) | k1_relat_1(X5) = X3) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f416,f121])).
% 2.18/0.68  fof(f121,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | sP4(X0,X2,X1)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f48])).
% 2.18/0.68  fof(f48,plain,(
% 2.18/0.68    ! [X0,X1,X2] : ((sP5(X2,X1,X0) & sP4(X0,X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.68    inference(definition_folding,[],[f35,f47,f46,f45])).
% 2.18/0.68  fof(f46,plain,(
% 2.18/0.68    ! [X0,X2,X1] : ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | sP3(X0,X1) | ~sP4(X0,X2,X1))),
% 2.18/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP4])])).
% 2.18/0.68  fof(f47,plain,(
% 2.18/0.68    ! [X2,X1,X0] : ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~sP5(X2,X1,X0))),
% 2.18/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP5])])).
% 2.18/0.68  fof(f35,plain,(
% 2.18/0.68    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.68    inference(flattening,[],[f34])).
% 2.18/0.68  fof(f34,plain,(
% 2.18/0.68    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.68    inference(ennf_transformation,[],[f12])).
% 2.18/0.68  fof(f12,axiom,(
% 2.18/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 2.18/0.68  fof(f416,plain,(
% 2.18/0.68    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4) | sP3(X3,X4) | ~sP4(X3,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) )),
% 2.18/0.68    inference(superposition,[],[f117,f112])).
% 2.18/0.68  fof(f112,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.18/0.68    inference(cnf_transformation,[],[f31])).
% 2.18/0.68  fof(f31,plain,(
% 2.18/0.68    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.18/0.68    inference(ennf_transformation,[],[f10])).
% 2.18/0.68  fof(f10,axiom,(
% 2.18/0.68    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 2.18/0.68  fof(f117,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2) | sP3(X0,X2) | ~sP4(X0,X1,X2)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f68])).
% 2.18/0.68  fof(f68,plain,(
% 2.18/0.68    ! [X0,X1,X2] : (((v1_funct_2(X1,X0,X2) | k1_relset_1(X0,X2,X1) != X0) & (k1_relset_1(X0,X2,X1) = X0 | ~v1_funct_2(X1,X0,X2))) | sP3(X0,X2) | ~sP4(X0,X1,X2))),
% 2.18/0.68    inference(rectify,[],[f67])).
% 2.18/0.68  fof(f67,plain,(
% 2.18/0.68    ! [X0,X2,X1] : (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | sP3(X0,X1) | ~sP4(X0,X2,X1))),
% 2.18/0.68    inference(nnf_transformation,[],[f46])).
% 2.18/0.68  fof(f1577,plain,(
% 2.18/0.68    m1_subset_1(k2_funct_1(sK10),k1_zfmisc_1(k2_zfmisc_1(sK9,sK8))) | (~spl15_42 | ~spl15_67)),
% 2.18/0.68    inference(forward_demodulation,[],[f1576,f234])).
% 2.18/0.68  fof(f1576,plain,(
% 2.18/0.68    m1_subset_1(k2_funct_1(sK10),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK10),sK8))) | (~spl15_42 | ~spl15_67)),
% 2.18/0.68    inference(subsumption_resolution,[],[f1575,f154])).
% 2.18/0.68  fof(f1575,plain,(
% 2.18/0.68    m1_subset_1(k2_funct_1(sK10),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK10),sK8))) | ~v1_relat_1(sK10) | (~spl15_42 | ~spl15_67)),
% 2.18/0.68    inference(subsumption_resolution,[],[f1574,f75])).
% 2.18/0.68  fof(f1574,plain,(
% 2.18/0.68    m1_subset_1(k2_funct_1(sK10),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK10),sK8))) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | (~spl15_42 | ~spl15_67)),
% 2.18/0.68    inference(subsumption_resolution,[],[f1573,f82])).
% 2.18/0.68  fof(f1573,plain,(
% 2.18/0.68    m1_subset_1(k2_funct_1(sK10),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK10),sK8))) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | (~spl15_42 | ~spl15_67)),
% 2.18/0.68    inference(subsumption_resolution,[],[f1545,f860])).
% 2.18/0.68  fof(f860,plain,(
% 2.18/0.68    sP0(k2_funct_1(sK10)) | ~spl15_42),
% 2.18/0.68    inference(avatar_component_clause,[],[f859])).
% 2.18/0.68  fof(f1545,plain,(
% 2.18/0.68    m1_subset_1(k2_funct_1(sK10),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK10),sK8))) | ~sP0(k2_funct_1(sK10)) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | ~spl15_67),
% 2.18/0.68    inference(superposition,[],[f221,f1480])).
% 2.18/0.68  fof(f221,plain,(
% 2.18/0.68    ( ! [X1] : (m1_subset_1(k2_funct_1(X1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(X1),k2_relat_1(k2_funct_1(X1))))) | ~sP0(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.18/0.68    inference(superposition,[],[f93,f97])).
% 2.18/0.68  fof(f93,plain,(
% 2.18/0.68    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~sP0(X0)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f56])).
% 2.18/0.68  fof(f56,plain,(
% 2.18/0.68    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~sP0(X0))),
% 2.18/0.68    inference(nnf_transformation,[],[f40])).
% 2.18/0.68  fof(f40,plain,(
% 2.18/0.68    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~sP0(X0))),
% 2.18/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.18/0.68  fof(f1436,plain,(
% 2.18/0.68    ( ! [X2] : (r2_hidden(k1_funct_1(k2_funct_1(sK10),X2),sK8) | ~r2_hidden(X2,k1_relat_1(k2_funct_1(sK10)))) ) | ~spl15_44),
% 2.18/0.68    inference(subsumption_resolution,[],[f1435,f154])).
% 2.18/0.68  fof(f1435,plain,(
% 2.18/0.68    ( ! [X2] : (r2_hidden(k1_funct_1(k2_funct_1(sK10),X2),sK8) | ~r2_hidden(X2,k1_relat_1(k2_funct_1(sK10))) | ~v1_relat_1(sK10)) ) | ~spl15_44),
% 2.18/0.68    inference(subsumption_resolution,[],[f1434,f75])).
% 2.18/0.68  fof(f1434,plain,(
% 2.18/0.68    ( ! [X2] : (r2_hidden(k1_funct_1(k2_funct_1(sK10),X2),sK8) | ~r2_hidden(X2,k1_relat_1(k2_funct_1(sK10))) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)) ) | ~spl15_44),
% 2.18/0.68    inference(subsumption_resolution,[],[f1427,f82])).
% 2.18/0.68  fof(f1427,plain,(
% 2.18/0.68    ( ! [X2] : (r2_hidden(k1_funct_1(k2_funct_1(sK10),X2),sK8) | ~r2_hidden(X2,k1_relat_1(k2_funct_1(sK10))) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)) ) | ~spl15_44),
% 2.18/0.68    inference(superposition,[],[f313,f1041])).
% 2.18/0.68  fof(f313,plain,(
% 2.18/0.68    ( ! [X0,X1] : (r2_hidden(k1_funct_1(k2_funct_1(X0),X1),k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f312,f95])).
% 2.18/0.68  fof(f312,plain,(
% 2.18/0.68    ( ! [X0,X1] : (r2_hidden(k1_funct_1(k2_funct_1(X0),X1),k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(k2_funct_1(X0))) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f305,f96])).
% 2.18/0.68  fof(f305,plain,(
% 2.18/0.68    ( ! [X0,X1] : (r2_hidden(k1_funct_1(k2_funct_1(X0),X1),k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(superposition,[],[f106,f98])).
% 2.18/0.68  fof(f106,plain,(
% 2.18/0.68    ( ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f30])).
% 2.18/0.68  fof(f30,plain,(
% 2.18/0.68    ! [X0,X1] : (r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.18/0.68    inference(flattening,[],[f29])).
% 2.18/0.68  fof(f29,plain,(
% 2.18/0.68    ! [X0,X1] : ((r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.18/0.68    inference(ennf_transformation,[],[f6])).
% 2.18/0.68  fof(f6,axiom,(
% 2.18/0.68    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r2_hidden(X0,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_funct_1)).
% 2.18/0.68  fof(f1932,plain,(
% 2.18/0.68    ~r2_hidden(k1_funct_1(k2_funct_1(sK10),sK14(sK9,k2_relat_1(sK11),k2_funct_1(sK10))),sK8) | spl15_76),
% 2.18/0.68    inference(avatar_component_clause,[],[f1930])).
% 2.18/0.68  fof(f1937,plain,(
% 2.18/0.68    ~spl15_76 | spl15_77 | ~spl15_46),
% 2.18/0.68    inference(avatar_split_clause,[],[f1921,f1049,f1934,f1930])).
% 2.18/0.68  fof(f1921,plain,(
% 2.18/0.68    sP6(k2_relat_1(sK11),sK9,k2_funct_1(sK10)) | ~r2_hidden(k1_funct_1(k2_funct_1(sK10),sK14(sK9,k2_relat_1(sK11),k2_funct_1(sK10))),sK8) | ~spl15_46),
% 2.18/0.68    inference(resolution,[],[f1902,f1355])).
% 2.18/0.68  fof(f1355,plain,(
% 2.18/0.68    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK11)) | ~r2_hidden(X0,sK8)) ) | ~spl15_46),
% 2.18/0.68    inference(subsumption_resolution,[],[f1354,f133])).
% 2.18/0.68  fof(f133,plain,(
% 2.18/0.68    ( ! [X5] : (r2_hidden(k1_funct_1(sK10,X5),sK9) | ~r2_hidden(X5,sK8)) )),
% 2.18/0.68    inference(equality_resolution,[],[f85])).
% 2.18/0.68  fof(f85,plain,(
% 2.18/0.68    ( ! [X4,X5] : (r2_hidden(X4,sK9) | k1_funct_1(sK10,X5) != X4 | ~r2_hidden(X5,sK8)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f55])).
% 2.18/0.68  fof(f1354,plain,(
% 2.18/0.68    ( ! [X0] : (~r2_hidden(k1_funct_1(sK10,X0),sK9) | r2_hidden(X0,k2_relat_1(sK11)) | ~r2_hidden(X0,sK8)) ) | ~spl15_46),
% 2.18/0.68    inference(forward_demodulation,[],[f308,f1051])).
% 2.18/0.68  fof(f308,plain,(
% 2.18/0.68    ( ! [X0] : (~r2_hidden(k1_funct_1(sK10,X0),k1_relat_1(sK11)) | r2_hidden(X0,k2_relat_1(sK11)) | ~r2_hidden(X0,sK8)) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f307,f155])).
% 2.18/0.68  fof(f307,plain,(
% 2.18/0.68    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK11)) | ~r2_hidden(k1_funct_1(sK10,X0),k1_relat_1(sK11)) | ~v1_relat_1(sK11) | ~r2_hidden(X0,sK8)) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f303,f78])).
% 2.18/0.68  fof(f303,plain,(
% 2.18/0.68    ( ! [X0] : (r2_hidden(X0,k2_relat_1(sK11)) | ~r2_hidden(k1_funct_1(sK10,X0),k1_relat_1(sK11)) | ~v1_funct_1(sK11) | ~v1_relat_1(sK11) | ~r2_hidden(X0,sK8)) )),
% 2.18/0.68    inference(superposition,[],[f106,f132])).
% 2.18/0.68  fof(f1902,plain,(
% 2.18/0.68    ( ! [X3] : (~r2_hidden(k1_funct_1(k2_funct_1(sK10),sK14(sK9,X3,k2_funct_1(sK10))),X3) | sP6(X3,sK9,k2_funct_1(sK10))) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f1901,f154])).
% 2.18/0.68  fof(f1901,plain,(
% 2.18/0.68    ( ! [X3] : (~r2_hidden(k1_funct_1(k2_funct_1(sK10),sK14(sK9,X3,k2_funct_1(sK10))),X3) | sP6(X3,sK9,k2_funct_1(sK10)) | ~v1_relat_1(sK10)) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f1900,f75])).
% 2.18/0.68  fof(f1900,plain,(
% 2.18/0.68    ( ! [X3] : (~r2_hidden(k1_funct_1(k2_funct_1(sK10),sK14(sK9,X3,k2_funct_1(sK10))),X3) | sP6(X3,sK9,k2_funct_1(sK10)) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f1894,f82])).
% 2.18/0.68  fof(f1894,plain,(
% 2.18/0.68    ( ! [X3] : (~r2_hidden(k1_funct_1(k2_funct_1(sK10),sK14(sK9,X3,k2_funct_1(sK10))),X3) | sP6(X3,sK9,k2_funct_1(sK10)) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)) )),
% 2.18/0.68    inference(superposition,[],[f563,f234])).
% 2.18/0.68  fof(f563,plain,(
% 2.18/0.68    ( ! [X0,X1] : (~r2_hidden(k1_funct_1(k2_funct_1(X0),sK14(k2_relat_1(X0),X1,k2_funct_1(X0))),X1) | sP6(X1,k2_relat_1(X0),k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f562,f95])).
% 2.18/0.68  fof(f562,plain,(
% 2.18/0.68    ( ! [X0,X1] : (~r2_hidden(k1_funct_1(k2_funct_1(X0),sK14(k2_relat_1(X0),X1,k2_funct_1(X0))),X1) | sP6(X1,k2_relat_1(X0),k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f515,f96])).
% 2.18/0.68  fof(f515,plain,(
% 2.18/0.68    ( ! [X0,X1] : (~r2_hidden(k1_funct_1(k2_funct_1(X0),sK14(k2_relat_1(X0),X1,k2_funct_1(X0))),X1) | sP6(X1,k2_relat_1(X0),k2_funct_1(X0)) | ~v1_funct_1(k2_funct_1(X0)) | ~v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(superposition,[],[f143,f97])).
% 2.18/0.68  fof(f143,plain,(
% 2.18/0.68    ( ! [X2,X1] : (~r2_hidden(k1_funct_1(X2,sK14(k1_relat_1(X2),X1,X2)),X1) | sP6(X1,k1_relat_1(X2),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.18/0.68    inference(equality_resolution,[],[f127])).
% 2.18/0.68  fof(f127,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (sP6(X1,X0,X2) | ~r2_hidden(k1_funct_1(X2,sK14(X0,X1,X2)),X1) | k1_relat_1(X2) != X0 | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f73])).
% 2.18/0.68  fof(f1526,plain,(
% 2.18/0.68    spl15_67 | ~spl15_64 | ~spl15_66),
% 2.18/0.68    inference(avatar_split_clause,[],[f1525,f1474,f1441,f1478])).
% 2.18/0.68  fof(f1441,plain,(
% 2.18/0.68    spl15_64 <=> sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10))),
% 2.18/0.68    introduced(avatar_definition,[new_symbols(naming,[spl15_64])])).
% 2.18/0.68  fof(f1474,plain,(
% 2.18/0.68    spl15_66 <=> r1_tarski(sK8,k2_relat_1(k2_funct_1(sK10)))),
% 2.18/0.68    introduced(avatar_definition,[new_symbols(naming,[spl15_66])])).
% 2.18/0.68  fof(f1525,plain,(
% 2.18/0.68    sK8 = k2_relat_1(k2_funct_1(sK10)) | (~spl15_64 | ~spl15_66)),
% 2.18/0.68    inference(subsumption_resolution,[],[f1522,f1464])).
% 2.18/0.68  fof(f1464,plain,(
% 2.18/0.68    r1_tarski(k2_relat_1(k2_funct_1(sK10)),sK8) | ~spl15_64),
% 2.18/0.68    inference(resolution,[],[f1443,f361])).
% 2.18/0.68  fof(f1443,plain,(
% 2.18/0.68    sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10)) | ~spl15_64),
% 2.18/0.68    inference(avatar_component_clause,[],[f1441])).
% 2.18/0.68  fof(f1522,plain,(
% 2.18/0.68    sK8 = k2_relat_1(k2_funct_1(sK10)) | ~r1_tarski(k2_relat_1(k2_funct_1(sK10)),sK8) | ~spl15_66),
% 2.18/0.68    inference(resolution,[],[f1475,f109])).
% 2.18/0.68  fof(f1475,plain,(
% 2.18/0.68    r1_tarski(sK8,k2_relat_1(k2_funct_1(sK10))) | ~spl15_66),
% 2.18/0.68    inference(avatar_component_clause,[],[f1474])).
% 2.18/0.68  fof(f1499,plain,(
% 2.18/0.68    ~spl15_44 | spl15_66),
% 2.18/0.68    inference(avatar_contradiction_clause,[],[f1498])).
% 2.18/0.68  fof(f1498,plain,(
% 2.18/0.68    $false | (~spl15_44 | spl15_66)),
% 2.18/0.68    inference(subsumption_resolution,[],[f1497,f137])).
% 2.18/0.68  fof(f137,plain,(
% 2.18/0.68    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.18/0.68    inference(equality_resolution,[],[f108])).
% 2.18/0.68  fof(f108,plain,(
% 2.18/0.68    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.18/0.68    inference(cnf_transformation,[],[f63])).
% 2.18/0.68  fof(f1497,plain,(
% 2.18/0.68    ~r1_tarski(sK8,sK8) | (~spl15_44 | spl15_66)),
% 2.18/0.68    inference(forward_demodulation,[],[f1496,f1041])).
% 2.18/0.68  fof(f1496,plain,(
% 2.18/0.68    ~r1_tarski(sK8,k1_relat_1(sK10)) | spl15_66),
% 2.18/0.68    inference(subsumption_resolution,[],[f1495,f154])).
% 2.18/0.68  fof(f1495,plain,(
% 2.18/0.68    ~r1_tarski(sK8,k1_relat_1(sK10)) | ~v1_relat_1(sK10) | spl15_66),
% 2.18/0.68    inference(subsumption_resolution,[],[f1494,f75])).
% 2.18/0.68  fof(f1494,plain,(
% 2.18/0.68    ~r1_tarski(sK8,k1_relat_1(sK10)) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | spl15_66),
% 2.18/0.68    inference(subsumption_resolution,[],[f1493,f82])).
% 2.18/0.68  fof(f1493,plain,(
% 2.18/0.68    ~r1_tarski(sK8,k1_relat_1(sK10)) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10) | spl15_66),
% 2.18/0.68    inference(superposition,[],[f1476,f98])).
% 2.18/0.68  fof(f1476,plain,(
% 2.18/0.68    ~r1_tarski(sK8,k2_relat_1(k2_funct_1(sK10))) | spl15_66),
% 2.18/0.68    inference(avatar_component_clause,[],[f1474])).
% 2.18/0.68  fof(f1453,plain,(
% 2.18/0.68    spl15_64 | spl15_65),
% 2.18/0.68    inference(avatar_split_clause,[],[f1452,f1445,f1441])).
% 2.18/0.68  fof(f1445,plain,(
% 2.18/0.68    spl15_65 <=> r2_hidden(sK14(k1_relat_1(k2_funct_1(sK10)),sK8,k2_funct_1(sK10)),k1_relat_1(k2_funct_1(sK10)))),
% 2.18/0.68    introduced(avatar_definition,[new_symbols(naming,[spl15_65])])).
% 2.18/0.68  fof(f1452,plain,(
% 2.18/0.68    sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10)) | spl15_65),
% 2.18/0.68    inference(subsumption_resolution,[],[f1451,f618])).
% 2.18/0.68  fof(f618,plain,(
% 2.18/0.68    v1_relat_1(k2_funct_1(sK10))),
% 2.18/0.68    inference(resolution,[],[f601,f215])).
% 2.18/0.68  fof(f215,plain,(
% 2.18/0.68    ( ! [X6,X8,X7] : (~sP7(X6,X7,X8) | v1_relat_1(k2_funct_1(X8))) )),
% 2.18/0.68    inference(subsumption_resolution,[],[f213,f105])).
% 2.18/0.68  fof(f213,plain,(
% 2.18/0.68    ( ! [X6,X8,X7] : (~sP7(X6,X7,X8) | v1_relat_1(k2_funct_1(X8)) | ~v1_relat_1(k2_zfmisc_1(X7,X6))) )),
% 2.18/0.68    inference(resolution,[],[f130,f90])).
% 2.18/0.68  fof(f130,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~sP7(X0,X1,X2)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f74])).
% 2.18/0.68  fof(f74,plain,(
% 2.18/0.68    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP7(X0,X1,X2))),
% 2.18/0.68    inference(nnf_transformation,[],[f51])).
% 2.18/0.68  fof(f51,plain,(
% 2.18/0.68    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | ~sP7(X0,X1,X2))),
% 2.18/0.68    introduced(predicate_definition_introduction,[new_symbols(naming,[sP7])])).
% 2.18/0.68  fof(f601,plain,(
% 2.18/0.68    sP7(sK8,sK9,sK10)),
% 2.18/0.68    inference(subsumption_resolution,[],[f600,f75])).
% 2.18/0.68  fof(f600,plain,(
% 2.18/0.68    sP7(sK8,sK9,sK10) | ~v1_funct_1(sK10)),
% 2.18/0.68    inference(subsumption_resolution,[],[f599,f76])).
% 2.18/0.68  fof(f76,plain,(
% 2.18/0.68    v1_funct_2(sK10,sK8,sK9)),
% 2.18/0.68    inference(cnf_transformation,[],[f55])).
% 2.18/0.68  fof(f599,plain,(
% 2.18/0.68    sP7(sK8,sK9,sK10) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10)),
% 2.18/0.68    inference(subsumption_resolution,[],[f598,f82])).
% 2.18/0.68  fof(f598,plain,(
% 2.18/0.68    ~v2_funct_1(sK10) | sP7(sK8,sK9,sK10) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10)),
% 2.18/0.68    inference(subsumption_resolution,[],[f584,f81])).
% 2.18/0.68  fof(f584,plain,(
% 2.18/0.68    sK9 != k2_relset_1(sK8,sK9,sK10) | ~v2_funct_1(sK10) | sP7(sK8,sK9,sK10) | ~v1_funct_2(sK10,sK8,sK9) | ~v1_funct_1(sK10)),
% 2.18/0.68    inference(resolution,[],[f131,f77])).
% 2.18/0.68  fof(f131,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | sP7(X0,X1,X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f52])).
% 2.18/0.68  fof(f52,plain,(
% 2.18/0.68    ! [X0,X1,X2] : (sP7(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.18/0.68    inference(definition_folding,[],[f39,f51])).
% 2.18/0.68  fof(f39,plain,(
% 2.18/0.68    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.18/0.68    inference(flattening,[],[f38])).
% 2.18/0.68  fof(f38,plain,(
% 2.18/0.68    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.18/0.68    inference(ennf_transformation,[],[f13])).
% 2.18/0.68  fof(f13,axiom,(
% 2.18/0.68    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 2.18/0.68  fof(f1451,plain,(
% 2.18/0.68    sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10)) | ~v1_relat_1(k2_funct_1(sK10)) | spl15_65),
% 2.18/0.68    inference(subsumption_resolution,[],[f1449,f619])).
% 2.18/0.68  fof(f619,plain,(
% 2.18/0.68    v1_funct_1(k2_funct_1(sK10))),
% 2.18/0.68    inference(resolution,[],[f601,f128])).
% 2.18/0.68  fof(f128,plain,(
% 2.18/0.68    ( ! [X2,X0,X1] : (~sP7(X0,X1,X2) | v1_funct_1(k2_funct_1(X2))) )),
% 2.18/0.68    inference(cnf_transformation,[],[f74])).
% 2.18/0.68  fof(f1449,plain,(
% 2.18/0.68    sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10)) | ~v1_funct_1(k2_funct_1(sK10)) | ~v1_relat_1(k2_funct_1(sK10)) | spl15_65),
% 2.18/0.68    inference(resolution,[],[f1447,f144])).
% 2.18/0.68  fof(f1447,plain,(
% 2.18/0.68    ~r2_hidden(sK14(k1_relat_1(k2_funct_1(sK10)),sK8,k2_funct_1(sK10)),k1_relat_1(k2_funct_1(sK10))) | spl15_65),
% 2.18/0.68    inference(avatar_component_clause,[],[f1445])).
% 2.18/0.68  fof(f1448,plain,(
% 2.18/0.68    spl15_64 | ~spl15_65 | ~spl15_44),
% 2.18/0.68    inference(avatar_split_clause,[],[f1439,f1039,f1445,f1441])).
% 2.18/0.68  fof(f1439,plain,(
% 2.18/0.68    ~r2_hidden(sK14(k1_relat_1(k2_funct_1(sK10)),sK8,k2_funct_1(sK10)),k1_relat_1(k2_funct_1(sK10))) | sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10)) | ~spl15_44),
% 2.18/0.68    inference(subsumption_resolution,[],[f1438,f618])).
% 2.18/0.68  fof(f1438,plain,(
% 2.18/0.68    ~r2_hidden(sK14(k1_relat_1(k2_funct_1(sK10)),sK8,k2_funct_1(sK10)),k1_relat_1(k2_funct_1(sK10))) | sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10)) | ~v1_relat_1(k2_funct_1(sK10)) | ~spl15_44),
% 2.18/0.68    inference(subsumption_resolution,[],[f1437,f619])).
% 2.18/0.68  fof(f1437,plain,(
% 2.18/0.68    ~r2_hidden(sK14(k1_relat_1(k2_funct_1(sK10)),sK8,k2_funct_1(sK10)),k1_relat_1(k2_funct_1(sK10))) | sP6(sK8,k1_relat_1(k2_funct_1(sK10)),k2_funct_1(sK10)) | ~v1_funct_1(k2_funct_1(sK10)) | ~v1_relat_1(k2_funct_1(sK10)) | ~spl15_44),
% 2.18/0.68    inference(resolution,[],[f1436,f143])).
% 2.18/0.68  fof(f1238,plain,(
% 2.18/0.68    ~spl15_47),
% 2.18/0.68    inference(avatar_contradiction_clause,[],[f1237])).
% 2.18/0.68  fof(f1237,plain,(
% 2.18/0.68    $false | ~spl15_47),
% 2.18/0.68    inference(subsumption_resolution,[],[f1236,f87])).
% 2.18/0.68  fof(f87,plain,(
% 2.18/0.68    k1_xboole_0 != sK8),
% 2.18/0.68    inference(cnf_transformation,[],[f55])).
% 2.18/0.68  fof(f1236,plain,(
% 2.18/0.68    k1_xboole_0 = sK8 | ~spl15_47),
% 2.18/0.68    inference(resolution,[],[f1055,f119])).
% 2.18/0.68  fof(f1055,plain,(
% 2.18/0.68    sP3(sK9,sK8) | ~spl15_47),
% 2.18/0.68    inference(avatar_component_clause,[],[f1053])).
% 2.18/0.68  fof(f1056,plain,(
% 2.18/0.68    spl15_46 | spl15_47),
% 2.18/0.68    inference(avatar_split_clause,[],[f1047,f1053,f1049])).
% 2.18/0.68  fof(f1047,plain,(
% 2.18/0.68    sP3(sK9,sK8) | sK9 = k1_relat_1(sK11)),
% 2.18/0.68    inference(subsumption_resolution,[],[f1029,f79])).
% 2.18/0.68  fof(f79,plain,(
% 2.18/0.68    v1_funct_2(sK11,sK9,sK8)),
% 2.18/0.68    inference(cnf_transformation,[],[f55])).
% 2.18/0.68  fof(f1029,plain,(
% 2.18/0.68    ~v1_funct_2(sK11,sK9,sK8) | sP3(sK9,sK8) | sK9 = k1_relat_1(sK11)),
% 2.18/0.68    inference(resolution,[],[f418,f80])).
% 2.18/0.68  fof(f1046,plain,(
% 2.18/0.68    spl15_44 | spl15_45),
% 2.18/0.68    inference(avatar_split_clause,[],[f1037,f1043,f1039])).
% 2.18/0.68  fof(f1037,plain,(
% 2.18/0.68    sP3(sK8,sK9) | sK8 = k1_relat_1(sK10)),
% 2.18/0.68    inference(subsumption_resolution,[],[f1027,f76])).
% 2.18/0.68  fof(f1027,plain,(
% 2.18/0.68    ~v1_funct_2(sK10,sK8,sK9) | sP3(sK8,sK9) | sK8 = k1_relat_1(sK10)),
% 2.18/0.68    inference(resolution,[],[f418,f77])).
% 2.18/0.68  fof(f892,plain,(
% 2.18/0.68    spl15_42),
% 2.18/0.68    inference(avatar_contradiction_clause,[],[f891])).
% 2.18/0.68  fof(f891,plain,(
% 2.18/0.68    $false | spl15_42),
% 2.18/0.68    inference(subsumption_resolution,[],[f890,f618])).
% 2.18/0.68  fof(f890,plain,(
% 2.18/0.68    ~v1_relat_1(k2_funct_1(sK10)) | spl15_42),
% 2.18/0.68    inference(subsumption_resolution,[],[f889,f619])).
% 2.18/0.68  fof(f889,plain,(
% 2.18/0.68    ~v1_funct_1(k2_funct_1(sK10)) | ~v1_relat_1(k2_funct_1(sK10)) | spl15_42),
% 2.18/0.68    inference(resolution,[],[f861,f94])).
% 2.18/0.68  fof(f94,plain,(
% 2.18/0.68    ( ! [X0] : (sP0(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f41])).
% 2.18/0.68  fof(f41,plain,(
% 2.18/0.68    ! [X0] : (sP0(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/0.68    inference(definition_folding,[],[f22,f40])).
% 2.18/0.68  fof(f22,plain,(
% 2.18/0.68    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.18/0.68    inference(flattening,[],[f21])).
% 2.18/0.68  fof(f21,plain,(
% 2.18/0.68    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.18/0.68    inference(ennf_transformation,[],[f14])).
% 2.18/0.68  fof(f14,axiom,(
% 2.18/0.68    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 2.18/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 2.18/0.68  fof(f861,plain,(
% 2.18/0.68    ~sP0(k2_funct_1(sK10)) | spl15_42),
% 2.18/0.68    inference(avatar_component_clause,[],[f859])).
% 2.18/0.68  fof(f884,plain,(
% 2.18/0.68    ~spl15_42 | spl15_43),
% 2.18/0.68    inference(avatar_split_clause,[],[f879,f881,f859])).
% 2.18/0.68  fof(f879,plain,(
% 2.18/0.68    v1_funct_2(k2_funct_1(sK10),sK9,k2_relat_1(k2_funct_1(sK10))) | ~sP0(k2_funct_1(sK10))),
% 2.18/0.68    inference(subsumption_resolution,[],[f878,f154])).
% 2.18/0.68  fof(f878,plain,(
% 2.18/0.68    v1_funct_2(k2_funct_1(sK10),sK9,k2_relat_1(k2_funct_1(sK10))) | ~sP0(k2_funct_1(sK10)) | ~v1_relat_1(sK10)),
% 2.18/0.68    inference(subsumption_resolution,[],[f877,f75])).
% 2.18/0.68  fof(f877,plain,(
% 2.18/0.68    v1_funct_2(k2_funct_1(sK10),sK9,k2_relat_1(k2_funct_1(sK10))) | ~sP0(k2_funct_1(sK10)) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)),
% 2.18/0.68    inference(subsumption_resolution,[],[f865,f82])).
% 2.18/0.68  fof(f865,plain,(
% 2.18/0.68    v1_funct_2(k2_funct_1(sK10),sK9,k2_relat_1(k2_funct_1(sK10))) | ~sP0(k2_funct_1(sK10)) | ~v2_funct_1(sK10) | ~v1_funct_1(sK10) | ~v1_relat_1(sK10)),
% 2.18/0.68    inference(superposition,[],[f220,f234])).
% 2.18/0.68  fof(f220,plain,(
% 2.18/0.68    ( ! [X0] : (v1_funct_2(k2_funct_1(X0),k2_relat_1(X0),k2_relat_1(k2_funct_1(X0))) | ~sP0(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.18/0.68    inference(superposition,[],[f92,f97])).
% 2.18/0.68  fof(f92,plain,(
% 2.18/0.68    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~sP0(X0)) )),
% 2.18/0.68    inference(cnf_transformation,[],[f56])).
% 2.18/0.68  % SZS output end Proof for theBenchmark
% 2.18/0.68  % (8880)------------------------------
% 2.18/0.68  % (8880)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.18/0.68  % (8880)Termination reason: Refutation
% 2.18/0.68  
% 2.18/0.68  % (8880)Memory used [KB]: 7419
% 2.18/0.68  % (8880)Time elapsed: 0.255 s
% 2.18/0.68  % (8880)------------------------------
% 2.18/0.68  % (8880)------------------------------
% 2.18/0.68  % (8875)Success in time 0.326 s
%------------------------------------------------------------------------------
