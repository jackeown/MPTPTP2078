%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :  272 (1437 expanded)
%              Number of leaves         :   40 ( 648 expanded)
%              Depth                    :   30
%              Number of atoms          : 1374 (18863 expanded)
%              Number of equality atoms :  173 (4068 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1189,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f368,f384,f389,f402,f555,f671,f694,f735,f752,f1024,f1041,f1051,f1188])).

fof(f1188,plain,
    ( spl10_3
    | ~ spl10_56 ),
    inference(avatar_contradiction_clause,[],[f1187])).

fof(f1187,plain,
    ( $false
    | spl10_3
    | ~ spl10_56 ),
    inference(subsumption_resolution,[],[f1186,f1044])).

fof(f1044,plain,
    ( sP0(sK8,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,sK7)
    | ~ spl10_56 ),
    inference(resolution,[],[f1019,f113])).

fof(f113,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,k1_tmap_1(X1,X3,X2,X5,X0,X6),X5,X6)
      | sP0(X6,X5,k1_tmap_1(X1,X3,X2,X5,X0,X6),X3,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0)
      | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( ( k1_tmap_1(X1,X3,X2,X5,X0,X6) = X4
          | ~ sP0(X6,X5,X4,X3,X2,X1,X0) )
        & ( sP0(X6,X5,X4,X3,X2,X1,X0)
          | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4 ) )
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(rectify,[],[f52])).

fof(f52,plain,(
    ! [X4,X0,X2,X1,X6,X3,X5] :
      ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
          | ~ sP0(X5,X3,X6,X1,X2,X0,X4) )
        & ( sP0(X5,X3,X6,X1,X2,X0,X4)
          | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
      | ~ sP1(X4,X0,X2,X1,X6,X3,X5) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X4,X0,X2,X1,X6,X3,X5] :
      ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
      <=> sP0(X5,X3,X6,X1,X2,X0,X4) )
      | ~ sP1(X4,X0,X2,X1,X6,X3,X5) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f1019,plain,
    ( sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8)
    | ~ spl10_56 ),
    inference(avatar_component_clause,[],[f1017])).

fof(f1017,plain,
    ( spl10_56
  <=> sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).

fof(f1186,plain,
    ( ~ sP0(sK8,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,sK7)
    | spl10_3
    | ~ spl10_56 ),
    inference(resolution,[],[f1145,f1019])).

fof(f1145,plain,
    ( ! [X0] :
        ( ~ sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)
        | ~ sP0(sK8,sK6,X0,sK4,sK5,sK3,sK7) )
    | spl10_3 ),
    inference(subsumption_resolution,[],[f1142,f85])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) != X0
        | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) != X6 )
      & ( ( k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0
          & k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6 )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f55])).

fof(f55,plain,(
    ! [X5,X3,X6,X1,X2,X0,X4] :
      ( ( sP0(X5,X3,X6,X1,X2,X0,X4)
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
      & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
          & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
        | ~ sP0(X5,X3,X6,X1,X2,X0,X4) ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X5,X3,X6,X1,X2,X0,X4] :
      ( ( sP0(X5,X3,X6,X1,X2,X0,X4)
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
      & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
          & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
        | ~ sP0(X5,X3,X6,X1,X2,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X5,X3,X6,X1,X2,X0,X4] :
      ( sP0(X5,X3,X6,X1,X2,X0,X4)
    <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
        & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1142,plain,
    ( ! [X0] :
        ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,X0,sK6)
        | ~ sP0(sK8,sK6,X0,sK4,sK5,sK3,sK7)
        | ~ sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) )
    | spl10_3 ),
    inference(superposition,[],[f129,f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k1_tmap_1(X1,X3,X2,X5,X0,X6) = X4
      | ~ sP0(X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f129,plain,
    ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl10_3
  <=> sK8 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f1051,plain,
    ( spl10_2
    | ~ spl10_56 ),
    inference(avatar_contradiction_clause,[],[f1050])).

fof(f1050,plain,
    ( $false
    | spl10_2
    | ~ spl10_56 ),
    inference(trivial_inequality_removal,[],[f1046])).

fof(f1046,plain,
    ( sK7 != sK7
    | spl10_2
    | ~ spl10_56 ),
    inference(resolution,[],[f1044,f408])).

fof(f408,plain,
    ( ! [X0,X1] :
        ( ~ sP0(X1,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,X0)
        | sK7 != X0 )
    | spl10_2 ),
    inference(superposition,[],[f125,f84])).

fof(f84,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f125,plain,
    ( sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl10_2
  <=> sK7 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f1041,plain,(
    spl10_57 ),
    inference(avatar_contradiction_clause,[],[f1040])).

fof(f1040,plain,
    ( $false
    | spl10_57 ),
    inference(subsumption_resolution,[],[f1039,f68])).

fof(f68,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)
      | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)
      | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) )
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    & v1_funct_2(sK8,sK6,sK4)
    & v1_funct_1(sK8)
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    & v1_funct_2(sK7,sK5,sK4)
    & v1_funct_1(sK7)
    & r1_subset_1(sK5,sK6)
    & m1_subset_1(sK6,k1_zfmisc_1(sK3))
    & ~ v1_xboole_0(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(sK3))
    & ~ v1_xboole_0(sK5)
    & ~ v1_xboole_0(sK4)
    & ~ v1_xboole_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f21,f50,f49,f48,f47,f46,f45])).

fof(f45,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                              | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                    & r1_subset_1(X2,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK3,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK3))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK3))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,X1,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK3,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X5,X3,X1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                    & v1_funct_2(X4,X2,X1)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(sK3))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(sK3))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X3) != X5
                        | k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X2) != X4
                        | k2_partfun1(X2,sK4,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,X2,X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4)))
                      & v1_funct_2(X5,X3,sK4)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK4)))
                  & v1_funct_2(X4,X2,sK4)
                  & v1_funct_1(X4) )
              & r1_subset_1(X2,X3)
              & m1_subset_1(X3,k1_zfmisc_1(sK3))
              & ~ v1_xboole_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(sK3))
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X2) != X4
                      | k2_partfun1(X2,sK4,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,X2,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4)))
                    & v1_funct_2(X5,X3,sK4)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK4)))
                & v1_funct_2(X4,X2,sK4)
                & v1_funct_1(X4) )
            & r1_subset_1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(sK3))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(sK3))
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),X3) != X5
                    | k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),sK5) != X4
                    | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,sK5,X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4)))
                  & v1_funct_2(X5,X3,sK4)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
              & v1_funct_2(X4,sK5,sK4)
              & v1_funct_1(X4) )
          & r1_subset_1(sK5,X3)
          & m1_subset_1(X3,k1_zfmisc_1(sK3))
          & ~ v1_xboole_0(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(sK3))
      & ~ v1_xboole_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),X3) != X5
                  | k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),sK5) != X4
                  | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,sK5,X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4)))
                & v1_funct_2(X5,X3,sK4)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
            & v1_funct_2(X4,sK5,sK4)
            & v1_funct_1(X4) )
        & r1_subset_1(sK5,X3)
        & m1_subset_1(X3,k1_zfmisc_1(sK3))
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK6) != X5
                | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK5) != X4
                | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
              & v1_funct_2(X5,sK6,sK4)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
          & v1_funct_2(X4,sK5,sK4)
          & v1_funct_1(X4) )
      & r1_subset_1(sK5,sK6)
      & m1_subset_1(sK6,k1_zfmisc_1(sK3))
      & ~ v1_xboole_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK6) != X5
              | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK5) != X4
              | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
            & v1_funct_2(X5,sK6,sK4)
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        & v1_funct_2(X4,sK5,sK4)
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK6) != X5
            | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK5)
            | k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
          & v1_funct_2(X5,sK6,sK4)
          & v1_funct_1(X5) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
      & v1_funct_2(sK7,sK5,sK4)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

% (22620)Refutation not found, incomplete strategy% (22620)------------------------------
% (22620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f50,plain,
    ( ? [X5] :
        ( ( k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK6) != X5
          | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK5)
          | k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
        & v1_funct_2(X5,sK6,sK4)
        & v1_funct_1(X5) )
   => ( ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)
        | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)
        | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
      & v1_funct_2(sK8,sK6,sK4)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                      & ~ v1_xboole_0(X3) )
                   => ( r1_subset_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                            & v1_funct_2(X4,X2,X1)
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                                & v1_funct_2(X5,X3,X1)
                                & v1_funct_1(X5) )
                             => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                                & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                                & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ( r1_subset_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                          & v1_funct_2(X4,X2,X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                              & v1_funct_2(X5,X3,X1)
                              & v1_funct_1(X5) )
                           => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                              & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                              & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f1039,plain,
    ( v1_xboole_0(sK4)
    | spl10_57 ),
    inference(subsumption_resolution,[],[f1038,f69])).

fof(f69,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f51])).

fof(f1038,plain,
    ( v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_57 ),
    inference(subsumption_resolution,[],[f1037,f70])).

fof(f70,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f1037,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_57 ),
    inference(subsumption_resolution,[],[f1036,f71])).

fof(f71,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f1036,plain,
    ( v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_57 ),
    inference(subsumption_resolution,[],[f1035,f72])).

fof(f72,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f51])).

fof(f1035,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_57 ),
    inference(subsumption_resolution,[],[f1034,f74])).

fof(f74,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f51])).

fof(f1034,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_57 ),
    inference(subsumption_resolution,[],[f1033,f75])).

fof(f75,plain,(
    v1_funct_2(sK7,sK5,sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f1033,plain,
    ( ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_57 ),
    inference(subsumption_resolution,[],[f1032,f76])).

fof(f76,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f51])).

fof(f1032,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_57 ),
    inference(subsumption_resolution,[],[f1031,f77])).

fof(f77,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f51])).

fof(f1031,plain,
    ( ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_57 ),
    inference(subsumption_resolution,[],[f1030,f78])).

fof(f78,plain,(
    v1_funct_2(sK8,sK6,sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f1030,plain,
    ( ~ v1_funct_2(sK8,sK6,sK4)
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_57 ),
    inference(subsumption_resolution,[],[f1029,f79])).

fof(f79,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f51])).

fof(f1029,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_2(sK8,sK6,sK4)
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_57 ),
    inference(resolution,[],[f1027,f621])).

fof(f621,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP2(X1,X3,X2,X0,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f112,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( sP2(X1,X3,X2,X0,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( sP2(X1,X3,X2,X0,X5,X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f39,f43])).

fof(f43,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP2(X1,X3,X2,X0,X5,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f39,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(X5,X3,X1)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(X4,X2,X1)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f1027,plain,
    ( ~ sP2(sK4,sK6,sK5,sK3,sK8,sK7)
    | spl10_57 ),
    inference(resolution,[],[f1023,f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0)
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0)))
        & v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0)
        & v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4)) )
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f65])).

fof(f65,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP2(X1,X3,X2,X0,X5,X4) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f1023,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)
    | spl10_57 ),
    inference(avatar_component_clause,[],[f1021])).

fof(f1021,plain,
    ( spl10_57
  <=> v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).

fof(f1024,plain,
    ( spl10_56
    | ~ spl10_57
    | ~ spl10_1
    | ~ spl10_26
    | ~ spl10_27
    | ~ spl10_41 ),
    inference(avatar_split_clause,[],[f1015,f656,f415,f411,f119,f1021,f1017])).

fof(f119,plain,
    ( spl10_1
  <=> k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f411,plain,
    ( spl10_26
  <=> v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f415,plain,
    ( spl10_27
  <=> m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f656,plain,
    ( spl10_41
  <=> k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).

fof(f1015,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)
    | sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8)
    | ~ spl10_1
    | ~ spl10_26
    | ~ spl10_27
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f1012,f412])).

fof(f412,plain,
    ( v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f411])).

fof(f1012,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)
    | ~ v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))
    | sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8)
    | ~ spl10_1
    | ~ spl10_27
    | ~ spl10_41 ),
    inference(resolution,[],[f1011,f416])).

fof(f416,plain,
    ( m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f415])).

fof(f1011,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X0)
        | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) )
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f1010,f74])).

fof(f1010,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X0)
        | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)
        | ~ v1_funct_1(sK7) )
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f1009,f75])).

fof(f1009,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X0)
        | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)
        | ~ v1_funct_2(sK7,sK5,sK4)
        | ~ v1_funct_1(sK7) )
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f1007,f76])).

fof(f1007,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X0)
        | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(sK7,sK5,sK4)
        | ~ v1_funct_1(sK7) )
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(trivial_inequality_removal,[],[f1004])).

fof(f1004,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X0)
        | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(sK7,sK5,sK4)
        | ~ v1_funct_1(sK7) )
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(superposition,[],[f829,f718])).

fof(f718,plain,
    ( k1_xboole_0 = k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(forward_demodulation,[],[f440,f695])).

fof(f695,plain,
    ( k1_xboole_0 = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(backward_demodulation,[],[f635,f658])).

fof(f658,plain,
    ( k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_41 ),
    inference(avatar_component_clause,[],[f656])).

fof(f635,plain,
    ( k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f634,f74])).

fof(f634,plain,
    ( k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ v1_funct_1(sK7)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f630,f76])).

fof(f630,plain,
    ( k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(sK7)
    | ~ spl10_1 ),
    inference(superposition,[],[f438,f108])).

fof(f108,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f438,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f437,f77])).

fof(f437,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ v1_funct_1(sK8)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f434,f79])).

fof(f434,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | ~ spl10_1 ),
    inference(superposition,[],[f120,f108])).

fof(f120,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f440,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f439,f77])).

fof(f439,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ v1_funct_1(sK8)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f435,f79])).

fof(f435,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | ~ spl10_1 ),
    inference(superposition,[],[f108,f120])).

fof(f829,plain,
    ( ! [X8,X7] :
        ( k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X8)
        | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(X7,sK5,sK4)
        | ~ v1_funct_1(X7) )
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f828,f68])).

fof(f828,plain,
    ( ! [X8,X7] :
        ( k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X8)
        | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(X7,sK5,sK4)
        | ~ v1_funct_1(X7)
        | v1_xboole_0(sK4) )
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f827,f69])).

fof(f827,plain,
    ( ! [X8,X7] :
        ( k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X8)
        | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(X7,sK5,sK4)
        | ~ v1_funct_1(X7)
        | v1_xboole_0(sK5)
        | v1_xboole_0(sK4) )
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f826,f70])).

fof(f826,plain,
    ( ! [X8,X7] :
        ( k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X8)
        | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(X7,sK5,sK4)
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
        | v1_xboole_0(sK5)
        | v1_xboole_0(sK4) )
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f825,f71])).

fof(f825,plain,
    ( ! [X8,X7] :
        ( k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X8)
        | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(X7,sK5,sK4)
        | ~ v1_funct_1(X7)
        | v1_xboole_0(sK6)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
        | v1_xboole_0(sK5)
        | v1_xboole_0(sK4) )
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f824,f72])).

fof(f824,plain,
    ( ! [X8,X7] :
        ( k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X8)
        | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(X7,sK5,sK4)
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
        | v1_xboole_0(sK6)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
        | v1_xboole_0(sK5)
        | v1_xboole_0(sK4) )
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f823,f77])).

fof(f823,plain,
    ( ! [X8,X7] :
        ( k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X8)
        | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8)
        | ~ v1_funct_1(sK8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(X7,sK5,sK4)
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
        | v1_xboole_0(sK6)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
        | v1_xboole_0(sK5)
        | v1_xboole_0(sK4) )
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f822,f78])).

fof(f822,plain,
    ( ! [X8,X7] :
        ( k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X8)
        | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8)
        | ~ v1_funct_2(sK8,sK6,sK4)
        | ~ v1_funct_1(sK8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(X7,sK5,sK4)
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
        | v1_xboole_0(sK6)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
        | v1_xboole_0(sK5)
        | v1_xboole_0(sK4) )
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(subsumption_resolution,[],[f816,f79])).

fof(f816,plain,
    ( ! [X8,X7] :
        ( k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X8)
        | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8)
        | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
        | ~ v1_funct_2(sK8,sK6,sK4)
        | ~ v1_funct_1(sK8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(X7,sK5,sK4)
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
        | v1_xboole_0(sK6)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
        | v1_xboole_0(sK5)
        | v1_xboole_0(sK4) )
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(superposition,[],[f777,f713])).

fof(f713,plain,
    ( k1_xboole_0 = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1
    | ~ spl10_41 ),
    inference(forward_demodulation,[],[f641,f658])).

fof(f641,plain,
    ( k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(backward_demodulation,[],[f628,f635])).

fof(f628,plain,
    ( k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(backward_demodulation,[],[f120,f438])).

fof(f777,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | sP1(X4,X0,X2,X1,X6,X3,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1) ) ),
    inference(subsumption_resolution,[],[f87,f88])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP1(X4,X0,X2,X1,X6,X3,X5)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( sP1(X4,X0,X2,X1,X6,X3,X5)
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(definition_folding,[],[f23,f41,f40])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                         => ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                                  & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                                  & v1_funct_1(X6) )
                               => ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f752,plain,(
    spl10_27 ),
    inference(avatar_contradiction_clause,[],[f751])).

fof(f751,plain,
    ( $false
    | spl10_27 ),
    inference(subsumption_resolution,[],[f750,f68])).

fof(f750,plain,
    ( v1_xboole_0(sK4)
    | spl10_27 ),
    inference(subsumption_resolution,[],[f749,f69])).

fof(f749,plain,
    ( v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_27 ),
    inference(subsumption_resolution,[],[f748,f70])).

fof(f748,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_27 ),
    inference(subsumption_resolution,[],[f747,f71])).

fof(f747,plain,
    ( v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_27 ),
    inference(subsumption_resolution,[],[f746,f72])).

fof(f746,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_27 ),
    inference(subsumption_resolution,[],[f745,f74])).

fof(f745,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_27 ),
    inference(subsumption_resolution,[],[f744,f75])).

fof(f744,plain,
    ( ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_27 ),
    inference(subsumption_resolution,[],[f743,f76])).

fof(f743,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_27 ),
    inference(subsumption_resolution,[],[f742,f77])).

fof(f742,plain,
    ( ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_27 ),
    inference(subsumption_resolution,[],[f741,f78])).

fof(f741,plain,
    ( ~ v1_funct_2(sK8,sK6,sK4)
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_27 ),
    inference(subsumption_resolution,[],[f740,f79])).

fof(f740,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_2(sK8,sK6,sK4)
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_27 ),
    inference(resolution,[],[f737,f621])).

fof(f737,plain,
    ( ~ sP2(sK4,sK6,sK5,sK3,sK8,sK7)
    | spl10_27 ),
    inference(resolution,[],[f417,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0)))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f417,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
    | spl10_27 ),
    inference(avatar_component_clause,[],[f415])).

fof(f735,plain,(
    spl10_26 ),
    inference(avatar_contradiction_clause,[],[f734])).

fof(f734,plain,
    ( $false
    | spl10_26 ),
    inference(subsumption_resolution,[],[f733,f68])).

fof(f733,plain,
    ( v1_xboole_0(sK4)
    | spl10_26 ),
    inference(subsumption_resolution,[],[f732,f69])).

fof(f732,plain,
    ( v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_26 ),
    inference(subsumption_resolution,[],[f731,f70])).

fof(f731,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_26 ),
    inference(subsumption_resolution,[],[f730,f71])).

fof(f730,plain,
    ( v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_26 ),
    inference(subsumption_resolution,[],[f729,f72])).

fof(f729,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_26 ),
    inference(subsumption_resolution,[],[f728,f74])).

fof(f728,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_26 ),
    inference(subsumption_resolution,[],[f727,f75])).

fof(f727,plain,
    ( ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_26 ),
    inference(subsumption_resolution,[],[f726,f76])).

fof(f726,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_26 ),
    inference(subsumption_resolution,[],[f725,f77])).

fof(f725,plain,
    ( ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_26 ),
    inference(subsumption_resolution,[],[f724,f78])).

fof(f724,plain,
    ( ~ v1_funct_2(sK8,sK6,sK4)
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_26 ),
    inference(subsumption_resolution,[],[f723,f79])).

fof(f723,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_2(sK8,sK6,sK4)
    | ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_26 ),
    inference(resolution,[],[f621,f423])).

fof(f423,plain,
    ( ~ sP2(sK4,sK6,sK5,sK3,sK8,sK7)
    | spl10_26 ),
    inference(resolution,[],[f413,f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f413,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))
    | spl10_26 ),
    inference(avatar_component_clause,[],[f411])).

fof(f694,plain,
    ( spl10_31
    | ~ spl10_40 ),
    inference(avatar_split_clause,[],[f693,f653,f505])).

fof(f505,plain,
    ( spl10_31
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,k3_xboole_0(sK5,sK6))
        | ~ v4_relat_1(sK8,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).

fof(f653,plain,
    ( spl10_40
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,k9_subset_1(sK3,sK5,sK6))
        | ~ v4_relat_1(sK8,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).

fof(f693,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k3_xboole_0(sK5,sK6))
        | ~ v4_relat_1(sK8,X0) )
    | ~ spl10_40 ),
    inference(subsumption_resolution,[],[f682,f72])).

fof(f682,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k3_xboole_0(sK5,sK6))
        | ~ v4_relat_1(sK8,X0)
        | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3)) )
    | ~ spl10_40 ),
    inference(superposition,[],[f654,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f654,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k9_subset_1(sK3,sK5,sK6))
        | ~ v4_relat_1(sK8,X0) )
    | ~ spl10_40 ),
    inference(avatar_component_clause,[],[f653])).

fof(f671,plain,
    ( spl10_40
    | spl10_41
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f670,f119,f656,f653])).

fof(f670,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
        | ~ r1_xboole_0(X0,k9_subset_1(sK3,sK5,sK6))
        | ~ v4_relat_1(sK8,X0) )
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f646,f166])).

fof(f166,plain,(
    v1_relat_1(sK8) ),
    inference(resolution,[],[f106,f79])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f646,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
        | ~ r1_xboole_0(X0,k9_subset_1(sK3,sK5,sK6))
        | ~ v1_relat_1(sK8)
        | ~ v4_relat_1(sK8,X0) )
    | ~ spl10_1 ),
    inference(superposition,[],[f243,f635])).

fof(f243,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f239])).

fof(f239,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ v1_relat_1(X0)
      | ~ v4_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f104,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f555,plain,
    ( spl10_16
    | ~ spl10_31 ),
    inference(avatar_split_clause,[],[f554,f505,f297])).

fof(f297,plain,
    ( spl10_16
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | ~ v4_relat_1(sK8,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f554,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | ~ v4_relat_1(sK8,X0) )
    | ~ spl10_31 ),
    inference(subsumption_resolution,[],[f540,f235])).

fof(f235,plain,(
    r1_xboole_0(sK5,sK6) ),
    inference(resolution,[],[f234,f73])).

fof(f73,plain,(
    r1_subset_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f233,f231])).

fof(f231,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f225,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f25,f57])).

fof(f57,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f225,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f224,f116])).

fof(f116,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f224,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X6,X4)
      | ~ r2_hidden(X5,X6)
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f107,f103])).

fof(f103,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f107,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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

fof(f233,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f94,f232])).

fof(f232,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f225,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f540,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | ~ v4_relat_1(sK8,X0)
        | ~ r1_xboole_0(sK5,sK6) )
    | ~ spl10_31 ),
    inference(superposition,[],[f506,f100])).

fof(f100,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f506,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k3_xboole_0(sK5,sK6))
        | ~ v4_relat_1(sK8,X0) )
    | ~ spl10_31 ),
    inference(avatar_component_clause,[],[f505])).

fof(f402,plain,(
    ~ spl10_22 ),
    inference(avatar_contradiction_clause,[],[f401])).

fof(f401,plain,
    ( $false
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f398,f81])).

fof(f81,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f398,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_22 ),
    inference(resolution,[],[f393,f232])).

fof(f393,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK7),k1_xboole_0)
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f392,f165])).

fof(f165,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f106,f76])).

fof(f392,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK7),k1_xboole_0)
    | ~ v1_relat_1(sK7)
    | ~ spl10_22 ),
    inference(resolution,[],[f334,f176])).

fof(f176,plain,(
    ! [X2] :
      ( v4_relat_1(X2,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(resolution,[],[f93,f116])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f334,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK7,X0)
        | ~ r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f333])).

fof(f333,plain,
    ( spl10_22
  <=> ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | ~ v4_relat_1(sK7,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f389,plain,
    ( spl10_22
    | spl10_17 ),
    inference(avatar_split_clause,[],[f388,f300,f333])).

fof(f300,plain,
    ( spl10_17
  <=> k1_xboole_0 = k7_relat_1(sK7,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f388,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | ~ v4_relat_1(sK7,X0) )
    | spl10_17 ),
    inference(subsumption_resolution,[],[f387,f165])).

fof(f387,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | ~ v1_relat_1(sK7)
        | ~ v4_relat_1(sK7,X0) )
    | spl10_17 ),
    inference(trivial_inequality_removal,[],[f385])).

fof(f385,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ r1_xboole_0(X0,k1_xboole_0)
        | ~ v1_relat_1(sK7)
        | ~ v4_relat_1(sK7,X0) )
    | spl10_17 ),
    inference(superposition,[],[f302,f243])).

fof(f302,plain,
    ( k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0)
    | spl10_17 ),
    inference(avatar_component_clause,[],[f300])).

fof(f384,plain,(
    ~ spl10_16 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f380,f81])).

fof(f380,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ spl10_16 ),
    inference(resolution,[],[f370,f232])).

fof(f370,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK8),k1_xboole_0)
    | ~ spl10_16 ),
    inference(subsumption_resolution,[],[f369,f166])).

fof(f369,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK8),k1_xboole_0)
    | ~ v1_relat_1(sK8)
    | ~ spl10_16 ),
    inference(resolution,[],[f298,f176])).

fof(f298,plain,
    ( ! [X0] :
        ( ~ v4_relat_1(sK8,X0)
        | ~ r1_xboole_0(X0,k1_xboole_0) )
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f297])).

fof(f368,plain,
    ( spl10_16
    | spl10_1
    | ~ spl10_17 ),
    inference(avatar_split_clause,[],[f367,f300,f119,f297])).

fof(f367,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | ~ v4_relat_1(sK8,X0) )
    | spl10_1
    | ~ spl10_17 ),
    inference(subsumption_resolution,[],[f366,f166])).

fof(f366,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | ~ v1_relat_1(sK8)
        | ~ v4_relat_1(sK8,X0) )
    | spl10_1
    | ~ spl10_17 ),
    inference(trivial_inequality_removal,[],[f364])).

fof(f364,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | ~ r1_xboole_0(X0,k1_xboole_0)
        | ~ v1_relat_1(sK8)
        | ~ v4_relat_1(sK8,X0) )
    | spl10_1
    | ~ spl10_17 ),
    inference(superposition,[],[f355,f243])).

fof(f355,plain,
    ( k1_xboole_0 != k7_relat_1(sK8,k1_xboole_0)
    | spl10_1
    | ~ spl10_17 ),
    inference(backward_demodulation,[],[f292,f301])).

fof(f301,plain,
    ( k1_xboole_0 = k7_relat_1(sK7,k1_xboole_0)
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f300])).

fof(f292,plain,
    ( k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f291,f74])).

fof(f291,plain,
    ( k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | ~ v1_funct_1(sK7)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f290,f76])).

fof(f290,plain,
    ( k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(sK7)
    | spl10_1 ),
    inference(superposition,[],[f289,f108])).

fof(f289,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f288,f77])).

fof(f288,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0)
    | ~ v1_funct_1(sK8)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f283,f79])).

fof(f283,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | spl10_1 ),
    inference(superposition,[],[f257,f108])).

fof(f257,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f256,f235])).

fof(f256,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0)
    | ~ r1_xboole_0(sK5,sK6)
    | spl10_1 ),
    inference(superposition,[],[f255,f100])).

fof(f255,plain,
    ( k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f254,f72])).

fof(f254,plain,
    ( k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | spl10_1 ),
    inference(superposition,[],[f121,f105])).

fof(f121,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f130,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f80,f127,f123,f119])).

fof(f80,plain,
    ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)
    | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)
    | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) ),
    inference(cnf_transformation,[],[f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:49:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (22642)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (22624)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (22632)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (22620)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (22626)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (22634)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (22637)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.21/0.51  % (22643)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.52  % (22628)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.52  % (22635)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (22630)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (22645)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (22627)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.52  % (22623)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.52  % (22625)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.53  % (22638)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.53  % (22640)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (22639)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.53  % (22633)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (22621)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (22631)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.54  % (22644)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.55  % (22641)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.55  % (22624)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (22629)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.55  % (22622)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.50/0.56  % (22636)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.50/0.56  % (22626)Refutation not found, incomplete strategy% (22626)------------------------------
% 1.50/0.56  % (22626)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.56  % (22626)Termination reason: Refutation not found, incomplete strategy
% 1.50/0.56  
% 1.50/0.56  % (22626)Memory used [KB]: 11129
% 1.50/0.56  % (22626)Time elapsed: 0.147 s
% 1.50/0.56  % (22626)------------------------------
% 1.50/0.56  % (22626)------------------------------
% 1.50/0.57  % SZS output start Proof for theBenchmark
% 1.50/0.57  fof(f1189,plain,(
% 1.50/0.57    $false),
% 1.50/0.57    inference(avatar_sat_refutation,[],[f130,f368,f384,f389,f402,f555,f671,f694,f735,f752,f1024,f1041,f1051,f1188])).
% 1.50/0.57  fof(f1188,plain,(
% 1.50/0.57    spl10_3 | ~spl10_56),
% 1.50/0.57    inference(avatar_contradiction_clause,[],[f1187])).
% 1.50/0.57  fof(f1187,plain,(
% 1.50/0.57    $false | (spl10_3 | ~spl10_56)),
% 1.50/0.57    inference(subsumption_resolution,[],[f1186,f1044])).
% 1.50/0.57  fof(f1044,plain,(
% 1.50/0.57    sP0(sK8,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,sK7) | ~spl10_56),
% 1.50/0.57    inference(resolution,[],[f1019,f113])).
% 1.50/0.57  fof(f113,plain,(
% 1.50/0.57    ( ! [X6,X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3,k1_tmap_1(X1,X3,X2,X5,X0,X6),X5,X6) | sP0(X6,X5,k1_tmap_1(X1,X3,X2,X5,X0,X6),X3,X2,X1,X0)) )),
% 1.50/0.57    inference(equality_resolution,[],[f82])).
% 1.50/0.57  fof(f82,plain,(
% 1.50/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0) | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4 | ~sP1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f53])).
% 1.50/0.57  fof(f53,plain,(
% 1.50/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : (((k1_tmap_1(X1,X3,X2,X5,X0,X6) = X4 | ~sP0(X6,X5,X4,X3,X2,X1,X0)) & (sP0(X6,X5,X4,X3,X2,X1,X0) | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4)) | ~sP1(X0,X1,X2,X3,X4,X5,X6))),
% 1.50/0.57    inference(rectify,[],[f52])).
% 1.50/0.57  fof(f52,plain,(
% 1.50/0.57    ! [X4,X0,X2,X1,X6,X3,X5] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | ~sP0(X5,X3,X6,X1,X2,X0,X4)) & (sP0(X5,X3,X6,X1,X2,X0,X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~sP1(X4,X0,X2,X1,X6,X3,X5))),
% 1.50/0.57    inference(nnf_transformation,[],[f41])).
% 1.50/0.57  fof(f41,plain,(
% 1.50/0.57    ! [X4,X0,X2,X1,X6,X3,X5] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> sP0(X5,X3,X6,X1,X2,X0,X4)) | ~sP1(X4,X0,X2,X1,X6,X3,X5))),
% 1.50/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.50/0.57  fof(f1019,plain,(
% 1.50/0.57    sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8) | ~spl10_56),
% 1.50/0.57    inference(avatar_component_clause,[],[f1017])).
% 1.50/0.57  fof(f1017,plain,(
% 1.50/0.57    spl10_56 <=> sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8)),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_56])])).
% 1.50/0.57  fof(f1186,plain,(
% 1.50/0.57    ~sP0(sK8,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,sK7) | (spl10_3 | ~spl10_56)),
% 1.50/0.57    inference(resolution,[],[f1145,f1019])).
% 1.50/0.57  fof(f1145,plain,(
% 1.50/0.57    ( ! [X0] : (~sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~sP0(sK8,sK6,X0,sK4,sK5,sK3,sK7)) ) | spl10_3),
% 1.50/0.57    inference(subsumption_resolution,[],[f1142,f85])).
% 1.50/0.57  fof(f85,plain,(
% 1.50/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f56])).
% 1.50/0.57  fof(f56,plain,(
% 1.50/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) != X0 | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) != X6) & ((k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0 & k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 1.50/0.57    inference(rectify,[],[f55])).
% 1.50/0.57  fof(f55,plain,(
% 1.50/0.57    ! [X5,X3,X6,X1,X2,X0,X4] : ((sP0(X5,X3,X6,X1,X2,X0,X4) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | ~sP0(X5,X3,X6,X1,X2,X0,X4)))),
% 1.50/0.57    inference(flattening,[],[f54])).
% 1.50/0.57  fof(f54,plain,(
% 1.50/0.57    ! [X5,X3,X6,X1,X2,X0,X4] : ((sP0(X5,X3,X6,X1,X2,X0,X4) | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | ~sP0(X5,X3,X6,X1,X2,X0,X4)))),
% 1.50/0.57    inference(nnf_transformation,[],[f40])).
% 1.50/0.57  fof(f40,plain,(
% 1.50/0.57    ! [X5,X3,X6,X1,X2,X0,X4] : (sP0(X5,X3,X6,X1,X2,X0,X4) <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))),
% 1.50/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.50/0.57  fof(f1142,plain,(
% 1.50/0.57    ( ! [X0] : (sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,X0,sK6) | ~sP0(sK8,sK6,X0,sK4,sK5,sK3,sK7) | ~sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)) ) | spl10_3),
% 1.50/0.57    inference(superposition,[],[f129,f83])).
% 1.50/0.57  fof(f83,plain,(
% 1.50/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_tmap_1(X1,X3,X2,X5,X0,X6) = X4 | ~sP0(X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f53])).
% 1.50/0.57  fof(f129,plain,(
% 1.50/0.57    sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | spl10_3),
% 1.50/0.57    inference(avatar_component_clause,[],[f127])).
% 1.50/0.57  fof(f127,plain,(
% 1.50/0.57    spl10_3 <=> sK8 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.50/0.57  fof(f1051,plain,(
% 1.50/0.57    spl10_2 | ~spl10_56),
% 1.50/0.57    inference(avatar_contradiction_clause,[],[f1050])).
% 1.50/0.57  fof(f1050,plain,(
% 1.50/0.57    $false | (spl10_2 | ~spl10_56)),
% 1.50/0.57    inference(trivial_inequality_removal,[],[f1046])).
% 1.50/0.57  fof(f1046,plain,(
% 1.50/0.57    sK7 != sK7 | (spl10_2 | ~spl10_56)),
% 1.50/0.57    inference(resolution,[],[f1044,f408])).
% 1.50/0.57  fof(f408,plain,(
% 1.50/0.57    ( ! [X0,X1] : (~sP0(X1,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,X0) | sK7 != X0) ) | spl10_2),
% 1.50/0.57    inference(superposition,[],[f125,f84])).
% 1.50/0.57  fof(f84,plain,(
% 1.50/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.50/0.57    inference(cnf_transformation,[],[f56])).
% 1.50/0.57  fof(f125,plain,(
% 1.50/0.57    sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | spl10_2),
% 1.50/0.57    inference(avatar_component_clause,[],[f123])).
% 1.50/0.57  fof(f123,plain,(
% 1.50/0.57    spl10_2 <=> sK7 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)),
% 1.50/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.50/0.57  fof(f1041,plain,(
% 1.50/0.57    spl10_57),
% 1.50/0.57    inference(avatar_contradiction_clause,[],[f1040])).
% 1.50/0.57  fof(f1040,plain,(
% 1.50/0.57    $false | spl10_57),
% 1.50/0.57    inference(subsumption_resolution,[],[f1039,f68])).
% 1.50/0.57  fof(f68,plain,(
% 1.50/0.57    ~v1_xboole_0(sK4)),
% 1.50/0.57    inference(cnf_transformation,[],[f51])).
% 1.50/0.57  fof(f51,plain,(
% 1.50/0.57    ((((((sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(sK8,sK6,sK4) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(sK7,sK5,sK4) & v1_funct_1(sK7)) & r1_subset_1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)),
% 1.50/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f21,f50,f49,f48,f47,f46,f45])).
% 1.50/0.57  fof(f45,plain,(
% 1.50/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK3))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f46,plain,(
% 1.50/0.57    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK4,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK4))) & v1_funct_2(X4,X2,sK4) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK4))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.50/0.57  fof(f47,plain,(
% 1.50/0.57    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK4,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK4))) & v1_funct_2(X4,X2,sK4) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,sK5,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) & r1_subset_1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(sK5,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK5))),
% 1.50/0.57    introduced(choice_axiom,[])).
% 1.65/0.57  fof(f48,plain,(
% 1.65/0.57    ? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,sK5,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) & r1_subset_1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK6) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) & r1_subset_1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK6))),
% 1.65/0.57    introduced(choice_axiom,[])).
% 1.65/0.57  fof(f49,plain,(
% 1.65/0.57    ? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK6) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK6) != X5 | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK5) | k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(sK7,sK5,sK4) & v1_funct_1(sK7))),
% 1.65/0.57    introduced(choice_axiom,[])).
% 1.65/0.58  % (22620)Refutation not found, incomplete strategy% (22620)------------------------------
% 1.65/0.58  % (22620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  fof(f50,plain,(
% 1.65/0.58    ? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK6) != X5 | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK5) | k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) => ((sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(sK8,sK6,sK4) & v1_funct_1(sK8))),
% 1.65/0.58    introduced(choice_axiom,[])).
% 1.65/0.58  fof(f21,plain,(
% 1.65/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.65/0.58    inference(flattening,[],[f20])).
% 1.65/0.58  fof(f20,plain,(
% 1.65/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.65/0.58    inference(ennf_transformation,[],[f18])).
% 1.65/0.58  fof(f18,negated_conjecture,(
% 1.65/0.58    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.65/0.58    inference(negated_conjecture,[],[f17])).
% 1.65/0.58  fof(f17,conjecture,(
% 1.65/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 1.65/0.58  fof(f1039,plain,(
% 1.65/0.58    v1_xboole_0(sK4) | spl10_57),
% 1.65/0.58    inference(subsumption_resolution,[],[f1038,f69])).
% 1.65/0.58  fof(f69,plain,(
% 1.65/0.58    ~v1_xboole_0(sK5)),
% 1.65/0.58    inference(cnf_transformation,[],[f51])).
% 1.65/0.58  fof(f1038,plain,(
% 1.65/0.58    v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_57),
% 1.65/0.58    inference(subsumption_resolution,[],[f1037,f70])).
% 1.65/0.58  fof(f70,plain,(
% 1.65/0.58    m1_subset_1(sK5,k1_zfmisc_1(sK3))),
% 1.65/0.58    inference(cnf_transformation,[],[f51])).
% 1.65/0.58  fof(f1037,plain,(
% 1.65/0.58    ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_57),
% 1.65/0.58    inference(subsumption_resolution,[],[f1036,f71])).
% 1.65/0.58  fof(f71,plain,(
% 1.65/0.58    ~v1_xboole_0(sK6)),
% 1.65/0.58    inference(cnf_transformation,[],[f51])).
% 1.65/0.58  fof(f1036,plain,(
% 1.65/0.58    v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_57),
% 1.65/0.58    inference(subsumption_resolution,[],[f1035,f72])).
% 1.65/0.58  fof(f72,plain,(
% 1.65/0.58    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 1.65/0.58    inference(cnf_transformation,[],[f51])).
% 1.65/0.58  fof(f1035,plain,(
% 1.65/0.58    ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_57),
% 1.65/0.58    inference(subsumption_resolution,[],[f1034,f74])).
% 1.65/0.58  fof(f74,plain,(
% 1.65/0.58    v1_funct_1(sK7)),
% 1.65/0.58    inference(cnf_transformation,[],[f51])).
% 1.65/0.58  fof(f1034,plain,(
% 1.65/0.58    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_57),
% 1.65/0.58    inference(subsumption_resolution,[],[f1033,f75])).
% 1.65/0.58  fof(f75,plain,(
% 1.65/0.58    v1_funct_2(sK7,sK5,sK4)),
% 1.65/0.58    inference(cnf_transformation,[],[f51])).
% 1.65/0.58  fof(f1033,plain,(
% 1.65/0.58    ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_57),
% 1.65/0.58    inference(subsumption_resolution,[],[f1032,f76])).
% 1.65/0.58  fof(f76,plain,(
% 1.65/0.58    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 1.65/0.58    inference(cnf_transformation,[],[f51])).
% 1.65/0.58  fof(f1032,plain,(
% 1.65/0.58    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_57),
% 1.65/0.58    inference(subsumption_resolution,[],[f1031,f77])).
% 1.65/0.58  fof(f77,plain,(
% 1.65/0.58    v1_funct_1(sK8)),
% 1.65/0.58    inference(cnf_transformation,[],[f51])).
% 1.65/0.58  fof(f1031,plain,(
% 1.65/0.58    ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_57),
% 1.65/0.58    inference(subsumption_resolution,[],[f1030,f78])).
% 1.65/0.58  fof(f78,plain,(
% 1.65/0.58    v1_funct_2(sK8,sK6,sK4)),
% 1.65/0.58    inference(cnf_transformation,[],[f51])).
% 1.65/0.58  fof(f1030,plain,(
% 1.65/0.58    ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_57),
% 1.65/0.58    inference(subsumption_resolution,[],[f1029,f79])).
% 1.65/0.58  fof(f79,plain,(
% 1.65/0.58    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 1.65/0.58    inference(cnf_transformation,[],[f51])).
% 1.65/0.58  fof(f1029,plain,(
% 1.65/0.58    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_57),
% 1.65/0.58    inference(resolution,[],[f1027,f621])).
% 1.65/0.58  fof(f621,plain,(
% 1.65/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (sP2(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1)) )),
% 1.65/0.58    inference(subsumption_resolution,[],[f112,f88])).
% 1.65/0.58  fof(f88,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f24])).
% 1.65/0.58  fof(f24,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.65/0.58    inference(ennf_transformation,[],[f6])).
% 1.65/0.58  fof(f6,axiom,(
% 1.65/0.58    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.65/0.58  fof(f112,plain,(
% 1.65/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (sP2(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f44])).
% 1.65/0.58  fof(f44,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3,X4,X5] : (sP2(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.65/0.58    inference(definition_folding,[],[f39,f43])).
% 1.65/0.58  fof(f43,plain,(
% 1.65/0.58    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP2(X1,X3,X2,X0,X5,X4))),
% 1.65/0.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.65/0.58  fof(f39,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.65/0.58    inference(flattening,[],[f38])).
% 1.65/0.58  fof(f38,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f16])).
% 1.65/0.58  fof(f16,axiom,(
% 1.65/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.65/0.58  fof(f1027,plain,(
% 1.65/0.58    ~sP2(sK4,sK6,sK5,sK3,sK8,sK7) | spl10_57),
% 1.65/0.58    inference(resolution,[],[f1023,f110])).
% 1.65/0.58  fof(f110,plain,(
% 1.65/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f66])).
% 1.65/0.58  fof(f66,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0))) & v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0) & v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4))) | ~sP2(X0,X1,X2,X3,X4,X5))),
% 1.65/0.58    inference(rectify,[],[f65])).
% 1.65/0.58  fof(f65,plain,(
% 1.65/0.58    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP2(X1,X3,X2,X0,X5,X4))),
% 1.65/0.58    inference(nnf_transformation,[],[f43])).
% 1.65/0.58  fof(f1023,plain,(
% 1.65/0.58    ~v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) | spl10_57),
% 1.65/0.58    inference(avatar_component_clause,[],[f1021])).
% 1.65/0.58  fof(f1021,plain,(
% 1.65/0.58    spl10_57 <=> v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_57])])).
% 1.65/0.58  fof(f1024,plain,(
% 1.65/0.58    spl10_56 | ~spl10_57 | ~spl10_1 | ~spl10_26 | ~spl10_27 | ~spl10_41),
% 1.65/0.58    inference(avatar_split_clause,[],[f1015,f656,f415,f411,f119,f1021,f1017])).
% 1.65/0.58  fof(f119,plain,(
% 1.65/0.58    spl10_1 <=> k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.65/0.58  fof(f411,plain,(
% 1.65/0.58    spl10_26 <=> v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).
% 1.65/0.58  fof(f415,plain,(
% 1.65/0.58    spl10_27 <=> m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).
% 1.65/0.58  fof(f656,plain,(
% 1.65/0.58    spl10_41 <=> k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_41])])).
% 1.65/0.58  fof(f1015,plain,(
% 1.65/0.58    ~v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) | sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8) | (~spl10_1 | ~spl10_26 | ~spl10_27 | ~spl10_41)),
% 1.65/0.58    inference(subsumption_resolution,[],[f1012,f412])).
% 1.65/0.58  fof(f412,plain,(
% 1.65/0.58    v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) | ~spl10_26),
% 1.65/0.58    inference(avatar_component_clause,[],[f411])).
% 1.65/0.58  fof(f1012,plain,(
% 1.65/0.58    ~v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) | sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8) | (~spl10_1 | ~spl10_27 | ~spl10_41)),
% 1.65/0.58    inference(resolution,[],[f1011,f416])).
% 1.65/0.58  fof(f416,plain,(
% 1.65/0.58    m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~spl10_27),
% 1.65/0.58    inference(avatar_component_clause,[],[f415])).
% 1.65/0.58  fof(f1011,plain,(
% 1.65/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)) ) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(subsumption_resolution,[],[f1010,f74])).
% 1.65/0.58  fof(f1010,plain,(
% 1.65/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~v1_funct_1(sK7)) ) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(subsumption_resolution,[],[f1009,f75])).
% 1.65/0.58  fof(f1009,plain,(
% 1.65/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7)) ) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(subsumption_resolution,[],[f1007,f76])).
% 1.65/0.58  fof(f1007,plain,(
% 1.65/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7)) ) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(trivial_inequality_removal,[],[f1004])).
% 1.65/0.58  fof(f1004,plain,(
% 1.65/0.58    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7)) ) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(superposition,[],[f829,f718])).
% 1.65/0.58  fof(f718,plain,(
% 1.65/0.58    k1_xboole_0 = k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(forward_demodulation,[],[f440,f695])).
% 1.65/0.58  fof(f695,plain,(
% 1.65/0.58    k1_xboole_0 = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(backward_demodulation,[],[f635,f658])).
% 1.65/0.58  fof(f658,plain,(
% 1.65/0.58    k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~spl10_41),
% 1.65/0.58    inference(avatar_component_clause,[],[f656])).
% 1.65/0.58  fof(f635,plain,(
% 1.65/0.58    k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f634,f74])).
% 1.65/0.58  fof(f634,plain,(
% 1.65/0.58    k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~v1_funct_1(sK7) | ~spl10_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f630,f76])).
% 1.65/0.58  fof(f630,plain,(
% 1.65/0.58    k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_1(sK7) | ~spl10_1),
% 1.65/0.58    inference(superposition,[],[f438,f108])).
% 1.65/0.58  fof(f108,plain,(
% 1.65/0.58    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f37])).
% 1.65/0.58  fof(f37,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.65/0.58    inference(flattening,[],[f36])).
% 1.65/0.58  fof(f36,plain,(
% 1.65/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.65/0.58    inference(ennf_transformation,[],[f14])).
% 1.65/0.58  fof(f14,axiom,(
% 1.65/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.65/0.58  fof(f438,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f437,f77])).
% 1.65/0.58  fof(f437,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~v1_funct_1(sK8) | ~spl10_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f434,f79])).
% 1.65/0.58  fof(f434,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_1(sK8) | ~spl10_1),
% 1.65/0.58    inference(superposition,[],[f120,f108])).
% 1.65/0.58  fof(f120,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.65/0.58    inference(avatar_component_clause,[],[f119])).
% 1.65/0.58  fof(f440,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f439,f77])).
% 1.65/0.58  fof(f439,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~v1_funct_1(sK8) | ~spl10_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f435,f79])).
% 1.65/0.58  fof(f435,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_1(sK8) | ~spl10_1),
% 1.65/0.58    inference(superposition,[],[f108,f120])).
% 1.65/0.58  fof(f829,plain,(
% 1.65/0.58    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7)) ) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(subsumption_resolution,[],[f828,f68])).
% 1.65/0.58  fof(f828,plain,(
% 1.65/0.58    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(subsumption_resolution,[],[f827,f69])).
% 1.65/0.58  fof(f827,plain,(
% 1.65/0.58    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | v1_xboole_0(sK5) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(subsumption_resolution,[],[f826,f70])).
% 1.65/0.58  fof(f826,plain,(
% 1.65/0.58    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(subsumption_resolution,[],[f825,f71])).
% 1.65/0.58  fof(f825,plain,(
% 1.65/0.58    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(subsumption_resolution,[],[f824,f72])).
% 1.65/0.58  fof(f824,plain,(
% 1.65/0.58    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(subsumption_resolution,[],[f823,f77])).
% 1.65/0.58  fof(f823,plain,(
% 1.65/0.58    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~v1_funct_1(sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(subsumption_resolution,[],[f822,f78])).
% 1.65/0.58  fof(f822,plain,(
% 1.65/0.58    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(subsumption_resolution,[],[f816,f79])).
% 1.65/0.58  fof(f816,plain,(
% 1.65/0.58    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(superposition,[],[f777,f713])).
% 1.65/0.58  fof(f713,plain,(
% 1.65/0.58    k1_xboole_0 = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) | (~spl10_1 | ~spl10_41)),
% 1.65/0.58    inference(forward_demodulation,[],[f641,f658])).
% 1.65/0.58  fof(f641,plain,(
% 1.65/0.58    k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.65/0.58    inference(backward_demodulation,[],[f628,f635])).
% 1.65/0.58  fof(f628,plain,(
% 1.65/0.58    k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.65/0.58    inference(backward_demodulation,[],[f120,f438])).
% 1.65/0.58  fof(f777,plain,(
% 1.65/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | sP1(X4,X0,X2,X1,X6,X3,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1)) )),
% 1.65/0.58    inference(subsumption_resolution,[],[f87,f88])).
% 1.65/0.58  fof(f87,plain,(
% 1.65/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP1(X4,X0,X2,X1,X6,X3,X5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f42])).
% 1.65/0.58  fof(f42,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (sP1(X4,X0,X2,X1,X6,X3,X5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.65/0.58    inference(definition_folding,[],[f23,f41,f40])).
% 1.65/0.58  fof(f23,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.65/0.58    inference(flattening,[],[f22])).
% 1.65/0.58  fof(f22,plain,(
% 1.65/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.65/0.58    inference(ennf_transformation,[],[f15])).
% 1.65/0.58  fof(f15,axiom,(
% 1.65/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.65/0.58  fof(f752,plain,(
% 1.65/0.58    spl10_27),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f751])).
% 1.65/0.58  fof(f751,plain,(
% 1.65/0.58    $false | spl10_27),
% 1.65/0.58    inference(subsumption_resolution,[],[f750,f68])).
% 1.65/0.58  fof(f750,plain,(
% 1.65/0.58    v1_xboole_0(sK4) | spl10_27),
% 1.65/0.58    inference(subsumption_resolution,[],[f749,f69])).
% 1.65/0.58  fof(f749,plain,(
% 1.65/0.58    v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_27),
% 1.65/0.58    inference(subsumption_resolution,[],[f748,f70])).
% 1.65/0.58  fof(f748,plain,(
% 1.65/0.58    ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_27),
% 1.65/0.58    inference(subsumption_resolution,[],[f747,f71])).
% 1.65/0.58  fof(f747,plain,(
% 1.65/0.58    v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_27),
% 1.65/0.58    inference(subsumption_resolution,[],[f746,f72])).
% 1.65/0.58  fof(f746,plain,(
% 1.65/0.58    ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_27),
% 1.65/0.58    inference(subsumption_resolution,[],[f745,f74])).
% 1.65/0.58  fof(f745,plain,(
% 1.65/0.58    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_27),
% 1.65/0.58    inference(subsumption_resolution,[],[f744,f75])).
% 1.65/0.58  fof(f744,plain,(
% 1.65/0.58    ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_27),
% 1.65/0.58    inference(subsumption_resolution,[],[f743,f76])).
% 1.65/0.58  fof(f743,plain,(
% 1.65/0.58    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_27),
% 1.65/0.58    inference(subsumption_resolution,[],[f742,f77])).
% 1.65/0.58  fof(f742,plain,(
% 1.65/0.58    ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_27),
% 1.65/0.58    inference(subsumption_resolution,[],[f741,f78])).
% 1.65/0.58  fof(f741,plain,(
% 1.65/0.58    ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_27),
% 1.65/0.58    inference(subsumption_resolution,[],[f740,f79])).
% 1.65/0.58  fof(f740,plain,(
% 1.65/0.58    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_27),
% 1.65/0.58    inference(resolution,[],[f737,f621])).
% 1.65/0.58  fof(f737,plain,(
% 1.65/0.58    ~sP2(sK4,sK6,sK5,sK3,sK8,sK7) | spl10_27),
% 1.65/0.58    inference(resolution,[],[f417,f111])).
% 1.65/0.58  fof(f111,plain,(
% 1.65/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0))) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f66])).
% 1.65/0.58  fof(f417,plain,(
% 1.65/0.58    ~m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | spl10_27),
% 1.65/0.58    inference(avatar_component_clause,[],[f415])).
% 1.65/0.58  fof(f735,plain,(
% 1.65/0.58    spl10_26),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f734])).
% 1.65/0.58  fof(f734,plain,(
% 1.65/0.58    $false | spl10_26),
% 1.65/0.58    inference(subsumption_resolution,[],[f733,f68])).
% 1.65/0.58  fof(f733,plain,(
% 1.65/0.58    v1_xboole_0(sK4) | spl10_26),
% 1.65/0.58    inference(subsumption_resolution,[],[f732,f69])).
% 1.65/0.58  fof(f732,plain,(
% 1.65/0.58    v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_26),
% 1.65/0.58    inference(subsumption_resolution,[],[f731,f70])).
% 1.65/0.58  fof(f731,plain,(
% 1.65/0.58    ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_26),
% 1.65/0.58    inference(subsumption_resolution,[],[f730,f71])).
% 1.65/0.58  fof(f730,plain,(
% 1.65/0.58    v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_26),
% 1.65/0.58    inference(subsumption_resolution,[],[f729,f72])).
% 1.65/0.58  fof(f729,plain,(
% 1.65/0.58    ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_26),
% 1.65/0.58    inference(subsumption_resolution,[],[f728,f74])).
% 1.65/0.58  fof(f728,plain,(
% 1.65/0.58    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_26),
% 1.65/0.58    inference(subsumption_resolution,[],[f727,f75])).
% 1.65/0.58  fof(f727,plain,(
% 1.65/0.58    ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_26),
% 1.65/0.58    inference(subsumption_resolution,[],[f726,f76])).
% 1.65/0.58  fof(f726,plain,(
% 1.65/0.58    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_26),
% 1.65/0.58    inference(subsumption_resolution,[],[f725,f77])).
% 1.65/0.58  fof(f725,plain,(
% 1.65/0.58    ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_26),
% 1.65/0.58    inference(subsumption_resolution,[],[f724,f78])).
% 1.65/0.58  fof(f724,plain,(
% 1.65/0.58    ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_26),
% 1.65/0.58    inference(subsumption_resolution,[],[f723,f79])).
% 1.65/0.58  fof(f723,plain,(
% 1.65/0.58    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_26),
% 1.65/0.58    inference(resolution,[],[f621,f423])).
% 1.65/0.58  fof(f423,plain,(
% 1.65/0.58    ~sP2(sK4,sK6,sK5,sK3,sK8,sK7) | spl10_26),
% 1.65/0.58    inference(resolution,[],[f413,f109])).
% 1.65/0.58  fof(f109,plain,(
% 1.65/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4)) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f66])).
% 1.65/0.58  fof(f413,plain,(
% 1.65/0.58    ~v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) | spl10_26),
% 1.65/0.58    inference(avatar_component_clause,[],[f411])).
% 1.65/0.58  fof(f694,plain,(
% 1.65/0.58    spl10_31 | ~spl10_40),
% 1.65/0.58    inference(avatar_split_clause,[],[f693,f653,f505])).
% 1.65/0.58  fof(f505,plain,(
% 1.65/0.58    spl10_31 <=> ! [X0] : (~r1_xboole_0(X0,k3_xboole_0(sK5,sK6)) | ~v4_relat_1(sK8,X0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_31])])).
% 1.65/0.58  fof(f653,plain,(
% 1.65/0.58    spl10_40 <=> ! [X0] : (~r1_xboole_0(X0,k9_subset_1(sK3,sK5,sK6)) | ~v4_relat_1(sK8,X0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_40])])).
% 1.65/0.58  fof(f693,plain,(
% 1.65/0.58    ( ! [X0] : (~r1_xboole_0(X0,k3_xboole_0(sK5,sK6)) | ~v4_relat_1(sK8,X0)) ) | ~spl10_40),
% 1.65/0.58    inference(subsumption_resolution,[],[f682,f72])).
% 1.65/0.58  fof(f682,plain,(
% 1.65/0.58    ( ! [X0] : (~r1_xboole_0(X0,k3_xboole_0(sK5,sK6)) | ~v4_relat_1(sK8,X0) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3))) ) | ~spl10_40),
% 1.65/0.58    inference(superposition,[],[f654,f105])).
% 1.65/0.58  fof(f105,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.65/0.58    inference(cnf_transformation,[],[f33])).
% 1.65/0.58  fof(f33,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f5])).
% 1.65/0.58  fof(f5,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.65/0.58  fof(f654,plain,(
% 1.65/0.58    ( ! [X0] : (~r1_xboole_0(X0,k9_subset_1(sK3,sK5,sK6)) | ~v4_relat_1(sK8,X0)) ) | ~spl10_40),
% 1.65/0.58    inference(avatar_component_clause,[],[f653])).
% 1.65/0.58  fof(f671,plain,(
% 1.65/0.58    spl10_40 | spl10_41 | ~spl10_1),
% 1.65/0.58    inference(avatar_split_clause,[],[f670,f119,f656,f653])).
% 1.65/0.58  fof(f670,plain,(
% 1.65/0.58    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~r1_xboole_0(X0,k9_subset_1(sK3,sK5,sK6)) | ~v4_relat_1(sK8,X0)) ) | ~spl10_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f646,f166])).
% 1.65/0.58  fof(f166,plain,(
% 1.65/0.58    v1_relat_1(sK8)),
% 1.65/0.58    inference(resolution,[],[f106,f79])).
% 1.65/0.58  fof(f106,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f34])).
% 1.65/0.58  fof(f34,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.65/0.58    inference(ennf_transformation,[],[f13])).
% 1.65/0.58  fof(f13,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.65/0.58  fof(f646,plain,(
% 1.65/0.58    ( ! [X0] : (k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~r1_xboole_0(X0,k9_subset_1(sK3,sK5,sK6)) | ~v1_relat_1(sK8) | ~v4_relat_1(sK8,X0)) ) | ~spl10_1),
% 1.65/0.58    inference(superposition,[],[f243,f635])).
% 1.65/0.58  fof(f243,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X2) | ~r1_xboole_0(X1,X2) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1)) )),
% 1.65/0.58    inference(duplicate_literal_removal,[],[f239])).
% 1.65/0.58  fof(f239,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X2) | ~r1_xboole_0(X1,X2) | ~v1_relat_1(X0) | ~v4_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 1.65/0.58    inference(superposition,[],[f104,f96])).
% 1.65/0.58  fof(f96,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f30])).
% 1.65/0.58  fof(f30,plain,(
% 1.65/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.65/0.58    inference(flattening,[],[f29])).
% 1.65/0.58  fof(f29,plain,(
% 1.65/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.65/0.58    inference(ennf_transformation,[],[f11])).
% 1.65/0.58  fof(f11,axiom,(
% 1.65/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.65/0.58  fof(f104,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f32])).
% 1.65/0.58  fof(f32,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 1.65/0.58    inference(flattening,[],[f31])).
% 1.65/0.58  fof(f31,plain,(
% 1.65/0.58    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.65/0.58    inference(ennf_transformation,[],[f10])).
% 1.65/0.58  fof(f10,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 1.65/0.58  fof(f555,plain,(
% 1.65/0.58    spl10_16 | ~spl10_31),
% 1.65/0.58    inference(avatar_split_clause,[],[f554,f505,f297])).
% 1.65/0.58  fof(f297,plain,(
% 1.65/0.58    spl10_16 <=> ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | ~v4_relat_1(sK8,X0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 1.65/0.58  fof(f554,plain,(
% 1.65/0.58    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | ~v4_relat_1(sK8,X0)) ) | ~spl10_31),
% 1.65/0.58    inference(subsumption_resolution,[],[f540,f235])).
% 1.65/0.58  fof(f235,plain,(
% 1.65/0.58    r1_xboole_0(sK5,sK6)),
% 1.65/0.58    inference(resolution,[],[f234,f73])).
% 1.65/0.58  fof(f73,plain,(
% 1.65/0.58    r1_subset_1(sK5,sK6)),
% 1.65/0.58    inference(cnf_transformation,[],[f51])).
% 1.65/0.58  fof(f234,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | r1_xboole_0(X0,X1)) )),
% 1.65/0.58    inference(subsumption_resolution,[],[f233,f231])).
% 1.65/0.58  fof(f231,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.65/0.58    inference(resolution,[],[f225,f89])).
% 1.65/0.58  fof(f89,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f58])).
% 1.65/0.58  fof(f58,plain,(
% 1.65/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.65/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f25,f57])).
% 1.65/0.58  fof(f57,plain,(
% 1.65/0.58    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 1.65/0.58    introduced(choice_axiom,[])).
% 1.65/0.58  fof(f25,plain,(
% 1.65/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.65/0.58    inference(ennf_transformation,[],[f19])).
% 1.65/0.58  fof(f19,plain,(
% 1.65/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.65/0.58    inference(rectify,[],[f3])).
% 1.65/0.58  fof(f3,axiom,(
% 1.65/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.65/0.58  fof(f225,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 1.65/0.58    inference(resolution,[],[f224,f116])).
% 1.65/0.58  fof(f116,plain,(
% 1.65/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.65/0.58    inference(equality_resolution,[],[f98])).
% 1.65/0.58  fof(f98,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.65/0.58    inference(cnf_transformation,[],[f62])).
% 1.65/0.58  fof(f62,plain,(
% 1.65/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/0.58    inference(flattening,[],[f61])).
% 1.65/0.58  fof(f61,plain,(
% 1.65/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.65/0.58    inference(nnf_transformation,[],[f4])).
% 1.65/0.58  fof(f4,axiom,(
% 1.65/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.65/0.58  fof(f224,plain,(
% 1.65/0.58    ( ! [X6,X4,X5] : (~r1_tarski(X6,X4) | ~r2_hidden(X5,X6) | ~v1_xboole_0(X4)) )),
% 1.65/0.58    inference(resolution,[],[f107,f103])).
% 1.65/0.58  fof(f103,plain,(
% 1.65/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f64])).
% 1.65/0.58  fof(f64,plain,(
% 1.65/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.65/0.58    inference(nnf_transformation,[],[f7])).
% 1.65/0.58  fof(f7,axiom,(
% 1.65/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.65/0.58  fof(f107,plain,(
% 1.65/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f35])).
% 1.65/0.58  fof(f35,plain,(
% 1.65/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.65/0.58    inference(ennf_transformation,[],[f8])).
% 1.65/0.58  fof(f8,axiom,(
% 1.65/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.65/0.58  fof(f233,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X0)) )),
% 1.65/0.58    inference(subsumption_resolution,[],[f94,f232])).
% 1.65/0.58  fof(f232,plain,(
% 1.65/0.58    ( ! [X2,X3] : (r1_xboole_0(X3,X2) | ~v1_xboole_0(X2)) )),
% 1.65/0.58    inference(resolution,[],[f225,f90])).
% 1.65/0.58  fof(f90,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f58])).
% 1.65/0.58  fof(f94,plain,(
% 1.65/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f60])).
% 1.65/0.58  fof(f60,plain,(
% 1.65/0.58    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.65/0.58    inference(nnf_transformation,[],[f28])).
% 1.65/0.58  fof(f28,plain,(
% 1.65/0.58    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.65/0.58    inference(flattening,[],[f27])).
% 1.65/0.58  fof(f27,plain,(
% 1.65/0.58    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.65/0.58    inference(ennf_transformation,[],[f12])).
% 1.65/0.58  fof(f12,axiom,(
% 1.65/0.58    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.65/0.58  fof(f540,plain,(
% 1.65/0.58    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | ~v4_relat_1(sK8,X0) | ~r1_xboole_0(sK5,sK6)) ) | ~spl10_31),
% 1.65/0.58    inference(superposition,[],[f506,f100])).
% 1.65/0.58  fof(f100,plain,(
% 1.65/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f63])).
% 1.65/0.58  fof(f63,plain,(
% 1.65/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.65/0.58    inference(nnf_transformation,[],[f1])).
% 1.65/0.58  fof(f1,axiom,(
% 1.65/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.65/0.58  fof(f506,plain,(
% 1.65/0.58    ( ! [X0] : (~r1_xboole_0(X0,k3_xboole_0(sK5,sK6)) | ~v4_relat_1(sK8,X0)) ) | ~spl10_31),
% 1.65/0.58    inference(avatar_component_clause,[],[f505])).
% 1.65/0.58  fof(f402,plain,(
% 1.65/0.58    ~spl10_22),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f401])).
% 1.65/0.58  fof(f401,plain,(
% 1.65/0.58    $false | ~spl10_22),
% 1.65/0.58    inference(subsumption_resolution,[],[f398,f81])).
% 1.65/0.58  fof(f81,plain,(
% 1.65/0.58    v1_xboole_0(k1_xboole_0)),
% 1.65/0.58    inference(cnf_transformation,[],[f2])).
% 1.65/0.58  fof(f2,axiom,(
% 1.65/0.58    v1_xboole_0(k1_xboole_0)),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.65/0.58  fof(f398,plain,(
% 1.65/0.58    ~v1_xboole_0(k1_xboole_0) | ~spl10_22),
% 1.65/0.58    inference(resolution,[],[f393,f232])).
% 1.65/0.58  fof(f393,plain,(
% 1.65/0.58    ~r1_xboole_0(k1_relat_1(sK7),k1_xboole_0) | ~spl10_22),
% 1.65/0.58    inference(subsumption_resolution,[],[f392,f165])).
% 1.65/0.58  fof(f165,plain,(
% 1.65/0.58    v1_relat_1(sK7)),
% 1.65/0.58    inference(resolution,[],[f106,f76])).
% 1.65/0.58  fof(f392,plain,(
% 1.65/0.58    ~r1_xboole_0(k1_relat_1(sK7),k1_xboole_0) | ~v1_relat_1(sK7) | ~spl10_22),
% 1.65/0.58    inference(resolution,[],[f334,f176])).
% 1.65/0.58  fof(f176,plain,(
% 1.65/0.58    ( ! [X2] : (v4_relat_1(X2,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 1.65/0.58    inference(resolution,[],[f93,f116])).
% 1.65/0.58  fof(f93,plain,(
% 1.65/0.58    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.65/0.58    inference(cnf_transformation,[],[f59])).
% 1.65/0.58  fof(f59,plain,(
% 1.65/0.58    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.65/0.58    inference(nnf_transformation,[],[f26])).
% 1.65/0.58  fof(f26,plain,(
% 1.65/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.65/0.58    inference(ennf_transformation,[],[f9])).
% 1.65/0.58  fof(f9,axiom,(
% 1.65/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.65/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.65/0.58  fof(f334,plain,(
% 1.65/0.58    ( ! [X0] : (~v4_relat_1(sK7,X0) | ~r1_xboole_0(X0,k1_xboole_0)) ) | ~spl10_22),
% 1.65/0.58    inference(avatar_component_clause,[],[f333])).
% 1.65/0.58  fof(f333,plain,(
% 1.65/0.58    spl10_22 <=> ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | ~v4_relat_1(sK7,X0))),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).
% 1.65/0.58  fof(f389,plain,(
% 1.65/0.58    spl10_22 | spl10_17),
% 1.65/0.58    inference(avatar_split_clause,[],[f388,f300,f333])).
% 1.65/0.58  fof(f300,plain,(
% 1.65/0.58    spl10_17 <=> k1_xboole_0 = k7_relat_1(sK7,k1_xboole_0)),
% 1.65/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 1.65/0.58  fof(f388,plain,(
% 1.65/0.58    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | ~v4_relat_1(sK7,X0)) ) | spl10_17),
% 1.65/0.58    inference(subsumption_resolution,[],[f387,f165])).
% 1.65/0.58  fof(f387,plain,(
% 1.65/0.58    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | ~v1_relat_1(sK7) | ~v4_relat_1(sK7,X0)) ) | spl10_17),
% 1.65/0.58    inference(trivial_inequality_removal,[],[f385])).
% 1.65/0.58  fof(f385,plain,(
% 1.65/0.58    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(X0,k1_xboole_0) | ~v1_relat_1(sK7) | ~v4_relat_1(sK7,X0)) ) | spl10_17),
% 1.65/0.58    inference(superposition,[],[f302,f243])).
% 1.65/0.58  fof(f302,plain,(
% 1.65/0.58    k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0) | spl10_17),
% 1.65/0.58    inference(avatar_component_clause,[],[f300])).
% 1.65/0.58  fof(f384,plain,(
% 1.65/0.58    ~spl10_16),
% 1.65/0.58    inference(avatar_contradiction_clause,[],[f383])).
% 1.65/0.58  fof(f383,plain,(
% 1.65/0.58    $false | ~spl10_16),
% 1.65/0.58    inference(subsumption_resolution,[],[f380,f81])).
% 1.65/0.58  fof(f380,plain,(
% 1.65/0.58    ~v1_xboole_0(k1_xboole_0) | ~spl10_16),
% 1.65/0.58    inference(resolution,[],[f370,f232])).
% 1.65/0.58  fof(f370,plain,(
% 1.65/0.58    ~r1_xboole_0(k1_relat_1(sK8),k1_xboole_0) | ~spl10_16),
% 1.65/0.58    inference(subsumption_resolution,[],[f369,f166])).
% 1.65/0.58  fof(f369,plain,(
% 1.65/0.58    ~r1_xboole_0(k1_relat_1(sK8),k1_xboole_0) | ~v1_relat_1(sK8) | ~spl10_16),
% 1.65/0.58    inference(resolution,[],[f298,f176])).
% 1.65/0.58  fof(f298,plain,(
% 1.65/0.58    ( ! [X0] : (~v4_relat_1(sK8,X0) | ~r1_xboole_0(X0,k1_xboole_0)) ) | ~spl10_16),
% 1.65/0.58    inference(avatar_component_clause,[],[f297])).
% 1.65/0.58  fof(f368,plain,(
% 1.65/0.58    spl10_16 | spl10_1 | ~spl10_17),
% 1.65/0.58    inference(avatar_split_clause,[],[f367,f300,f119,f297])).
% 1.65/0.58  fof(f367,plain,(
% 1.65/0.58    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | ~v4_relat_1(sK8,X0)) ) | (spl10_1 | ~spl10_17)),
% 1.65/0.58    inference(subsumption_resolution,[],[f366,f166])).
% 1.65/0.58  fof(f366,plain,(
% 1.65/0.58    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | ~v1_relat_1(sK8) | ~v4_relat_1(sK8,X0)) ) | (spl10_1 | ~spl10_17)),
% 1.65/0.58    inference(trivial_inequality_removal,[],[f364])).
% 1.65/0.58  fof(f364,plain,(
% 1.65/0.58    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(X0,k1_xboole_0) | ~v1_relat_1(sK8) | ~v4_relat_1(sK8,X0)) ) | (spl10_1 | ~spl10_17)),
% 1.65/0.58    inference(superposition,[],[f355,f243])).
% 1.65/0.58  fof(f355,plain,(
% 1.65/0.58    k1_xboole_0 != k7_relat_1(sK8,k1_xboole_0) | (spl10_1 | ~spl10_17)),
% 1.65/0.58    inference(backward_demodulation,[],[f292,f301])).
% 1.65/0.58  fof(f301,plain,(
% 1.65/0.58    k1_xboole_0 = k7_relat_1(sK7,k1_xboole_0) | ~spl10_17),
% 1.65/0.58    inference(avatar_component_clause,[],[f300])).
% 1.65/0.58  fof(f292,plain,(
% 1.65/0.58    k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) | spl10_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f291,f74])).
% 1.65/0.58  fof(f291,plain,(
% 1.65/0.58    k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) | ~v1_funct_1(sK7) | spl10_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f290,f76])).
% 1.65/0.58  fof(f290,plain,(
% 1.65/0.58    k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_1(sK7) | spl10_1),
% 1.65/0.58    inference(superposition,[],[f289,f108])).
% 1.65/0.58  fof(f289,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0) | spl10_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f288,f77])).
% 1.65/0.58  fof(f288,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0) | ~v1_funct_1(sK8) | spl10_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f283,f79])).
% 1.65/0.58  fof(f283,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_1(sK8) | spl10_1),
% 1.65/0.58    inference(superposition,[],[f257,f108])).
% 1.65/0.58  fof(f257,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0) | spl10_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f256,f235])).
% 1.65/0.58  fof(f256,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0) | ~r1_xboole_0(sK5,sK6) | spl10_1),
% 1.65/0.58    inference(superposition,[],[f255,f100])).
% 1.65/0.58  fof(f255,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6)) | spl10_1),
% 1.65/0.58    inference(subsumption_resolution,[],[f254,f72])).
% 1.65/0.58  fof(f254,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | spl10_1),
% 1.65/0.58    inference(superposition,[],[f121,f105])).
% 1.65/0.58  fof(f121,plain,(
% 1.65/0.58    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) | spl10_1),
% 1.65/0.58    inference(avatar_component_clause,[],[f119])).
% 1.65/0.58  fof(f130,plain,(
% 1.65/0.58    ~spl10_1 | ~spl10_2 | ~spl10_3),
% 1.65/0.58    inference(avatar_split_clause,[],[f80,f127,f123,f119])).
% 1.65/0.58  fof(f80,plain,(
% 1.65/0.58    sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))),
% 1.65/0.58    inference(cnf_transformation,[],[f51])).
% 1.65/0.58  % SZS output end Proof for theBenchmark
% 1.65/0.58  % (22624)------------------------------
% 1.65/0.58  % (22624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.65/0.58  % (22624)Termination reason: Refutation
% 1.65/0.58  
% 1.65/0.58  % (22624)Memory used [KB]: 6780
% 1.65/0.58  % (22624)Time elapsed: 0.146 s
% 1.65/0.58  % (22624)------------------------------
% 1.65/0.58  % (22624)------------------------------
% 1.65/0.59  % (22619)Success in time 0.225 s
%------------------------------------------------------------------------------
