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
% DateTime   : Thu Dec  3 13:17:34 EST 2020

% Result     : Theorem 1.27s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  245 (2119 expanded)
%              Number of leaves         :   32 (1021 expanded)
%              Depth                    :   35
%              Number of atoms          : 1320 (31536 expanded)
%              Number of equality atoms :  163 (6940 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f825,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f130,f255,f266,f280,f380,f439,f447,f514,f594,f674,f756,f824])).

fof(f824,plain,
    ( ~ spl10_1
    | spl10_3
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_20
    | ~ spl10_32 ),
    inference(avatar_contradiction_clause,[],[f823])).

fof(f823,plain,
    ( $false
    | ~ spl10_1
    | spl10_3
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_20
    | ~ spl10_32 ),
    inference(subsumption_resolution,[],[f822,f749])).

fof(f749,plain,
    ( sP0(sK8,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,sK7)
    | ~ spl10_1
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_20
    | ~ spl10_32 ),
    inference(resolution,[],[f745,f112])).

fof(f112,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,k1_tmap_1(X1,X3,X2,X5,X0,X6),X5,X6)
      | sP0(X6,X5,k1_tmap_1(X1,X3,X2,X5,X0,X6),X3,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0)
      | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( ( k1_tmap_1(X1,X3,X2,X5,X0,X6) = X4
          | ~ sP0(X6,X5,X4,X3,X2,X1,X0) )
        & ( sP0(X6,X5,X4,X3,X2,X1,X0)
          | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4 ) )
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X4,X0,X2,X1,X6,X3,X5] :
      ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
          | ~ sP0(X5,X3,X6,X1,X2,X0,X4) )
        & ( sP0(X5,X3,X6,X1,X2,X0,X4)
          | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
      | ~ sP1(X4,X0,X2,X1,X6,X3,X5) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X4,X0,X2,X1,X6,X3,X5] :
      ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
      <=> sP0(X5,X3,X6,X1,X2,X0,X4) )
      | ~ sP1(X4,X0,X2,X1,X6,X3,X5) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f745,plain,
    ( sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8)
    | ~ spl10_1
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_20
    | ~ spl10_32 ),
    inference(subsumption_resolution,[],[f744,f290])).

fof(f290,plain,
    ( v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl10_14 ),
    inference(avatar_component_clause,[],[f289])).

fof(f289,plain,
    ( spl10_14
  <=> v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).

fof(f744,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))
    | sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8)
    | ~ spl10_1
    | ~ spl10_15
    | ~ spl10_20
    | ~ spl10_32 ),
    inference(subsumption_resolution,[],[f741,f650])).

fof(f650,plain,
    ( v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)
    | ~ spl10_32 ),
    inference(avatar_component_clause,[],[f649])).

fof(f649,plain,
    ( spl10_32
  <=> v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).

fof(f741,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)
    | ~ v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))
    | sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8)
    | ~ spl10_1
    | ~ spl10_15
    | ~ spl10_20 ),
    inference(resolution,[],[f740,f294])).

fof(f294,plain,
    ( m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
    | ~ spl10_15 ),
    inference(avatar_component_clause,[],[f293])).

fof(f293,plain,
    ( spl10_15
  <=> m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).

fof(f740,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X0)
        | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f739,f72])).

fof(f72,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f20,f48,f47,f46,f45,f44,f43])).

% (24877)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f43,plain,
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

fof(f44,plain,
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

fof(f45,plain,
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

fof(f46,plain,
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

fof(f47,plain,
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

fof(f48,plain,
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f739,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X0)
        | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)
        | ~ v1_funct_1(sK7) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f738,f73])).

fof(f73,plain,(
    v1_funct_2(sK7,sK5,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f738,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X0)
        | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)
        | ~ v1_funct_2(sK7,sK5,sK4)
        | ~ v1_funct_1(sK7) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f736,f74])).

fof(f74,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f49])).

fof(f736,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X0)
        | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(sK7,sK5,sK4)
        | ~ v1_funct_1(sK7) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(trivial_inequality_removal,[],[f733])).

fof(f733,plain,
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
    | ~ spl10_20 ),
    inference(superposition,[],[f559,f469])).

fof(f469,plain,
    ( k1_xboole_0 = k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(forward_demodulation,[],[f309,f453])).

fof(f453,plain,
    ( k1_xboole_0 = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(backward_demodulation,[],[f419,f436])).

fof(f436,plain,
    ( k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_20 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl10_20
  <=> k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).

fof(f419,plain,
    ( k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f418,f72])).

fof(f418,plain,
    ( k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ v1_funct_1(sK7)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f414,f74])).

fof(f414,plain,
    ( k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(sK7)
    | ~ spl10_1 ),
    inference(superposition,[],[f307,f107])).

fof(f107,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f307,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f306,f75])).

fof(f75,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f49])).

fof(f306,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ v1_funct_1(sK8)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f303,f77])).

fof(f77,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f49])).

fof(f303,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | ~ spl10_1 ),
    inference(superposition,[],[f120,f107])).

fof(f120,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl10_1
  <=> k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f309,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f308,f75])).

fof(f308,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ v1_funct_1(sK8)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f304,f77])).

fof(f304,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | ~ spl10_1 ),
    inference(superposition,[],[f107,f120])).

fof(f559,plain,
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
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f558,f65])).

fof(f65,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f49])).

fof(f558,plain,
    ( ! [X8,X7] :
        ( k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X8)
        | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(X7,sK5,sK4)
        | ~ v1_funct_1(X7)
        | v1_xboole_0(sK3) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f557,f66])).

fof(f66,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f557,plain,
    ( ! [X8,X7] :
        ( k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6))
        | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X8)
        | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8)
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(X7,sK5,sK4)
        | ~ v1_funct_1(X7)
        | v1_xboole_0(sK4)
        | v1_xboole_0(sK3) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f556,f67])).

fof(f67,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f49])).

fof(f556,plain,
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
        | v1_xboole_0(sK4)
        | v1_xboole_0(sK3) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f555,f68])).

fof(f68,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f555,plain,
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
        | v1_xboole_0(sK4)
        | v1_xboole_0(sK3) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f554,f69])).

fof(f69,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f554,plain,
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
        | v1_xboole_0(sK4)
        | v1_xboole_0(sK3) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f553,f70])).

fof(f70,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f49])).

fof(f553,plain,
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
        | v1_xboole_0(sK4)
        | v1_xboole_0(sK3) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f552,f75])).

fof(f552,plain,
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
        | v1_xboole_0(sK4)
        | v1_xboole_0(sK3) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f551,f76])).

fof(f76,plain,(
    v1_funct_2(sK8,sK6,sK4) ),
    inference(cnf_transformation,[],[f49])).

fof(f551,plain,
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
        | v1_xboole_0(sK4)
        | v1_xboole_0(sK3) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(subsumption_resolution,[],[f545,f77])).

% (24875)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (24870)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% (24880)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% (24873)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% (24879)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% (24863)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
fof(f545,plain,
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
        | v1_xboole_0(sK4)
        | v1_xboole_0(sK3) )
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(superposition,[],[f85,f458])).

fof(f458,plain,
    ( k1_xboole_0 = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1
    | ~ spl10_20 ),
    inference(forward_demodulation,[],[f452,f436])).

fof(f452,plain,
    ( k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f412,f419])).

fof(f412,plain,
    ( k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(backward_demodulation,[],[f120,f307])).

fof(f85,plain,(
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
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    inference(definition_folding,[],[f22,f39,f38])).

% (24868)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
fof(f38,plain,(
    ! [X5,X3,X6,X1,X2,X0,X4] :
      ( sP0(X5,X3,X6,X1,X2,X0,X4)
    <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
        & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f822,plain,
    ( ~ sP0(sK8,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,sK7)
    | ~ spl10_1
    | spl10_3
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_20
    | ~ spl10_32 ),
    inference(resolution,[],[f797,f745])).

fof(f797,plain,
    ( ! [X0] :
        ( ~ sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)
        | ~ sP0(sK8,sK6,X0,sK4,sK5,sK3,sK7) )
    | spl10_3 ),
    inference(subsumption_resolution,[],[f794,f83])).

fof(f83,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) != X0
        | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) != X6 )
      & ( ( k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0
          & k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6 )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X5,X3,X6,X1,X2,X0,X4] :
      ( ( sP0(X5,X3,X6,X1,X2,X0,X4)
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
      & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
          & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
        | ~ sP0(X5,X3,X6,X1,X2,X0,X4) ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X5,X3,X6,X1,X2,X0,X4] :
      ( ( sP0(X5,X3,X6,X1,X2,X0,X4)
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
      & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
          & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
        | ~ sP0(X5,X3,X6,X1,X2,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f794,plain,
    ( ! [X0] :
        ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,X0,sK6)
        | ~ sP0(sK8,sK6,X0,sK4,sK5,sK3,sK7)
        | ~ sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) )
    | spl10_3 ),
    inference(superposition,[],[f129,f81])).

fof(f81,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k1_tmap_1(X1,X3,X2,X5,X0,X6) = X4
      | ~ sP0(X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f129,plain,
    ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl10_3
  <=> sK8 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f756,plain,
    ( ~ spl10_1
    | spl10_2
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_20
    | ~ spl10_32 ),
    inference(avatar_contradiction_clause,[],[f755])).

fof(f755,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_20
    | ~ spl10_32 ),
    inference(trivial_inequality_removal,[],[f751])).

fof(f751,plain,
    ( sK7 != sK7
    | ~ spl10_1
    | spl10_2
    | ~ spl10_14
    | ~ spl10_15
    | ~ spl10_20
    | ~ spl10_32 ),
    inference(resolution,[],[f749,f286])).

fof(f286,plain,
    ( ! [X0,X1] :
        ( ~ sP0(X1,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,X0)
        | sK7 != X0 )
    | spl10_2 ),
    inference(superposition,[],[f125,f82])).

fof(f82,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f125,plain,
    ( sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl10_2
  <=> sK7 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f674,plain,(
    spl10_32 ),
    inference(avatar_contradiction_clause,[],[f673])).

fof(f673,plain,
    ( $false
    | spl10_32 ),
    inference(subsumption_resolution,[],[f672,f65])).

fof(f672,plain,
    ( v1_xboole_0(sK3)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f671,f66])).

fof(f671,plain,
    ( v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f670,f67])).

fof(f670,plain,
    ( v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f669,f68])).

fof(f669,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f668,f69])).

fof(f668,plain,
    ( v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f667,f70])).

fof(f667,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f666,f72])).

fof(f666,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f665,f73])).

fof(f665,plain,
    ( ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f664,f74])).

fof(f664,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f663,f75])).

fof(f663,plain,
    ( ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f662,f76])).

fof(f662,plain,
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
    | v1_xboole_0(sK3)
    | spl10_32 ),
    inference(subsumption_resolution,[],[f661,f77])).

fof(f661,plain,
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
    | v1_xboole_0(sK3)
    | spl10_32 ),
    inference(resolution,[],[f659,f111])).

fof(f111,plain,(
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
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(definition_folding,[],[f37,f41])).

fof(f41,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP2(X1,X3,X2,X0,X5,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f659,plain,
    ( ~ sP2(sK4,sK6,sK5,sK3,sK8,sK7)
    | spl10_32 ),
    inference(resolution,[],[f651,f109])).

fof(f109,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0)
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0)))
        & v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0)
        & v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4)) )
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f63])).

fof(f63,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP2(X1,X3,X2,X0,X5,X4) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f651,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)
    | spl10_32 ),
    inference(avatar_component_clause,[],[f649])).

fof(f594,plain,(
    spl10_15 ),
    inference(avatar_contradiction_clause,[],[f593])).

fof(f593,plain,
    ( $false
    | spl10_15 ),
    inference(subsumption_resolution,[],[f592,f65])).

fof(f592,plain,
    ( v1_xboole_0(sK3)
    | spl10_15 ),
    inference(subsumption_resolution,[],[f591,f66])).

fof(f591,plain,
    ( v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_15 ),
    inference(subsumption_resolution,[],[f590,f67])).

fof(f590,plain,
    ( v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_15 ),
    inference(subsumption_resolution,[],[f589,f68])).

fof(f589,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_15 ),
    inference(subsumption_resolution,[],[f588,f69])).

fof(f588,plain,
    ( v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_15 ),
    inference(subsumption_resolution,[],[f587,f70])).

fof(f587,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_15 ),
    inference(subsumption_resolution,[],[f586,f72])).

fof(f586,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_15 ),
    inference(subsumption_resolution,[],[f585,f73])).

fof(f585,plain,
    ( ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_15 ),
    inference(subsumption_resolution,[],[f584,f74])).

fof(f584,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_15 ),
    inference(subsumption_resolution,[],[f583,f75])).

fof(f583,plain,
    ( ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_15 ),
    inference(subsumption_resolution,[],[f582,f76])).

fof(f582,plain,
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
    | v1_xboole_0(sK3)
    | spl10_15 ),
    inference(subsumption_resolution,[],[f581,f77])).

fof(f581,plain,
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
    | v1_xboole_0(sK3)
    | spl10_15 ),
    inference(resolution,[],[f578,f111])).

fof(f578,plain,
    ( ~ sP2(sK4,sK6,sK5,sK3,sK8,sK7)
    | spl10_15 ),
    inference(resolution,[],[f295,f110])).

fof(f110,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0)))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f295,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
    | spl10_15 ),
    inference(avatar_component_clause,[],[f293])).

fof(f514,plain,(
    spl10_14 ),
    inference(avatar_contradiction_clause,[],[f513])).

fof(f513,plain,
    ( $false
    | spl10_14 ),
    inference(subsumption_resolution,[],[f512,f65])).

fof(f512,plain,
    ( v1_xboole_0(sK3)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f511,f66])).

fof(f511,plain,
    ( v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f510,f67])).

fof(f510,plain,
    ( v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f509,f68])).

fof(f509,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f508,f69])).

fof(f508,plain,
    ( v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f507,f70])).

fof(f507,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f506,f72])).

fof(f506,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f505,f73])).

fof(f505,plain,
    ( ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f504,f74])).

fof(f504,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f503,f75])).

fof(f503,plain,
    ( ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK3)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f502,f76])).

fof(f502,plain,
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
    | v1_xboole_0(sK3)
    | spl10_14 ),
    inference(subsumption_resolution,[],[f501,f77])).

fof(f501,plain,
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
    | v1_xboole_0(sK3)
    | spl10_14 ),
    inference(resolution,[],[f111,f301])).

fof(f301,plain,
    ( ~ sP2(sK4,sK6,sK5,sK3,sK8,sK7)
    | spl10_14 ),
    inference(resolution,[],[f291,f108])).

fof(f108,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f291,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))
    | spl10_14 ),
    inference(avatar_component_clause,[],[f289])).

fof(f447,plain,
    ( ~ spl10_17
    | spl10_19 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | ~ spl10_17
    | spl10_19 ),
    inference(subsumption_resolution,[],[f445,f70])).

fof(f445,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | ~ spl10_17
    | spl10_19 ),
    inference(subsumption_resolution,[],[f443,f364])).

fof(f364,plain,
    ( r1_xboole_0(k3_xboole_0(sK5,sK6),k1_relat_1(sK8))
    | ~ spl10_17 ),
    inference(avatar_component_clause,[],[f363])).

fof(f363,plain,
    ( spl10_17
  <=> r1_xboole_0(k3_xboole_0(sK5,sK6),k1_relat_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f443,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK5,sK6),k1_relat_1(sK8))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | spl10_19 ),
    inference(superposition,[],[f432,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f432,plain,
    ( ~ r1_xboole_0(k9_subset_1(sK3,sK5,sK6),k1_relat_1(sK8))
    | spl10_19 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl10_19
  <=> r1_xboole_0(k9_subset_1(sK3,sK5,sK6),k1_relat_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f439,plain,
    ( ~ spl10_19
    | spl10_20
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f438,f119,f434,f430])).

fof(f438,plain,
    ( k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ r1_xboole_0(k9_subset_1(sK3,sK5,sK6),k1_relat_1(sK8))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f425,f140])).

fof(f140,plain,(
    v1_relat_1(sK8) ),
    inference(resolution,[],[f104,f77])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f425,plain,
    ( k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ r1_xboole_0(k9_subset_1(sK3,sK5,sK6),k1_relat_1(sK8))
    | ~ v1_relat_1(sK8)
    | ~ spl10_1 ),
    inference(superposition,[],[f86,f419])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f380,plain,
    ( ~ spl10_12
    | spl10_17 ),
    inference(avatar_contradiction_clause,[],[f379])).

fof(f379,plain,
    ( $false
    | ~ spl10_12
    | spl10_17 ),
    inference(subsumption_resolution,[],[f378,f202])).

fof(f202,plain,(
    r1_xboole_0(sK5,sK6) ),
    inference(subsumption_resolution,[],[f201,f67])).

fof(f201,plain,
    ( r1_xboole_0(sK5,sK6)
    | v1_xboole_0(sK5) ),
    inference(subsumption_resolution,[],[f200,f69])).

fof(f200,plain,
    ( r1_xboole_0(sK5,sK6)
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK5) ),
    inference(resolution,[],[f92,f71])).

fof(f71,plain,(
    r1_subset_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f378,plain,
    ( ~ r1_xboole_0(sK5,sK6)
    | ~ spl10_12
    | spl10_17 ),
    inference(subsumption_resolution,[],[f376,f249])).

fof(f249,plain,
    ( r1_xboole_0(k1_xboole_0,k1_relat_1(sK8))
    | ~ spl10_12 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl10_12
  <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).

fof(f376,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK8))
    | ~ r1_xboole_0(sK5,sK6)
    | spl10_17 ),
    inference(superposition,[],[f365,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f365,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK5,sK6),k1_relat_1(sK8))
    | spl10_17 ),
    inference(avatar_component_clause,[],[f363])).

fof(f280,plain,(
    spl10_13 ),
    inference(avatar_contradiction_clause,[],[f279])).

fof(f279,plain,
    ( $false
    | spl10_13 ),
    inference(subsumption_resolution,[],[f275,f138])).

fof(f138,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f136])).

fof(f136,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f100,f79])).

fof(f79,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f100,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f275,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK7),k1_xboole_0)
    | spl10_13 ),
    inference(resolution,[],[f272,f207])).

fof(f207,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | ~ r1_xboole_0(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f206])).

fof(f206,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,X3)
      | r1_xboole_0(X3,X2)
      | r1_xboole_0(X3,X2) ) ),
    inference(resolution,[],[f142,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f24,f55])).

fof(f55,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK9(X1,X2),X0)
      | ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f89,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f272,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK7))
    | spl10_13 ),
    inference(subsumption_resolution,[],[f271,f139])).

fof(f139,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f104,f74])).

fof(f271,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | spl10_13 ),
    inference(trivial_inequality_removal,[],[f270])).

fof(f270,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | spl10_13 ),
    inference(superposition,[],[f254,f86])).

fof(f254,plain,
    ( k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0)
    | spl10_13 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl10_13
  <=> k1_xboole_0 = k7_relat_1(sK7,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).

fof(f266,plain,(
    spl10_12 ),
    inference(avatar_contradiction_clause,[],[f265])).

fof(f265,plain,
    ( $false
    | spl10_12 ),
    inference(subsumption_resolution,[],[f261,f138])).

fof(f261,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK8),k1_xboole_0)
    | spl10_12 ),
    inference(resolution,[],[f250,f207])).

fof(f250,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK8))
    | spl10_12 ),
    inference(avatar_component_clause,[],[f248])).

fof(f255,plain,
    ( ~ spl10_12
    | ~ spl10_13
    | spl10_1 ),
    inference(avatar_split_clause,[],[f246,f119,f252,f248])).

fof(f246,plain,
    ( k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK8))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f245,f140])).

fof(f245,plain,
    ( k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK8))
    | ~ v1_relat_1(sK8)
    | spl10_1 ),
    inference(superposition,[],[f244,f86])).

fof(f244,plain,
    ( k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f243,f72])).

fof(f243,plain,
    ( k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | ~ v1_funct_1(sK7)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f242,f74])).

fof(f242,plain,
    ( k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(sK7)
    | spl10_1 ),
    inference(superposition,[],[f241,f107])).

fof(f241,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f240,f75])).

fof(f240,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0)
    | ~ v1_funct_1(sK8)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f235,f77])).

fof(f235,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | spl10_1 ),
    inference(superposition,[],[f220,f107])).

fof(f220,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f219,f202])).

fof(f219,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0)
    | ~ r1_xboole_0(sK5,sK6)
    | spl10_1 ),
    inference(superposition,[],[f218,f99])).

fof(f218,plain,
    ( k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f217,f70])).

fof(f217,plain,
    ( k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | spl10_1 ),
    inference(superposition,[],[f121,f103])).

fof(f121,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f130,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f78,f127,f123,f119])).

fof(f78,plain,
    ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)
    | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)
    | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) ),
    inference(cnf_transformation,[],[f49])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:30:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (24866)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.49  % (24856)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (24857)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (24855)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.51  % (24859)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.51  % (24860)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (24864)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  % (24865)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.52  % (24858)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.27/0.52  % (24878)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 1.27/0.52  % (24854)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.52  % (24872)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.27/0.52  % (24859)Refutation not found, incomplete strategy% (24859)------------------------------
% 1.27/0.52  % (24859)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (24853)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.27/0.53  % (24859)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (24859)Memory used [KB]: 11129
% 1.27/0.53  % (24859)Time elapsed: 0.091 s
% 1.27/0.53  % (24859)------------------------------
% 1.27/0.53  % (24859)------------------------------
% 1.27/0.53  % (24866)Refutation not found, incomplete strategy% (24866)------------------------------
% 1.27/0.53  % (24866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.27/0.53  % (24866)Termination reason: Refutation not found, incomplete strategy
% 1.27/0.53  
% 1.27/0.53  % (24866)Memory used [KB]: 7291
% 1.27/0.53  % (24866)Time elapsed: 0.085 s
% 1.27/0.53  % (24866)------------------------------
% 1.27/0.53  % (24866)------------------------------
% 1.27/0.53  % (24857)Refutation found. Thanks to Tanya!
% 1.27/0.53  % SZS status Theorem for theBenchmark
% 1.27/0.53  % SZS output start Proof for theBenchmark
% 1.27/0.53  fof(f825,plain,(
% 1.27/0.53    $false),
% 1.27/0.53    inference(avatar_sat_refutation,[],[f130,f255,f266,f280,f380,f439,f447,f514,f594,f674,f756,f824])).
% 1.27/0.53  fof(f824,plain,(
% 1.27/0.53    ~spl10_1 | spl10_3 | ~spl10_14 | ~spl10_15 | ~spl10_20 | ~spl10_32),
% 1.27/0.53    inference(avatar_contradiction_clause,[],[f823])).
% 1.27/0.53  fof(f823,plain,(
% 1.27/0.53    $false | (~spl10_1 | spl10_3 | ~spl10_14 | ~spl10_15 | ~spl10_20 | ~spl10_32)),
% 1.27/0.53    inference(subsumption_resolution,[],[f822,f749])).
% 1.27/0.53  fof(f749,plain,(
% 1.27/0.53    sP0(sK8,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,sK7) | (~spl10_1 | ~spl10_14 | ~spl10_15 | ~spl10_20 | ~spl10_32)),
% 1.27/0.53    inference(resolution,[],[f745,f112])).
% 1.27/0.53  fof(f112,plain,(
% 1.27/0.53    ( ! [X6,X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3,k1_tmap_1(X1,X3,X2,X5,X0,X6),X5,X6) | sP0(X6,X5,k1_tmap_1(X1,X3,X2,X5,X0,X6),X3,X2,X1,X0)) )),
% 1.27/0.53    inference(equality_resolution,[],[f80])).
% 1.27/0.53  fof(f80,plain,(
% 1.27/0.53    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0) | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4 | ~sP1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f51])).
% 1.27/0.53  fof(f51,plain,(
% 1.27/0.53    ! [X0,X1,X2,X3,X4,X5,X6] : (((k1_tmap_1(X1,X3,X2,X5,X0,X6) = X4 | ~sP0(X6,X5,X4,X3,X2,X1,X0)) & (sP0(X6,X5,X4,X3,X2,X1,X0) | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4)) | ~sP1(X0,X1,X2,X3,X4,X5,X6))),
% 1.27/0.53    inference(rectify,[],[f50])).
% 1.27/0.53  fof(f50,plain,(
% 1.27/0.53    ! [X4,X0,X2,X1,X6,X3,X5] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | ~sP0(X5,X3,X6,X1,X2,X0,X4)) & (sP0(X5,X3,X6,X1,X2,X0,X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~sP1(X4,X0,X2,X1,X6,X3,X5))),
% 1.27/0.53    inference(nnf_transformation,[],[f39])).
% 1.27/0.53  fof(f39,plain,(
% 1.27/0.53    ! [X4,X0,X2,X1,X6,X3,X5] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> sP0(X5,X3,X6,X1,X2,X0,X4)) | ~sP1(X4,X0,X2,X1,X6,X3,X5))),
% 1.27/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.27/0.53  fof(f745,plain,(
% 1.27/0.53    sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8) | (~spl10_1 | ~spl10_14 | ~spl10_15 | ~spl10_20 | ~spl10_32)),
% 1.27/0.53    inference(subsumption_resolution,[],[f744,f290])).
% 1.27/0.53  fof(f290,plain,(
% 1.27/0.53    v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) | ~spl10_14),
% 1.27/0.53    inference(avatar_component_clause,[],[f289])).
% 1.27/0.53  fof(f289,plain,(
% 1.27/0.53    spl10_14 <=> v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_14])])).
% 1.27/0.53  fof(f744,plain,(
% 1.27/0.53    ~v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) | sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8) | (~spl10_1 | ~spl10_15 | ~spl10_20 | ~spl10_32)),
% 1.27/0.53    inference(subsumption_resolution,[],[f741,f650])).
% 1.27/0.53  fof(f650,plain,(
% 1.27/0.53    v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) | ~spl10_32),
% 1.27/0.53    inference(avatar_component_clause,[],[f649])).
% 1.27/0.53  fof(f649,plain,(
% 1.27/0.53    spl10_32 <=> v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_32])])).
% 1.27/0.53  fof(f741,plain,(
% 1.27/0.53    ~v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) | sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8) | (~spl10_1 | ~spl10_15 | ~spl10_20)),
% 1.27/0.53    inference(resolution,[],[f740,f294])).
% 1.27/0.53  fof(f294,plain,(
% 1.27/0.53    m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~spl10_15),
% 1.27/0.53    inference(avatar_component_clause,[],[f293])).
% 1.27/0.53  fof(f293,plain,(
% 1.27/0.53    spl10_15 <=> m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_15])])).
% 1.27/0.53  fof(f740,plain,(
% 1.27/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)) ) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(subsumption_resolution,[],[f739,f72])).
% 1.27/0.53  fof(f72,plain,(
% 1.27/0.53    v1_funct_1(sK7)),
% 1.27/0.53    inference(cnf_transformation,[],[f49])).
% 1.27/0.53  fof(f49,plain,(
% 1.27/0.53    ((((((sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(sK8,sK6,sK4) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(sK7,sK5,sK4) & v1_funct_1(sK7)) & r1_subset_1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)),
% 1.27/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f20,f48,f47,f46,f45,f44,f43])).
% 1.27/0.53  % (24877)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 1.27/0.53  fof(f43,plain,(
% 1.27/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK3))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f44,plain,(
% 1.27/0.53    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK4,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK4))) & v1_funct_2(X4,X2,sK4) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK4))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f45,plain,(
% 1.27/0.53    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK4,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK4))) & v1_funct_2(X4,X2,sK4) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,sK5,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) & r1_subset_1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(sK5,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK5))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f46,plain,(
% 1.27/0.53    ? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,sK5,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) & r1_subset_1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK6) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) & r1_subset_1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK6))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f47,plain,(
% 1.27/0.53    ? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK6) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK6) != X5 | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK5) | k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(sK7,sK5,sK4) & v1_funct_1(sK7))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f48,plain,(
% 1.27/0.53    ? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK6) != X5 | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK5) | k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) => ((sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(sK8,sK6,sK4) & v1_funct_1(sK8))),
% 1.27/0.53    introduced(choice_axiom,[])).
% 1.27/0.53  fof(f20,plain,(
% 1.27/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.27/0.53    inference(flattening,[],[f19])).
% 1.27/0.53  fof(f19,plain,(
% 1.27/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.27/0.53    inference(ennf_transformation,[],[f17])).
% 1.27/0.53  fof(f17,negated_conjecture,(
% 1.27/0.53    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.27/0.53    inference(negated_conjecture,[],[f16])).
% 1.27/0.53  fof(f16,conjecture,(
% 1.27/0.53    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 1.27/0.53  fof(f739,plain,(
% 1.27/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~v1_funct_1(sK7)) ) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(subsumption_resolution,[],[f738,f73])).
% 1.27/0.53  fof(f73,plain,(
% 1.27/0.53    v1_funct_2(sK7,sK5,sK4)),
% 1.27/0.53    inference(cnf_transformation,[],[f49])).
% 1.27/0.53  fof(f738,plain,(
% 1.27/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7)) ) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(subsumption_resolution,[],[f736,f74])).
% 1.27/0.53  fof(f74,plain,(
% 1.27/0.53    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 1.27/0.53    inference(cnf_transformation,[],[f49])).
% 1.27/0.53  fof(f736,plain,(
% 1.27/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7)) ) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(trivial_inequality_removal,[],[f733])).
% 1.27/0.53  fof(f733,plain,(
% 1.27/0.53    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7)) ) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(superposition,[],[f559,f469])).
% 1.27/0.53  fof(f469,plain,(
% 1.27/0.53    k1_xboole_0 = k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(forward_demodulation,[],[f309,f453])).
% 1.27/0.53  fof(f453,plain,(
% 1.27/0.53    k1_xboole_0 = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(backward_demodulation,[],[f419,f436])).
% 1.27/0.53  fof(f436,plain,(
% 1.27/0.53    k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~spl10_20),
% 1.27/0.53    inference(avatar_component_clause,[],[f434])).
% 1.27/0.53  fof(f434,plain,(
% 1.27/0.53    spl10_20 <=> k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_20])])).
% 1.27/0.53  fof(f419,plain,(
% 1.27/0.53    k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.27/0.53    inference(subsumption_resolution,[],[f418,f72])).
% 1.27/0.53  fof(f418,plain,(
% 1.27/0.53    k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~v1_funct_1(sK7) | ~spl10_1),
% 1.27/0.53    inference(subsumption_resolution,[],[f414,f74])).
% 1.27/0.53  fof(f414,plain,(
% 1.27/0.53    k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_1(sK7) | ~spl10_1),
% 1.27/0.53    inference(superposition,[],[f307,f107])).
% 1.27/0.53  fof(f107,plain,(
% 1.27/0.53    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.27/0.53    inference(cnf_transformation,[],[f35])).
% 1.27/0.53  fof(f35,plain,(
% 1.27/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.27/0.53    inference(flattening,[],[f34])).
% 1.27/0.53  fof(f34,plain,(
% 1.27/0.53    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.27/0.53    inference(ennf_transformation,[],[f13])).
% 1.27/0.53  fof(f13,axiom,(
% 1.27/0.53    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.27/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.27/0.53  fof(f307,plain,(
% 1.27/0.53    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.27/0.53    inference(subsumption_resolution,[],[f306,f75])).
% 1.27/0.53  fof(f75,plain,(
% 1.27/0.53    v1_funct_1(sK8)),
% 1.27/0.53    inference(cnf_transformation,[],[f49])).
% 1.27/0.53  fof(f306,plain,(
% 1.27/0.53    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~v1_funct_1(sK8) | ~spl10_1),
% 1.27/0.53    inference(subsumption_resolution,[],[f303,f77])).
% 1.27/0.53  fof(f77,plain,(
% 1.27/0.53    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 1.27/0.53    inference(cnf_transformation,[],[f49])).
% 1.27/0.53  fof(f303,plain,(
% 1.27/0.53    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_1(sK8) | ~spl10_1),
% 1.27/0.53    inference(superposition,[],[f120,f107])).
% 1.27/0.53  fof(f120,plain,(
% 1.27/0.53    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.27/0.53    inference(avatar_component_clause,[],[f119])).
% 1.27/0.53  fof(f119,plain,(
% 1.27/0.53    spl10_1 <=> k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))),
% 1.27/0.53    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.27/0.53  fof(f309,plain,(
% 1.27/0.53    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.27/0.53    inference(subsumption_resolution,[],[f308,f75])).
% 1.27/0.53  fof(f308,plain,(
% 1.27/0.53    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~v1_funct_1(sK8) | ~spl10_1),
% 1.27/0.53    inference(subsumption_resolution,[],[f304,f77])).
% 1.27/0.53  fof(f304,plain,(
% 1.27/0.53    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_1(sK8) | ~spl10_1),
% 1.27/0.53    inference(superposition,[],[f107,f120])).
% 1.27/0.53  fof(f559,plain,(
% 1.27/0.53    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7)) ) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(subsumption_resolution,[],[f558,f65])).
% 1.27/0.53  fof(f65,plain,(
% 1.27/0.53    ~v1_xboole_0(sK3)),
% 1.27/0.53    inference(cnf_transformation,[],[f49])).
% 1.27/0.53  fof(f558,plain,(
% 1.27/0.53    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | v1_xboole_0(sK3)) ) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(subsumption_resolution,[],[f557,f66])).
% 1.27/0.53  fof(f66,plain,(
% 1.27/0.53    ~v1_xboole_0(sK4)),
% 1.27/0.53    inference(cnf_transformation,[],[f49])).
% 1.27/0.53  fof(f557,plain,(
% 1.27/0.53    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | v1_xboole_0(sK4) | v1_xboole_0(sK3)) ) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(subsumption_resolution,[],[f556,f67])).
% 1.27/0.53  fof(f67,plain,(
% 1.27/0.53    ~v1_xboole_0(sK5)),
% 1.27/0.53    inference(cnf_transformation,[],[f49])).
% 1.27/0.53  fof(f556,plain,(
% 1.27/0.53    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3)) ) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(subsumption_resolution,[],[f555,f68])).
% 1.27/0.53  fof(f68,plain,(
% 1.27/0.53    m1_subset_1(sK5,k1_zfmisc_1(sK3))),
% 1.27/0.53    inference(cnf_transformation,[],[f49])).
% 1.27/0.53  fof(f555,plain,(
% 1.27/0.53    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3)) ) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(subsumption_resolution,[],[f554,f69])).
% 1.27/0.53  fof(f69,plain,(
% 1.27/0.53    ~v1_xboole_0(sK6)),
% 1.27/0.53    inference(cnf_transformation,[],[f49])).
% 1.27/0.53  fof(f554,plain,(
% 1.27/0.53    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3)) ) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(subsumption_resolution,[],[f553,f70])).
% 1.27/0.53  fof(f70,plain,(
% 1.27/0.53    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 1.27/0.53    inference(cnf_transformation,[],[f49])).
% 1.27/0.53  fof(f553,plain,(
% 1.27/0.53    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3)) ) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(subsumption_resolution,[],[f552,f75])).
% 1.27/0.53  fof(f552,plain,(
% 1.27/0.53    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~v1_funct_1(sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3)) ) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(subsumption_resolution,[],[f551,f76])).
% 1.27/0.53  fof(f76,plain,(
% 1.27/0.53    v1_funct_2(sK8,sK6,sK4)),
% 1.27/0.53    inference(cnf_transformation,[],[f49])).
% 1.27/0.53  fof(f551,plain,(
% 1.27/0.53    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3)) ) | (~spl10_1 | ~spl10_20)),
% 1.27/0.53    inference(subsumption_resolution,[],[f545,f77])).
% 1.27/0.53  % (24875)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.27/0.53  % (24870)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.27/0.53  % (24880)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.41/0.54  % (24873)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.41/0.54  % (24879)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.41/0.54  % (24863)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.41/0.54  fof(f545,plain,(
% 1.41/0.54    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3)) ) | (~spl10_1 | ~spl10_20)),
% 1.41/0.54    inference(superposition,[],[f85,f458])).
% 1.41/0.54  fof(f458,plain,(
% 1.41/0.54    k1_xboole_0 = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) | (~spl10_1 | ~spl10_20)),
% 1.41/0.54    inference(forward_demodulation,[],[f452,f436])).
% 1.41/0.54  fof(f452,plain,(
% 1.41/0.54    k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.41/0.54    inference(forward_demodulation,[],[f412,f419])).
% 1.41/0.54  fof(f412,plain,(
% 1.41/0.54    k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.41/0.54    inference(backward_demodulation,[],[f120,f307])).
% 1.41/0.54  fof(f85,plain,(
% 1.41/0.54    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | sP1(X4,X0,X2,X1,X6,X3,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.41/0.54    inference(cnf_transformation,[],[f40])).
% 1.41/0.54  fof(f40,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (sP1(X4,X0,X2,X1,X6,X3,X5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.41/0.54    inference(definition_folding,[],[f22,f39,f38])).
% 1.41/0.54  % (24868)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.41/0.54  fof(f38,plain,(
% 1.41/0.54    ! [X5,X3,X6,X1,X2,X0,X4] : (sP0(X5,X3,X6,X1,X2,X0,X4) <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))),
% 1.41/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.41/0.54  fof(f22,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.41/0.54    inference(flattening,[],[f21])).
% 1.41/0.54  fof(f21,plain,(
% 1.41/0.54    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.41/0.54    inference(ennf_transformation,[],[f14])).
% 1.41/0.55  fof(f14,axiom,(
% 1.41/0.55    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.41/0.55  fof(f822,plain,(
% 1.41/0.55    ~sP0(sK8,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,sK7) | (~spl10_1 | spl10_3 | ~spl10_14 | ~spl10_15 | ~spl10_20 | ~spl10_32)),
% 1.41/0.55    inference(resolution,[],[f797,f745])).
% 1.41/0.55  fof(f797,plain,(
% 1.41/0.55    ( ! [X0] : (~sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~sP0(sK8,sK6,X0,sK4,sK5,sK3,sK7)) ) | spl10_3),
% 1.41/0.55    inference(subsumption_resolution,[],[f794,f83])).
% 1.41/0.55  fof(f83,plain,(
% 1.41/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f54])).
% 1.41/0.55  fof(f54,plain,(
% 1.41/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) != X0 | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) != X6) & ((k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0 & k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 1.41/0.55    inference(rectify,[],[f53])).
% 1.41/0.55  fof(f53,plain,(
% 1.41/0.55    ! [X5,X3,X6,X1,X2,X0,X4] : ((sP0(X5,X3,X6,X1,X2,X0,X4) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | ~sP0(X5,X3,X6,X1,X2,X0,X4)))),
% 1.41/0.55    inference(flattening,[],[f52])).
% 1.41/0.55  fof(f52,plain,(
% 1.41/0.55    ! [X5,X3,X6,X1,X2,X0,X4] : ((sP0(X5,X3,X6,X1,X2,X0,X4) | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | ~sP0(X5,X3,X6,X1,X2,X0,X4)))),
% 1.41/0.55    inference(nnf_transformation,[],[f38])).
% 1.41/0.55  fof(f794,plain,(
% 1.41/0.55    ( ! [X0] : (sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,X0,sK6) | ~sP0(sK8,sK6,X0,sK4,sK5,sK3,sK7) | ~sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)) ) | spl10_3),
% 1.41/0.55    inference(superposition,[],[f129,f81])).
% 1.41/0.55  fof(f81,plain,(
% 1.41/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_tmap_1(X1,X3,X2,X5,X0,X6) = X4 | ~sP0(X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f51])).
% 1.41/0.55  fof(f129,plain,(
% 1.41/0.55    sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | spl10_3),
% 1.41/0.55    inference(avatar_component_clause,[],[f127])).
% 1.41/0.55  fof(f127,plain,(
% 1.41/0.55    spl10_3 <=> sK8 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.41/0.55  fof(f756,plain,(
% 1.41/0.55    ~spl10_1 | spl10_2 | ~spl10_14 | ~spl10_15 | ~spl10_20 | ~spl10_32),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f755])).
% 1.41/0.55  fof(f755,plain,(
% 1.41/0.55    $false | (~spl10_1 | spl10_2 | ~spl10_14 | ~spl10_15 | ~spl10_20 | ~spl10_32)),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f751])).
% 1.41/0.55  fof(f751,plain,(
% 1.41/0.55    sK7 != sK7 | (~spl10_1 | spl10_2 | ~spl10_14 | ~spl10_15 | ~spl10_20 | ~spl10_32)),
% 1.41/0.55    inference(resolution,[],[f749,f286])).
% 1.41/0.55  fof(f286,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~sP0(X1,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,X0) | sK7 != X0) ) | spl10_2),
% 1.41/0.55    inference(superposition,[],[f125,f82])).
% 1.41/0.55  fof(f82,plain,(
% 1.41/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f54])).
% 1.41/0.55  fof(f125,plain,(
% 1.41/0.55    sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | spl10_2),
% 1.41/0.55    inference(avatar_component_clause,[],[f123])).
% 1.41/0.55  fof(f123,plain,(
% 1.41/0.55    spl10_2 <=> sK7 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.41/0.55  fof(f674,plain,(
% 1.41/0.55    spl10_32),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f673])).
% 1.41/0.55  fof(f673,plain,(
% 1.41/0.55    $false | spl10_32),
% 1.41/0.55    inference(subsumption_resolution,[],[f672,f65])).
% 1.41/0.55  fof(f672,plain,(
% 1.41/0.55    v1_xboole_0(sK3) | spl10_32),
% 1.41/0.55    inference(subsumption_resolution,[],[f671,f66])).
% 1.41/0.55  fof(f671,plain,(
% 1.41/0.55    v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_32),
% 1.41/0.55    inference(subsumption_resolution,[],[f670,f67])).
% 1.41/0.55  fof(f670,plain,(
% 1.41/0.55    v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_32),
% 1.41/0.55    inference(subsumption_resolution,[],[f669,f68])).
% 1.41/0.55  fof(f669,plain,(
% 1.41/0.55    ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_32),
% 1.41/0.55    inference(subsumption_resolution,[],[f668,f69])).
% 1.41/0.55  fof(f668,plain,(
% 1.41/0.55    v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_32),
% 1.41/0.55    inference(subsumption_resolution,[],[f667,f70])).
% 1.41/0.55  fof(f667,plain,(
% 1.41/0.55    ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_32),
% 1.41/0.55    inference(subsumption_resolution,[],[f666,f72])).
% 1.41/0.55  fof(f666,plain,(
% 1.41/0.55    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_32),
% 1.41/0.55    inference(subsumption_resolution,[],[f665,f73])).
% 1.41/0.55  fof(f665,plain,(
% 1.41/0.55    ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_32),
% 1.41/0.55    inference(subsumption_resolution,[],[f664,f74])).
% 1.41/0.55  fof(f664,plain,(
% 1.41/0.55    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_32),
% 1.41/0.55    inference(subsumption_resolution,[],[f663,f75])).
% 1.41/0.55  fof(f663,plain,(
% 1.41/0.55    ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_32),
% 1.41/0.55    inference(subsumption_resolution,[],[f662,f76])).
% 1.41/0.55  fof(f662,plain,(
% 1.41/0.55    ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_32),
% 1.41/0.55    inference(subsumption_resolution,[],[f661,f77])).
% 1.41/0.55  fof(f661,plain,(
% 1.41/0.55    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_32),
% 1.41/0.55    inference(resolution,[],[f659,f111])).
% 1.41/0.55  fof(f111,plain,(
% 1.41/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (sP2(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f42])).
% 1.41/0.55  fof(f42,plain,(
% 1.41/0.55    ! [X0,X1,X2,X3,X4,X5] : (sP2(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.41/0.55    inference(definition_folding,[],[f37,f41])).
% 1.41/0.55  fof(f41,plain,(
% 1.41/0.55    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP2(X1,X3,X2,X0,X5,X4))),
% 1.41/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.41/0.55  fof(f37,plain,(
% 1.41/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.41/0.55    inference(flattening,[],[f36])).
% 1.41/0.55  fof(f36,plain,(
% 1.41/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f15])).
% 1.41/0.55  fof(f15,axiom,(
% 1.41/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.41/0.55  fof(f659,plain,(
% 1.41/0.55    ~sP2(sK4,sK6,sK5,sK3,sK8,sK7) | spl10_32),
% 1.41/0.55    inference(resolution,[],[f651,f109])).
% 1.41/0.55  fof(f109,plain,(
% 1.41/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f64])).
% 1.41/0.55  fof(f64,plain,(
% 1.41/0.55    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0))) & v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0) & v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4))) | ~sP2(X0,X1,X2,X3,X4,X5))),
% 1.41/0.55    inference(rectify,[],[f63])).
% 1.41/0.55  fof(f63,plain,(
% 1.41/0.55    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP2(X1,X3,X2,X0,X5,X4))),
% 1.41/0.55    inference(nnf_transformation,[],[f41])).
% 1.41/0.55  fof(f651,plain,(
% 1.41/0.55    ~v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) | spl10_32),
% 1.41/0.55    inference(avatar_component_clause,[],[f649])).
% 1.41/0.55  fof(f594,plain,(
% 1.41/0.55    spl10_15),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f593])).
% 1.41/0.55  fof(f593,plain,(
% 1.41/0.55    $false | spl10_15),
% 1.41/0.55    inference(subsumption_resolution,[],[f592,f65])).
% 1.41/0.55  fof(f592,plain,(
% 1.41/0.55    v1_xboole_0(sK3) | spl10_15),
% 1.41/0.55    inference(subsumption_resolution,[],[f591,f66])).
% 1.41/0.55  fof(f591,plain,(
% 1.41/0.55    v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_15),
% 1.41/0.55    inference(subsumption_resolution,[],[f590,f67])).
% 1.41/0.55  fof(f590,plain,(
% 1.41/0.55    v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_15),
% 1.41/0.55    inference(subsumption_resolution,[],[f589,f68])).
% 1.41/0.55  fof(f589,plain,(
% 1.41/0.55    ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_15),
% 1.41/0.55    inference(subsumption_resolution,[],[f588,f69])).
% 1.41/0.55  fof(f588,plain,(
% 1.41/0.55    v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_15),
% 1.41/0.55    inference(subsumption_resolution,[],[f587,f70])).
% 1.41/0.55  fof(f587,plain,(
% 1.41/0.55    ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_15),
% 1.41/0.55    inference(subsumption_resolution,[],[f586,f72])).
% 1.41/0.55  fof(f586,plain,(
% 1.41/0.55    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_15),
% 1.41/0.55    inference(subsumption_resolution,[],[f585,f73])).
% 1.41/0.55  fof(f585,plain,(
% 1.41/0.55    ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_15),
% 1.41/0.55    inference(subsumption_resolution,[],[f584,f74])).
% 1.41/0.55  fof(f584,plain,(
% 1.41/0.55    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_15),
% 1.41/0.55    inference(subsumption_resolution,[],[f583,f75])).
% 1.41/0.55  fof(f583,plain,(
% 1.41/0.55    ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_15),
% 1.41/0.55    inference(subsumption_resolution,[],[f582,f76])).
% 1.41/0.55  fof(f582,plain,(
% 1.41/0.55    ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_15),
% 1.41/0.55    inference(subsumption_resolution,[],[f581,f77])).
% 1.41/0.55  fof(f581,plain,(
% 1.41/0.55    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_15),
% 1.41/0.55    inference(resolution,[],[f578,f111])).
% 1.41/0.55  fof(f578,plain,(
% 1.41/0.55    ~sP2(sK4,sK6,sK5,sK3,sK8,sK7) | spl10_15),
% 1.41/0.55    inference(resolution,[],[f295,f110])).
% 1.41/0.55  fof(f110,plain,(
% 1.41/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0))) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f64])).
% 1.41/0.55  fof(f295,plain,(
% 1.41/0.55    ~m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | spl10_15),
% 1.41/0.55    inference(avatar_component_clause,[],[f293])).
% 1.41/0.55  fof(f514,plain,(
% 1.41/0.55    spl10_14),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f513])).
% 1.41/0.55  fof(f513,plain,(
% 1.41/0.55    $false | spl10_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f512,f65])).
% 1.41/0.55  fof(f512,plain,(
% 1.41/0.55    v1_xboole_0(sK3) | spl10_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f511,f66])).
% 1.41/0.55  fof(f511,plain,(
% 1.41/0.55    v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f510,f67])).
% 1.41/0.55  fof(f510,plain,(
% 1.41/0.55    v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f509,f68])).
% 1.41/0.55  fof(f509,plain,(
% 1.41/0.55    ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f508,f69])).
% 1.41/0.55  fof(f508,plain,(
% 1.41/0.55    v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f507,f70])).
% 1.41/0.55  fof(f507,plain,(
% 1.41/0.55    ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f506,f72])).
% 1.41/0.55  fof(f506,plain,(
% 1.41/0.55    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f505,f73])).
% 1.41/0.55  fof(f505,plain,(
% 1.41/0.55    ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f504,f74])).
% 1.41/0.55  fof(f504,plain,(
% 1.41/0.55    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f503,f75])).
% 1.41/0.55  fof(f503,plain,(
% 1.41/0.55    ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f502,f76])).
% 1.41/0.55  fof(f502,plain,(
% 1.41/0.55    ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_14),
% 1.41/0.55    inference(subsumption_resolution,[],[f501,f77])).
% 1.41/0.55  fof(f501,plain,(
% 1.41/0.55    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | v1_xboole_0(sK3) | spl10_14),
% 1.41/0.55    inference(resolution,[],[f111,f301])).
% 1.41/0.55  fof(f301,plain,(
% 1.41/0.55    ~sP2(sK4,sK6,sK5,sK3,sK8,sK7) | spl10_14),
% 1.41/0.55    inference(resolution,[],[f291,f108])).
% 1.41/0.55  fof(f108,plain,(
% 1.41/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4)) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f64])).
% 1.41/0.55  fof(f291,plain,(
% 1.41/0.55    ~v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) | spl10_14),
% 1.41/0.55    inference(avatar_component_clause,[],[f289])).
% 1.41/0.55  fof(f447,plain,(
% 1.41/0.55    ~spl10_17 | spl10_19),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f446])).
% 1.41/0.55  fof(f446,plain,(
% 1.41/0.55    $false | (~spl10_17 | spl10_19)),
% 1.41/0.55    inference(subsumption_resolution,[],[f445,f70])).
% 1.41/0.55  fof(f445,plain,(
% 1.41/0.55    ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | (~spl10_17 | spl10_19)),
% 1.41/0.55    inference(subsumption_resolution,[],[f443,f364])).
% 1.41/0.55  fof(f364,plain,(
% 1.41/0.55    r1_xboole_0(k3_xboole_0(sK5,sK6),k1_relat_1(sK8)) | ~spl10_17),
% 1.41/0.55    inference(avatar_component_clause,[],[f363])).
% 1.41/0.55  fof(f363,plain,(
% 1.41/0.55    spl10_17 <=> r1_xboole_0(k3_xboole_0(sK5,sK6),k1_relat_1(sK8))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 1.41/0.55  fof(f443,plain,(
% 1.41/0.55    ~r1_xboole_0(k3_xboole_0(sK5,sK6),k1_relat_1(sK8)) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | spl10_19),
% 1.41/0.55    inference(superposition,[],[f432,f103])).
% 1.41/0.55  fof(f103,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.41/0.55    inference(cnf_transformation,[],[f31])).
% 1.41/0.55  fof(f31,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f5])).
% 1.41/0.55  fof(f5,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.41/0.55  fof(f432,plain,(
% 1.41/0.55    ~r1_xboole_0(k9_subset_1(sK3,sK5,sK6),k1_relat_1(sK8)) | spl10_19),
% 1.41/0.55    inference(avatar_component_clause,[],[f430])).
% 1.41/0.55  fof(f430,plain,(
% 1.41/0.55    spl10_19 <=> r1_xboole_0(k9_subset_1(sK3,sK5,sK6),k1_relat_1(sK8))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 1.41/0.55  fof(f439,plain,(
% 1.41/0.55    ~spl10_19 | spl10_20 | ~spl10_1),
% 1.41/0.55    inference(avatar_split_clause,[],[f438,f119,f434,f430])).
% 1.41/0.55  fof(f438,plain,(
% 1.41/0.55    k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~r1_xboole_0(k9_subset_1(sK3,sK5,sK6),k1_relat_1(sK8)) | ~spl10_1),
% 1.41/0.55    inference(subsumption_resolution,[],[f425,f140])).
% 1.41/0.55  fof(f140,plain,(
% 1.41/0.55    v1_relat_1(sK8)),
% 1.41/0.55    inference(resolution,[],[f104,f77])).
% 1.41/0.55  fof(f104,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f32])).
% 1.41/0.55  fof(f32,plain,(
% 1.41/0.55    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.41/0.55    inference(ennf_transformation,[],[f9])).
% 1.41/0.55  fof(f9,axiom,(
% 1.41/0.55    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.41/0.55  fof(f425,plain,(
% 1.41/0.55    k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~r1_xboole_0(k9_subset_1(sK3,sK5,sK6),k1_relat_1(sK8)) | ~v1_relat_1(sK8) | ~spl10_1),
% 1.41/0.55    inference(superposition,[],[f86,f419])).
% 1.41/0.55  fof(f86,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f23])).
% 1.41/0.55  fof(f23,plain,(
% 1.41/0.55    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.41/0.55    inference(ennf_transformation,[],[f7])).
% 1.41/0.55  fof(f7,axiom,(
% 1.41/0.55    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 1.41/0.55  fof(f380,plain,(
% 1.41/0.55    ~spl10_12 | spl10_17),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f379])).
% 1.41/0.55  fof(f379,plain,(
% 1.41/0.55    $false | (~spl10_12 | spl10_17)),
% 1.41/0.55    inference(subsumption_resolution,[],[f378,f202])).
% 1.41/0.55  fof(f202,plain,(
% 1.41/0.55    r1_xboole_0(sK5,sK6)),
% 1.41/0.55    inference(subsumption_resolution,[],[f201,f67])).
% 1.41/0.55  fof(f201,plain,(
% 1.41/0.55    r1_xboole_0(sK5,sK6) | v1_xboole_0(sK5)),
% 1.41/0.55    inference(subsumption_resolution,[],[f200,f69])).
% 1.41/0.55  fof(f200,plain,(
% 1.41/0.55    r1_xboole_0(sK5,sK6) | v1_xboole_0(sK6) | v1_xboole_0(sK5)),
% 1.41/0.55    inference(resolution,[],[f92,f71])).
% 1.41/0.55  fof(f71,plain,(
% 1.41/0.55    r1_subset_1(sK5,sK6)),
% 1.41/0.55    inference(cnf_transformation,[],[f49])).
% 1.41/0.55  fof(f92,plain,(
% 1.41/0.55    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f57])).
% 1.41/0.55  fof(f57,plain,(
% 1.41/0.55    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.41/0.55    inference(nnf_transformation,[],[f28])).
% 1.41/0.55  fof(f28,plain,(
% 1.41/0.55    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.41/0.55    inference(flattening,[],[f27])).
% 1.41/0.55  fof(f27,plain,(
% 1.41/0.55    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.41/0.55    inference(ennf_transformation,[],[f8])).
% 1.41/0.55  fof(f8,axiom,(
% 1.41/0.55    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.41/0.55  fof(f378,plain,(
% 1.41/0.55    ~r1_xboole_0(sK5,sK6) | (~spl10_12 | spl10_17)),
% 1.41/0.55    inference(subsumption_resolution,[],[f376,f249])).
% 1.41/0.55  fof(f249,plain,(
% 1.41/0.55    r1_xboole_0(k1_xboole_0,k1_relat_1(sK8)) | ~spl10_12),
% 1.41/0.55    inference(avatar_component_clause,[],[f248])).
% 1.41/0.55  fof(f248,plain,(
% 1.41/0.55    spl10_12 <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK8))),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_12])])).
% 1.41/0.55  fof(f376,plain,(
% 1.41/0.55    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK8)) | ~r1_xboole_0(sK5,sK6) | spl10_17),
% 1.41/0.55    inference(superposition,[],[f365,f99])).
% 1.41/0.55  fof(f99,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f61])).
% 1.41/0.55  fof(f61,plain,(
% 1.41/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.41/0.55    inference(nnf_transformation,[],[f1])).
% 1.41/0.55  fof(f1,axiom,(
% 1.41/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.41/0.55  fof(f365,plain,(
% 1.41/0.55    ~r1_xboole_0(k3_xboole_0(sK5,sK6),k1_relat_1(sK8)) | spl10_17),
% 1.41/0.55    inference(avatar_component_clause,[],[f363])).
% 1.41/0.55  fof(f280,plain,(
% 1.41/0.55    spl10_13),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f279])).
% 1.41/0.55  fof(f279,plain,(
% 1.41/0.55    $false | spl10_13),
% 1.41/0.55    inference(subsumption_resolution,[],[f275,f138])).
% 1.41/0.55  fof(f138,plain,(
% 1.41/0.55    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f136])).
% 1.41/0.55  fof(f136,plain,(
% 1.41/0.55    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(X0,k1_xboole_0)) )),
% 1.41/0.55    inference(superposition,[],[f100,f79])).
% 1.41/0.55  fof(f79,plain,(
% 1.41/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f4])).
% 1.41/0.55  fof(f4,axiom,(
% 1.41/0.55    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.41/0.55  fof(f100,plain,(
% 1.41/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f61])).
% 1.41/0.55  fof(f275,plain,(
% 1.41/0.55    ~r1_xboole_0(k1_relat_1(sK7),k1_xboole_0) | spl10_13),
% 1.41/0.55    inference(resolution,[],[f272,f207])).
% 1.41/0.55  fof(f207,plain,(
% 1.41/0.55    ( ! [X2,X3] : (r1_xboole_0(X3,X2) | ~r1_xboole_0(X2,X3)) )),
% 1.41/0.55    inference(duplicate_literal_removal,[],[f206])).
% 1.41/0.55  fof(f206,plain,(
% 1.41/0.55    ( ! [X2,X3] : (~r1_xboole_0(X2,X3) | r1_xboole_0(X3,X2) | r1_xboole_0(X3,X2)) )),
% 1.41/0.55    inference(resolution,[],[f142,f88])).
% 1.41/0.55  fof(f88,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f56])).
% 1.41/0.55  fof(f56,plain,(
% 1.41/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.41/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f24,f55])).
% 1.41/0.55  fof(f55,plain,(
% 1.41/0.55    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 1.41/0.55    introduced(choice_axiom,[])).
% 1.41/0.55  fof(f24,plain,(
% 1.41/0.55    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.41/0.55    inference(ennf_transformation,[],[f18])).
% 1.41/0.55  fof(f18,plain,(
% 1.41/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.41/0.55    inference(rectify,[],[f2])).
% 1.41/0.55  fof(f2,axiom,(
% 1.41/0.55    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.41/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.41/0.55  fof(f142,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~r2_hidden(sK9(X1,X2),X0) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X2)) )),
% 1.41/0.55    inference(resolution,[],[f89,f87])).
% 1.41/0.55  fof(f87,plain,(
% 1.41/0.55    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f56])).
% 1.41/0.55  fof(f89,plain,(
% 1.41/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X0)) )),
% 1.41/0.55    inference(cnf_transformation,[],[f56])).
% 1.41/0.55  fof(f272,plain,(
% 1.41/0.55    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK7)) | spl10_13),
% 1.41/0.55    inference(subsumption_resolution,[],[f271,f139])).
% 1.41/0.55  fof(f139,plain,(
% 1.41/0.55    v1_relat_1(sK7)),
% 1.41/0.55    inference(resolution,[],[f104,f74])).
% 1.41/0.55  fof(f271,plain,(
% 1.41/0.55    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK7)) | ~v1_relat_1(sK7) | spl10_13),
% 1.41/0.55    inference(trivial_inequality_removal,[],[f270])).
% 1.41/0.55  fof(f270,plain,(
% 1.41/0.55    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK7)) | ~v1_relat_1(sK7) | spl10_13),
% 1.41/0.55    inference(superposition,[],[f254,f86])).
% 1.41/0.55  fof(f254,plain,(
% 1.41/0.55    k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0) | spl10_13),
% 1.41/0.55    inference(avatar_component_clause,[],[f252])).
% 1.41/0.55  fof(f252,plain,(
% 1.41/0.55    spl10_13 <=> k1_xboole_0 = k7_relat_1(sK7,k1_xboole_0)),
% 1.41/0.55    introduced(avatar_definition,[new_symbols(naming,[spl10_13])])).
% 1.41/0.55  fof(f266,plain,(
% 1.41/0.55    spl10_12),
% 1.41/0.55    inference(avatar_contradiction_clause,[],[f265])).
% 1.41/0.55  fof(f265,plain,(
% 1.41/0.55    $false | spl10_12),
% 1.41/0.55    inference(subsumption_resolution,[],[f261,f138])).
% 1.41/0.55  fof(f261,plain,(
% 1.41/0.55    ~r1_xboole_0(k1_relat_1(sK8),k1_xboole_0) | spl10_12),
% 1.41/0.55    inference(resolution,[],[f250,f207])).
% 1.41/0.55  fof(f250,plain,(
% 1.41/0.55    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK8)) | spl10_12),
% 1.41/0.55    inference(avatar_component_clause,[],[f248])).
% 1.41/0.55  fof(f255,plain,(
% 1.41/0.55    ~spl10_12 | ~spl10_13 | spl10_1),
% 1.41/0.55    inference(avatar_split_clause,[],[f246,f119,f252,f248])).
% 1.41/0.55  fof(f246,plain,(
% 1.41/0.55    k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK8)) | spl10_1),
% 1.41/0.55    inference(subsumption_resolution,[],[f245,f140])).
% 1.41/0.55  fof(f245,plain,(
% 1.41/0.55    k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK8)) | ~v1_relat_1(sK8) | spl10_1),
% 1.41/0.55    inference(superposition,[],[f244,f86])).
% 1.41/0.55  fof(f244,plain,(
% 1.41/0.55    k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) | spl10_1),
% 1.41/0.55    inference(subsumption_resolution,[],[f243,f72])).
% 1.41/0.55  fof(f243,plain,(
% 1.41/0.55    k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) | ~v1_funct_1(sK7) | spl10_1),
% 1.41/0.55    inference(subsumption_resolution,[],[f242,f74])).
% 1.41/0.55  fof(f242,plain,(
% 1.41/0.55    k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_1(sK7) | spl10_1),
% 1.41/0.55    inference(superposition,[],[f241,f107])).
% 1.41/0.55  fof(f241,plain,(
% 1.41/0.55    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0) | spl10_1),
% 1.41/0.55    inference(subsumption_resolution,[],[f240,f75])).
% 1.41/0.55  fof(f240,plain,(
% 1.41/0.55    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0) | ~v1_funct_1(sK8) | spl10_1),
% 1.41/0.55    inference(subsumption_resolution,[],[f235,f77])).
% 1.41/0.55  fof(f235,plain,(
% 1.41/0.55    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_1(sK8) | spl10_1),
% 1.41/0.55    inference(superposition,[],[f220,f107])).
% 1.41/0.55  fof(f220,plain,(
% 1.41/0.55    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0) | spl10_1),
% 1.41/0.55    inference(subsumption_resolution,[],[f219,f202])).
% 1.41/0.55  fof(f219,plain,(
% 1.41/0.55    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0) | ~r1_xboole_0(sK5,sK6) | spl10_1),
% 1.41/0.55    inference(superposition,[],[f218,f99])).
% 1.41/0.55  fof(f218,plain,(
% 1.41/0.55    k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6)) | spl10_1),
% 1.41/0.55    inference(subsumption_resolution,[],[f217,f70])).
% 1.41/0.55  fof(f217,plain,(
% 1.41/0.55    k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | spl10_1),
% 1.41/0.55    inference(superposition,[],[f121,f103])).
% 1.41/0.55  fof(f121,plain,(
% 1.41/0.55    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) | spl10_1),
% 1.41/0.55    inference(avatar_component_clause,[],[f119])).
% 1.41/0.55  fof(f130,plain,(
% 1.41/0.55    ~spl10_1 | ~spl10_2 | ~spl10_3),
% 1.41/0.55    inference(avatar_split_clause,[],[f78,f127,f123,f119])).
% 1.41/0.55  fof(f78,plain,(
% 1.41/0.55    sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))),
% 1.41/0.55    inference(cnf_transformation,[],[f49])).
% 1.41/0.55  % SZS output end Proof for theBenchmark
% 1.41/0.55  % (24857)------------------------------
% 1.41/0.55  % (24857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.55  % (24857)Termination reason: Refutation
% 1.41/0.55  
% 1.41/0.55  % (24857)Memory used [KB]: 6652
% 1.41/0.55  % (24857)Time elapsed: 0.104 s
% 1.41/0.55  % (24857)------------------------------
% 1.41/0.55  % (24857)------------------------------
% 1.41/0.55  % (24874)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.41/0.55  % (24844)Success in time 0.192 s
%------------------------------------------------------------------------------
