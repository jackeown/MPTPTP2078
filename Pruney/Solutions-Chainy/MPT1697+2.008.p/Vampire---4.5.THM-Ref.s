%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  254 (2088 expanded)
%              Number of leaves         :   36 ( 973 expanded)
%              Depth                    :   34
%              Number of atoms          : 1331 (29555 expanded)
%              Number of equality atoms :  167 (6458 expanded)
%              Maximal formula depth    :   24 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (3908)Termination reason: Refutation not found, incomplete strategy

% (3908)Memory used [KB]: 11129
% (3908)Time elapsed: 0.117 s
% (3908)------------------------------
% (3908)------------------------------
fof(f954,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f138,f302,f310,f324,f444,f508,f521,f657,f674,f782,f873,f953])).

fof(f953,plain,
    ( ~ spl10_1
    | spl10_3
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_24
    | ~ spl10_36 ),
    inference(avatar_contradiction_clause,[],[f952])).

fof(f952,plain,
    ( $false
    | ~ spl10_1
    | spl10_3
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_24
    | ~ spl10_36 ),
    inference(subsumption_resolution,[],[f951,f856])).

fof(f856,plain,
    ( sP0(sK8,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,sK7)
    | ~ spl10_1
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_24
    | ~ spl10_36 ),
    inference(resolution,[],[f852,f120])).

fof(f120,plain,(
    ! [X6,X2,X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3,k1_tmap_1(X1,X3,X2,X5,X0,X6),X5,X6)
      | sP0(X6,X5,k1_tmap_1(X1,X3,X2,X5,X0,X6),X3,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( sP0(X6,X5,X4,X3,X2,X1,X0)
      | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( ( k1_tmap_1(X1,X3,X2,X5,X0,X6) = X4
          | ~ sP0(X6,X5,X4,X3,X2,X1,X0) )
        & ( sP0(X6,X5,X4,X3,X2,X1,X0)
          | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4 ) )
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X4,X0,X2,X1,X6,X3,X5] :
      ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
          | ~ sP0(X5,X3,X6,X1,X2,X0,X4) )
        & ( sP0(X5,X3,X6,X1,X2,X0,X4)
          | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
      | ~ sP1(X4,X0,X2,X1,X6,X3,X5) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X4,X0,X2,X1,X6,X3,X5] :
      ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
      <=> sP0(X5,X3,X6,X1,X2,X0,X4) )
      | ~ sP1(X4,X0,X2,X1,X6,X3,X5) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f852,plain,
    ( sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8)
    | ~ spl10_1
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_24
    | ~ spl10_36 ),
    inference(subsumption_resolution,[],[f851,f329])).

fof(f329,plain,
    ( v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))
    | ~ spl10_18 ),
    inference(avatar_component_clause,[],[f328])).

fof(f328,plain,
    ( spl10_18
  <=> v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).

fof(f851,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))
    | sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8)
    | ~ spl10_1
    | ~ spl10_19
    | ~ spl10_24
    | ~ spl10_36 ),
    inference(subsumption_resolution,[],[f848,f732])).

fof(f732,plain,
    ( v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)
    | ~ spl10_36 ),
    inference(avatar_component_clause,[],[f731])).

fof(f731,plain,
    ( spl10_36
  <=> v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).

fof(f848,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)
    | ~ v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))
    | sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8)
    | ~ spl10_1
    | ~ spl10_19
    | ~ spl10_24 ),
    inference(resolution,[],[f847,f333])).

fof(f333,plain,
    ( m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
    | ~ spl10_19 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl10_19
  <=> m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).

fof(f847,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X0)
        | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) )
    | ~ spl10_1
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f846,f77])).

fof(f77,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f22,f52,f51,f50,f49,f48,f47])).

fof(f47,plain,
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

fof(f48,plain,
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

fof(f49,plain,
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

fof(f50,plain,
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

fof(f51,plain,
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

fof(f52,plain,
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

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f846,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X0)
        | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)
        | ~ v1_funct_1(sK7) )
    | ~ spl10_1
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f845,f78])).

fof(f78,plain,(
    v1_funct_2(sK7,sK5,sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f845,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X0)
        | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)
        | ~ v1_funct_2(sK7,sK5,sK4)
        | ~ v1_funct_1(sK7) )
    | ~ spl10_1
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f843,f79])).

fof(f79,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f843,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
        | ~ v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4)
        | ~ v1_funct_1(X0)
        | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)
        | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
        | ~ v1_funct_2(sK7,sK5,sK4)
        | ~ v1_funct_1(sK7) )
    | ~ spl10_1
    | ~ spl10_24 ),
    inference(trivial_inequality_removal,[],[f840])).

fof(f840,plain,
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
    | ~ spl10_24 ),
    inference(superposition,[],[f767,f544])).

fof(f544,plain,
    ( k1_xboole_0 = k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1
    | ~ spl10_24 ),
    inference(forward_demodulation,[],[f357,f526])).

fof(f526,plain,
    ( k1_xboole_0 = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1
    | ~ spl10_24 ),
    inference(backward_demodulation,[],[f487,f505])).

fof(f505,plain,
    ( k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_24 ),
    inference(avatar_component_clause,[],[f503])).

fof(f503,plain,
    ( spl10_24
  <=> k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).

fof(f487,plain,
    ( k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f486,f77])).

fof(f486,plain,
    ( k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ v1_funct_1(sK7)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f482,f79])).

fof(f482,plain,
    ( k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(sK7)
    | ~ spl10_1 ),
    inference(superposition,[],[f355,f115])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f355,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f354,f80])).

fof(f80,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f53])).

fof(f354,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ v1_funct_1(sK8)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f351,f82])).

fof(f82,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) ),
    inference(cnf_transformation,[],[f53])).

fof(f351,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | ~ spl10_1 ),
    inference(superposition,[],[f128,f115])).

fof(f128,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl10_1
  <=> k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f357,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f356,f80])).

fof(f356,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ v1_funct_1(sK8)
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f352,f82])).

fof(f352,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | ~ spl10_1 ),
    inference(superposition,[],[f115,f128])).

fof(f767,plain,
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
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f766,f71])).

fof(f71,plain,(
    ~ v1_xboole_0(sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f766,plain,
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
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f765,f72])).

fof(f72,plain,(
    ~ v1_xboole_0(sK5) ),
    inference(cnf_transformation,[],[f53])).

fof(f765,plain,
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
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f764,f73])).

fof(f73,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f764,plain,
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
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f763,f74])).

fof(f74,plain,(
    ~ v1_xboole_0(sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f763,plain,
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
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f762,f75])).

fof(f75,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(sK3)) ),
    inference(cnf_transformation,[],[f53])).

fof(f762,plain,
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
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f761,f80])).

fof(f761,plain,
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
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f760,f81])).

fof(f81,plain,(
    v1_funct_2(sK8,sK6,sK4) ),
    inference(cnf_transformation,[],[f53])).

fof(f760,plain,
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
    | ~ spl10_24 ),
    inference(subsumption_resolution,[],[f754,f82])).

fof(f754,plain,
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
    | ~ spl10_24 ),
    inference(superposition,[],[f715,f540])).

fof(f540,plain,
    ( k1_xboole_0 = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1
    | ~ spl10_24 ),
    inference(forward_demodulation,[],[f525,f505])).

fof(f525,plain,
    ( k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(forward_demodulation,[],[f480,f487])).

fof(f480,plain,
    ( k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(backward_demodulation,[],[f128,f355])).

fof(f715,plain,(
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
    inference(subsumption_resolution,[],[f90,f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f90,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(definition_folding,[],[f24,f43,f42])).

fof(f42,plain,(
    ! [X5,X3,X6,X1,X2,X0,X4] :
      ( sP0(X5,X3,X6,X1,X2,X0,X4)
    <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
        & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f951,plain,
    ( ~ sP0(sK8,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,sK7)
    | ~ spl10_1
    | spl10_3
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_24
    | ~ spl10_36 ),
    inference(resolution,[],[f925,f852])).

fof(f925,plain,
    ( ! [X0] :
        ( ~ sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)
        | ~ sP0(sK8,sK6,X0,sK4,sK5,sK3,sK7) )
    | spl10_3 ),
    inference(subsumption_resolution,[],[f922,f88])).

fof(f88,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3,X4,X5,X6] :
      ( ( sP0(X0,X1,X2,X3,X4,X5,X6)
        | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) != X0
        | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) != X6 )
      & ( ( k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0
          & k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6 )
        | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X5,X3,X6,X1,X2,X0,X4] :
      ( ( sP0(X5,X3,X6,X1,X2,X0,X4)
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
      & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
          & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
        | ~ sP0(X5,X3,X6,X1,X2,X0,X4) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X5,X3,X6,X1,X2,X0,X4] :
      ( ( sP0(X5,X3,X6,X1,X2,X0,X4)
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
        | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
      & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
          & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
        | ~ sP0(X5,X3,X6,X1,X2,X0,X4) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f922,plain,
    ( ! [X0] :
        ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,X0,sK6)
        | ~ sP0(sK8,sK6,X0,sK4,sK5,sK3,sK7)
        | ~ sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) )
    | spl10_3 ),
    inference(superposition,[],[f137,f86])).

fof(f86,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k1_tmap_1(X1,X3,X2,X5,X0,X6) = X4
      | ~ sP0(X6,X5,X4,X3,X2,X1,X0)
      | ~ sP1(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f137,plain,
    ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)
    | spl10_3 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl10_3
  <=> sK8 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f873,plain,
    ( ~ spl10_1
    | spl10_2
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_24
    | ~ spl10_36 ),
    inference(avatar_contradiction_clause,[],[f872])).

fof(f872,plain,
    ( $false
    | ~ spl10_1
    | spl10_2
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_24
    | ~ spl10_36 ),
    inference(trivial_inequality_removal,[],[f868])).

fof(f868,plain,
    ( sK7 != sK7
    | ~ spl10_1
    | spl10_2
    | ~ spl10_18
    | ~ spl10_19
    | ~ spl10_24
    | ~ spl10_36 ),
    inference(resolution,[],[f856,f390])).

fof(f390,plain,
    ( ! [X0,X1] :
        ( ~ sP0(X1,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,X0)
        | sK7 != X0 )
    | spl10_2 ),
    inference(superposition,[],[f133,f87])).

fof(f87,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6
      | ~ sP0(X0,X1,X2,X3,X4,X5,X6) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f133,plain,
    ( sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)
    | spl10_2 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl10_2
  <=> sK7 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f782,plain,(
    spl10_36 ),
    inference(avatar_contradiction_clause,[],[f781])).

fof(f781,plain,
    ( $false
    | spl10_36 ),
    inference(subsumption_resolution,[],[f780,f71])).

fof(f780,plain,
    ( v1_xboole_0(sK4)
    | spl10_36 ),
    inference(subsumption_resolution,[],[f779,f72])).

fof(f779,plain,
    ( v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_36 ),
    inference(subsumption_resolution,[],[f778,f73])).

fof(f778,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_36 ),
    inference(subsumption_resolution,[],[f777,f74])).

fof(f777,plain,
    ( v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_36 ),
    inference(subsumption_resolution,[],[f776,f75])).

fof(f776,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_36 ),
    inference(subsumption_resolution,[],[f775,f77])).

fof(f775,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_36 ),
    inference(subsumption_resolution,[],[f774,f78])).

fof(f774,plain,
    ( ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_36 ),
    inference(subsumption_resolution,[],[f773,f79])).

fof(f773,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_36 ),
    inference(subsumption_resolution,[],[f772,f80])).

fof(f772,plain,
    ( ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_36 ),
    inference(subsumption_resolution,[],[f771,f81])).

fof(f771,plain,
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
    | spl10_36 ),
    inference(subsumption_resolution,[],[f770,f82])).

fof(f770,plain,
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
    | spl10_36 ),
    inference(resolution,[],[f768,f638])).

fof(f638,plain,(
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
    inference(subsumption_resolution,[],[f119,f91])).

fof(f119,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(definition_folding,[],[f41,f45])).

fof(f45,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP2(X1,X3,X2,X0,X5,X4) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f768,plain,
    ( ~ sP2(sK4,sK6,sK5,sK3,sK8,sK7)
    | spl10_36 ),
    inference(resolution,[],[f733,f117])).

fof(f117,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0)
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0)))
        & v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0)
        & v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4)) )
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(rectify,[],[f68])).

fof(f68,plain,(
    ! [X1,X3,X2,X0,X5,X4] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ sP2(X1,X3,X2,X0,X5,X4) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f733,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)
    | spl10_36 ),
    inference(avatar_component_clause,[],[f731])).

fof(f674,plain,(
    spl10_19 ),
    inference(avatar_contradiction_clause,[],[f673])).

fof(f673,plain,
    ( $false
    | spl10_19 ),
    inference(subsumption_resolution,[],[f672,f71])).

fof(f672,plain,
    ( v1_xboole_0(sK4)
    | spl10_19 ),
    inference(subsumption_resolution,[],[f671,f72])).

fof(f671,plain,
    ( v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_19 ),
    inference(subsumption_resolution,[],[f670,f73])).

fof(f670,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_19 ),
    inference(subsumption_resolution,[],[f669,f74])).

fof(f669,plain,
    ( v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_19 ),
    inference(subsumption_resolution,[],[f668,f75])).

fof(f668,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_19 ),
    inference(subsumption_resolution,[],[f667,f77])).

fof(f667,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_19 ),
    inference(subsumption_resolution,[],[f666,f78])).

fof(f666,plain,
    ( ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_19 ),
    inference(subsumption_resolution,[],[f665,f79])).

fof(f665,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_19 ),
    inference(subsumption_resolution,[],[f664,f80])).

fof(f664,plain,
    ( ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_19 ),
    inference(subsumption_resolution,[],[f663,f81])).

fof(f663,plain,
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
    | spl10_19 ),
    inference(subsumption_resolution,[],[f662,f82])).

fof(f662,plain,
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
    | spl10_19 ),
    inference(resolution,[],[f659,f638])).

fof(f659,plain,
    ( ~ sP2(sK4,sK6,sK5,sK3,sK8,sK7)
    | spl10_19 ),
    inference(resolution,[],[f334,f118])).

fof(f118,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0)))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f334,plain,
    ( ~ m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))
    | spl10_19 ),
    inference(avatar_component_clause,[],[f332])).

fof(f657,plain,(
    spl10_18 ),
    inference(avatar_contradiction_clause,[],[f656])).

fof(f656,plain,
    ( $false
    | spl10_18 ),
    inference(subsumption_resolution,[],[f655,f71])).

fof(f655,plain,
    ( v1_xboole_0(sK4)
    | spl10_18 ),
    inference(subsumption_resolution,[],[f654,f72])).

fof(f654,plain,
    ( v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_18 ),
    inference(subsumption_resolution,[],[f653,f73])).

fof(f653,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_18 ),
    inference(subsumption_resolution,[],[f652,f74])).

fof(f652,plain,
    ( v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_18 ),
    inference(subsumption_resolution,[],[f651,f75])).

fof(f651,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_18 ),
    inference(subsumption_resolution,[],[f650,f77])).

fof(f650,plain,
    ( ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_18 ),
    inference(subsumption_resolution,[],[f649,f78])).

fof(f649,plain,
    ( ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_18 ),
    inference(subsumption_resolution,[],[f648,f79])).

fof(f648,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_18 ),
    inference(subsumption_resolution,[],[f647,f80])).

fof(f647,plain,
    ( ~ v1_funct_1(sK8)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_2(sK7,sK5,sK4)
    | ~ v1_funct_1(sK7)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(sK3))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | spl10_18 ),
    inference(subsumption_resolution,[],[f646,f81])).

fof(f646,plain,
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
    | spl10_18 ),
    inference(subsumption_resolution,[],[f645,f82])).

fof(f645,plain,
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
    | spl10_18 ),
    inference(resolution,[],[f638,f345])).

fof(f345,plain,
    ( ~ sP2(sK4,sK6,sK5,sK3,sK8,sK7)
    | spl10_18 ),
    inference(resolution,[],[f330,f116])).

fof(f116,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4))
      | ~ sP2(X0,X1,X2,X3,X4,X5) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f330,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))
    | spl10_18 ),
    inference(avatar_component_clause,[],[f328])).

fof(f521,plain,
    ( ~ spl10_21
    | spl10_23 ),
    inference(avatar_contradiction_clause,[],[f520])).

fof(f520,plain,
    ( $false
    | ~ spl10_21
    | spl10_23 ),
    inference(subsumption_resolution,[],[f519,f75])).

fof(f519,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | ~ spl10_21
    | spl10_23 ),
    inference(subsumption_resolution,[],[f517,f423])).

fof(f423,plain,
    ( r1_xboole_0(k1_relat_1(sK8),k3_xboole_0(sK5,sK6))
    | ~ spl10_21 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl10_21
  <=> r1_xboole_0(k1_relat_1(sK8),k3_xboole_0(sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).

fof(f517,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK8),k3_xboole_0(sK5,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | spl10_23 ),
    inference(superposition,[],[f501,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f501,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK8),k9_subset_1(sK3,sK5,sK6))
    | spl10_23 ),
    inference(avatar_component_clause,[],[f499])).

fof(f499,plain,
    ( spl10_23
  <=> r1_xboole_0(k1_relat_1(sK8),k9_subset_1(sK3,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f508,plain,
    ( ~ spl10_23
    | spl10_24
    | ~ spl10_1 ),
    inference(avatar_split_clause,[],[f507,f127,f503,f499])).

fof(f507,plain,
    ( k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ r1_xboole_0(k1_relat_1(sK8),k9_subset_1(sK3,sK5,sK6))
    | ~ spl10_1 ),
    inference(subsumption_resolution,[],[f493,f174])).

fof(f174,plain,(
    v1_relat_1(sK8) ),
    inference(resolution,[],[f111,f82])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f493,plain,
    ( k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))
    | ~ r1_xboole_0(k1_relat_1(sK8),k9_subset_1(sK3,sK5,sK6))
    | ~ v1_relat_1(sK8)
    | ~ spl10_1 ),
    inference(superposition,[],[f98,f487])).

% (3907)Termination reason: Refutation not found, incomplete strategy

% (3907)Memory used [KB]: 6908
% (3907)Time elapsed: 0.138 s
% (3907)------------------------------
% (3907)------------------------------
fof(f98,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

fof(f444,plain,
    ( ~ spl10_16
    | spl10_21 ),
    inference(avatar_contradiction_clause,[],[f443])).

fof(f443,plain,
    ( $false
    | ~ spl10_16
    | spl10_21 ),
    inference(subsumption_resolution,[],[f442,f248])).

fof(f248,plain,(
    r1_xboole_0(sK5,sK6) ),
    inference(resolution,[],[f247,f76])).

fof(f76,plain,(
    r1_subset_1(sK5,sK6) ),
    inference(cnf_transformation,[],[f53])).

fof(f247,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(subsumption_resolution,[],[f246,f244])).

fof(f244,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ v1_xboole_0(X0) ) ),
    inference(resolution,[],[f239,f92])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK9(X0,X1),X1)
          & r2_hidden(sK9(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f26,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK9(X0,X1),X1)
        & r2_hidden(sK9(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f239,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v1_xboole_0(X1) ) ),
    inference(resolution,[],[f235,f124])).

fof(f124,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f235,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X6,X4)
      | ~ r2_hidden(X5,X6)
      | ~ v1_xboole_0(X4) ) ),
    inference(resolution,[],[f114,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
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

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f246,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f99,f245])).

fof(f245,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | ~ v1_xboole_0(X2) ) ),
    inference(resolution,[],[f239,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK9(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | ~ r1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f442,plain,
    ( ~ r1_xboole_0(sK5,sK6)
    | ~ spl10_16
    | spl10_21 ),
    inference(subsumption_resolution,[],[f440,f296])).

fof(f296,plain,
    ( r1_xboole_0(k1_relat_1(sK8),k1_xboole_0)
    | ~ spl10_16 ),
    inference(avatar_component_clause,[],[f295])).

fof(f295,plain,
    ( spl10_16
  <=> r1_xboole_0(k1_relat_1(sK8),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).

fof(f440,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK8),k1_xboole_0)
    | ~ r1_xboole_0(sK5,sK6)
    | spl10_21 ),
    inference(superposition,[],[f424,f106])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
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

fof(f424,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK8),k3_xboole_0(sK5,sK6))
    | spl10_21 ),
    inference(avatar_component_clause,[],[f422])).

fof(f324,plain,(
    spl10_17 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | spl10_17 ),
    inference(subsumption_resolution,[],[f320,f84])).

fof(f84,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f320,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl10_17 ),
    inference(resolution,[],[f316,f245])).

fof(f316,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK7),k1_xboole_0)
    | spl10_17 ),
    inference(subsumption_resolution,[],[f315,f173])).

fof(f173,plain,(
    v1_relat_1(sK7) ),
    inference(resolution,[],[f111,f79])).

fof(f315,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK7),k1_xboole_0)
    | ~ v1_relat_1(sK7)
    | spl10_17 ),
    inference(trivial_inequality_removal,[],[f314])).

fof(f314,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_relat_1(sK7),k1_xboole_0)
    | ~ v1_relat_1(sK7)
    | spl10_17 ),
    inference(superposition,[],[f301,f98])).

fof(f301,plain,
    ( k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0)
    | spl10_17 ),
    inference(avatar_component_clause,[],[f299])).

fof(f299,plain,
    ( spl10_17
  <=> k1_xboole_0 = k7_relat_1(sK7,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).

fof(f310,plain,(
    spl10_16 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | spl10_16 ),
    inference(subsumption_resolution,[],[f306,f84])).

fof(f306,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl10_16 ),
    inference(resolution,[],[f297,f245])).

fof(f297,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK8),k1_xboole_0)
    | spl10_16 ),
    inference(avatar_component_clause,[],[f295])).

fof(f302,plain,
    ( ~ spl10_16
    | ~ spl10_17
    | spl10_1 ),
    inference(avatar_split_clause,[],[f293,f127,f299,f295])).

fof(f293,plain,
    ( k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0)
    | ~ r1_xboole_0(k1_relat_1(sK8),k1_xboole_0)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f292,f174])).

fof(f292,plain,
    ( k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0)
    | ~ r1_xboole_0(k1_relat_1(sK8),k1_xboole_0)
    | ~ v1_relat_1(sK8)
    | spl10_1 ),
    inference(superposition,[],[f291,f98])).

fof(f291,plain,
    ( k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f290,f77])).

fof(f290,plain,
    ( k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | ~ v1_funct_1(sK7)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f289,f79])).

fof(f289,plain,
    ( k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))
    | ~ v1_funct_1(sK7)
    | spl10_1 ),
    inference(superposition,[],[f288,f115])).

fof(f288,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f287,f80])).

fof(f287,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0)
    | ~ v1_funct_1(sK8)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f282,f82])).

fof(f282,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))
    | ~ v1_funct_1(sK8)
    | spl10_1 ),
    inference(superposition,[],[f267,f115])).

fof(f267,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0)
    | spl10_1 ),
    inference(subsumption_resolution,[],[f266,f248])).

fof(f266,plain,
    ( k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0)
    | ~ r1_xboole_0(sK5,sK6)
    | spl10_1 ),
    inference(superposition,[],[f265,f106])).

fof(f265,plain,
    ( k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6))
    | spl10_1 ),
    inference(subsumption_resolution,[],[f264,f75])).

fof(f264,plain,
    ( k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(sK3))
    | spl10_1 ),
    inference(superposition,[],[f129,f110])).

fof(f129,plain,
    ( k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))
    | spl10_1 ),
    inference(avatar_component_clause,[],[f127])).

fof(f138,plain,
    ( ~ spl10_1
    | ~ spl10_2
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f83,f135,f131,f127])).

fof(f83,plain,
    ( sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)
    | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)
    | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:06:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (3906)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.51  % (3923)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.52  % (3922)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.52  % (3907)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.52  % (3908)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.52  % (3913)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (3915)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (3914)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.53  % (3927)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.53  % (3905)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.53  % (3925)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.53  % (3910)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.53  % (3917)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (3916)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.53  % (3924)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (3926)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.54  % (3911)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.55  % (3920)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.55  % (3904)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.55  % (3909)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.55  % (3902)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.55  % (3918)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.55  % (3903)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (3906)Refutation found. Thanks to Tanya!
% 0.22/0.55  % SZS status Theorem for theBenchmark
% 0.22/0.55  % (3908)Refutation not found, incomplete strategy% (3908)------------------------------
% 0.22/0.55  % (3908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (3919)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.56  % (3921)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.56  % (3912)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.57  % (3907)Refutation not found, incomplete strategy% (3907)------------------------------
% 0.22/0.57  % (3907)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  % (3908)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (3908)Memory used [KB]: 11129
% 0.22/0.57  % (3908)Time elapsed: 0.117 s
% 0.22/0.57  % (3908)------------------------------
% 0.22/0.57  % (3908)------------------------------
% 0.22/0.57  fof(f954,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f138,f302,f310,f324,f444,f508,f521,f657,f674,f782,f873,f953])).
% 0.22/0.57  fof(f953,plain,(
% 0.22/0.57    ~spl10_1 | spl10_3 | ~spl10_18 | ~spl10_19 | ~spl10_24 | ~spl10_36),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f952])).
% 0.22/0.57  fof(f952,plain,(
% 0.22/0.57    $false | (~spl10_1 | spl10_3 | ~spl10_18 | ~spl10_19 | ~spl10_24 | ~spl10_36)),
% 0.22/0.57    inference(subsumption_resolution,[],[f951,f856])).
% 0.22/0.57  fof(f856,plain,(
% 0.22/0.57    sP0(sK8,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,sK7) | (~spl10_1 | ~spl10_18 | ~spl10_19 | ~spl10_24 | ~spl10_36)),
% 0.22/0.57    inference(resolution,[],[f852,f120])).
% 0.22/0.57  fof(f120,plain,(
% 0.22/0.57    ( ! [X6,X2,X0,X5,X3,X1] : (~sP1(X0,X1,X2,X3,k1_tmap_1(X1,X3,X2,X5,X0,X6),X5,X6) | sP0(X6,X5,k1_tmap_1(X1,X3,X2,X5,X0,X6),X3,X2,X1,X0)) )),
% 0.22/0.57    inference(equality_resolution,[],[f85])).
% 0.22/0.57  fof(f85,plain,(
% 0.22/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP0(X6,X5,X4,X3,X2,X1,X0) | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4 | ~sP1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f55])).
% 0.22/0.57  fof(f55,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : (((k1_tmap_1(X1,X3,X2,X5,X0,X6) = X4 | ~sP0(X6,X5,X4,X3,X2,X1,X0)) & (sP0(X6,X5,X4,X3,X2,X1,X0) | k1_tmap_1(X1,X3,X2,X5,X0,X6) != X4)) | ~sP1(X0,X1,X2,X3,X4,X5,X6))),
% 0.22/0.57    inference(rectify,[],[f54])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    ! [X4,X0,X2,X1,X6,X3,X5] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | ~sP0(X5,X3,X6,X1,X2,X0,X4)) & (sP0(X5,X3,X6,X1,X2,X0,X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~sP1(X4,X0,X2,X1,X6,X3,X5))),
% 0.22/0.57    inference(nnf_transformation,[],[f43])).
% 0.22/0.57  fof(f43,plain,(
% 0.22/0.57    ! [X4,X0,X2,X1,X6,X3,X5] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> sP0(X5,X3,X6,X1,X2,X0,X4)) | ~sP1(X4,X0,X2,X1,X6,X3,X5))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.57  fof(f852,plain,(
% 0.22/0.57    sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8) | (~spl10_1 | ~spl10_18 | ~spl10_19 | ~spl10_24 | ~spl10_36)),
% 0.22/0.57    inference(subsumption_resolution,[],[f851,f329])).
% 0.22/0.57  fof(f329,plain,(
% 0.22/0.57    v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) | ~spl10_18),
% 0.22/0.57    inference(avatar_component_clause,[],[f328])).
% 0.22/0.57  fof(f328,plain,(
% 0.22/0.57    spl10_18 <=> v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_18])])).
% 0.22/0.57  fof(f851,plain,(
% 0.22/0.57    ~v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) | sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8) | (~spl10_1 | ~spl10_19 | ~spl10_24 | ~spl10_36)),
% 0.22/0.57    inference(subsumption_resolution,[],[f848,f732])).
% 0.22/0.57  fof(f732,plain,(
% 0.22/0.57    v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) | ~spl10_36),
% 0.22/0.57    inference(avatar_component_clause,[],[f731])).
% 0.22/0.57  fof(f731,plain,(
% 0.22/0.57    spl10_36 <=> v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_36])])).
% 0.22/0.57  fof(f848,plain,(
% 0.22/0.57    ~v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) | sP1(sK7,sK3,sK5,sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6,sK8) | (~spl10_1 | ~spl10_19 | ~spl10_24)),
% 0.22/0.57    inference(resolution,[],[f847,f333])).
% 0.22/0.57  fof(f333,plain,(
% 0.22/0.57    m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~spl10_19),
% 0.22/0.57    inference(avatar_component_clause,[],[f332])).
% 0.22/0.57  fof(f332,plain,(
% 0.22/0.57    spl10_19 <=> m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_19])])).
% 0.22/0.57  fof(f847,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)) ) | (~spl10_1 | ~spl10_24)),
% 0.22/0.57    inference(subsumption_resolution,[],[f846,f77])).
% 0.22/0.57  fof(f77,plain,(
% 0.22/0.57    v1_funct_1(sK7)),
% 0.22/0.57    inference(cnf_transformation,[],[f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    ((((((sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(sK8,sK6,sK4) & v1_funct_1(sK8)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(sK7,sK5,sK4) & v1_funct_1(sK7)) & r1_subset_1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK5)) & ~v1_xboole_0(sK4)) & ~v1_xboole_0(sK3)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7,sK8])],[f22,f52,f51,f50,f49,f48,f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK3))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),X1,k1_tmap_1(sK3,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK4,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK4))) & v1_funct_2(X4,X2,sK4) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK4))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,X2,X3),sK4,k1_tmap_1(sK3,sK4,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK4,X4,k9_subset_1(sK3,X2,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK4))) & v1_funct_2(X4,X2,sK4) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,sK5,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) & r1_subset_1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) & m1_subset_1(sK5,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK5))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    ? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,X3),sK4,k1_tmap_1(sK3,sK4,sK5,X3,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,X3)) != k2_partfun1(X3,sK4,X5,k9_subset_1(sK3,sK5,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK4))) & v1_funct_2(X5,X3,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) & r1_subset_1(sK5,X3) & m1_subset_1(X3,k1_zfmisc_1(sK3)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK6) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) & r1_subset_1(sK5,sK6) & m1_subset_1(sK6,k1_zfmisc_1(sK3)) & ~v1_xboole_0(sK6))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    ? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK6) != X5 | k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,X4,X5),sK5) != X4 | k2_partfun1(sK5,sK4,X4,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(X4,sK5,sK4) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK6) != X5 | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK5) | k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) & v1_funct_2(sK7,sK5,sK4) & v1_funct_1(sK7))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    ? [X5] : ((k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK6) != X5 | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,X5),sK5) | k2_partfun1(sK6,sK4,X5,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(X5,sK6,sK4) & v1_funct_1(X5)) => ((sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) & v1_funct_2(sK8,sK6,sK4) & v1_funct_1(sK8))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.57    inference(flattening,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.22/0.57    inference(ennf_transformation,[],[f19])).
% 0.22/0.57  fof(f19,negated_conjecture,(
% 0.22/0.57    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.22/0.57    inference(negated_conjecture,[],[f18])).
% 0.22/0.57  fof(f18,conjecture,(
% 0.22/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 0.22/0.57  fof(f846,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~v1_funct_1(sK7)) ) | (~spl10_1 | ~spl10_24)),
% 0.22/0.57    inference(subsumption_resolution,[],[f845,f78])).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    v1_funct_2(sK7,sK5,sK4)),
% 0.22/0.57    inference(cnf_transformation,[],[f53])).
% 0.22/0.57  fof(f845,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7)) ) | (~spl10_1 | ~spl10_24)),
% 0.22/0.57    inference(subsumption_resolution,[],[f843,f79])).
% 0.22/0.57  fof(f79,plain,(
% 0.22/0.57    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4)))),
% 0.22/0.57    inference(cnf_transformation,[],[f53])).
% 0.22/0.57  fof(f843,plain,(
% 0.22/0.57    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7)) ) | (~spl10_1 | ~spl10_24)),
% 0.22/0.57    inference(trivial_inequality_removal,[],[f840])).
% 0.22/0.57  fof(f840,plain,(
% 0.22/0.57    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X0,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X0) | sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7)) ) | (~spl10_1 | ~spl10_24)),
% 0.22/0.57    inference(superposition,[],[f767,f544])).
% 0.22/0.57  fof(f544,plain,(
% 0.22/0.57    k1_xboole_0 = k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) | (~spl10_1 | ~spl10_24)),
% 0.22/0.57    inference(forward_demodulation,[],[f357,f526])).
% 0.22/0.57  fof(f526,plain,(
% 0.22/0.57    k1_xboole_0 = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | (~spl10_1 | ~spl10_24)),
% 0.22/0.57    inference(backward_demodulation,[],[f487,f505])).
% 0.22/0.57  fof(f505,plain,(
% 0.22/0.57    k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~spl10_24),
% 0.22/0.57    inference(avatar_component_clause,[],[f503])).
% 0.22/0.57  fof(f503,plain,(
% 0.22/0.57    spl10_24 <=> k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_24])])).
% 0.22/0.57  fof(f487,plain,(
% 0.22/0.57    k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 0.22/0.57    inference(subsumption_resolution,[],[f486,f77])).
% 0.22/0.57  fof(f486,plain,(
% 0.22/0.57    k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~v1_funct_1(sK7) | ~spl10_1),
% 0.22/0.57    inference(subsumption_resolution,[],[f482,f79])).
% 0.22/0.57  fof(f482,plain,(
% 0.22/0.57    k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_1(sK7) | ~spl10_1),
% 0.22/0.57    inference(superposition,[],[f355,f115])).
% 0.22/0.57  fof(f115,plain,(
% 0.22/0.57    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f39])).
% 0.22/0.57  fof(f39,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.22/0.57    inference(flattening,[],[f38])).
% 0.22/0.57  fof(f38,plain,(
% 0.22/0.57    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.22/0.57    inference(ennf_transformation,[],[f15])).
% 0.22/0.57  fof(f15,axiom,(
% 0.22/0.57    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.22/0.57  fof(f355,plain,(
% 0.22/0.57    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 0.22/0.57    inference(subsumption_resolution,[],[f354,f80])).
% 1.42/0.57  fof(f80,plain,(
% 1.42/0.57    v1_funct_1(sK8)),
% 1.42/0.57    inference(cnf_transformation,[],[f53])).
% 1.42/0.57  fof(f354,plain,(
% 1.42/0.57    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~v1_funct_1(sK8) | ~spl10_1),
% 1.42/0.57    inference(subsumption_resolution,[],[f351,f82])).
% 1.42/0.57  fof(f82,plain,(
% 1.42/0.57    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4)))),
% 1.42/0.57    inference(cnf_transformation,[],[f53])).
% 1.42/0.57  fof(f351,plain,(
% 1.42/0.57    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_1(sK8) | ~spl10_1),
% 1.42/0.57    inference(superposition,[],[f128,f115])).
% 1.42/0.57  fof(f128,plain,(
% 1.42/0.57    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.42/0.57    inference(avatar_component_clause,[],[f127])).
% 1.42/0.57  fof(f127,plain,(
% 1.42/0.57    spl10_1 <=> k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).
% 1.42/0.57  fof(f357,plain,(
% 1.42/0.57    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.42/0.57    inference(subsumption_resolution,[],[f356,f80])).
% 1.42/0.57  fof(f356,plain,(
% 1.42/0.57    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~v1_funct_1(sK8) | ~spl10_1),
% 1.42/0.57    inference(subsumption_resolution,[],[f352,f82])).
% 1.42/0.57  fof(f352,plain,(
% 1.42/0.57    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_1(sK8) | ~spl10_1),
% 1.42/0.57    inference(superposition,[],[f115,f128])).
% 1.42/0.57  fof(f767,plain,(
% 1.42/0.57    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7)) ) | (~spl10_1 | ~spl10_24)),
% 1.42/0.57    inference(subsumption_resolution,[],[f766,f71])).
% 1.42/0.57  fof(f71,plain,(
% 1.42/0.57    ~v1_xboole_0(sK4)),
% 1.42/0.57    inference(cnf_transformation,[],[f53])).
% 1.42/0.57  fof(f766,plain,(
% 1.42/0.57    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_24)),
% 1.42/0.57    inference(subsumption_resolution,[],[f765,f72])).
% 1.42/0.57  fof(f72,plain,(
% 1.42/0.57    ~v1_xboole_0(sK5)),
% 1.42/0.57    inference(cnf_transformation,[],[f53])).
% 1.42/0.57  fof(f765,plain,(
% 1.42/0.57    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | v1_xboole_0(sK5) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_24)),
% 1.42/0.57    inference(subsumption_resolution,[],[f764,f73])).
% 1.42/0.57  fof(f73,plain,(
% 1.42/0.57    m1_subset_1(sK5,k1_zfmisc_1(sK3))),
% 1.42/0.57    inference(cnf_transformation,[],[f53])).
% 1.42/0.57  fof(f764,plain,(
% 1.42/0.57    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_24)),
% 1.42/0.57    inference(subsumption_resolution,[],[f763,f74])).
% 1.42/0.57  fof(f74,plain,(
% 1.42/0.57    ~v1_xboole_0(sK6)),
% 1.42/0.57    inference(cnf_transformation,[],[f53])).
% 1.42/0.57  fof(f763,plain,(
% 1.42/0.57    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_24)),
% 1.42/0.57    inference(subsumption_resolution,[],[f762,f75])).
% 1.42/0.57  fof(f75,plain,(
% 1.42/0.57    m1_subset_1(sK6,k1_zfmisc_1(sK3))),
% 1.42/0.57    inference(cnf_transformation,[],[f53])).
% 1.42/0.57  fof(f762,plain,(
% 1.42/0.57    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_24)),
% 1.42/0.57    inference(subsumption_resolution,[],[f761,f80])).
% 1.42/0.57  fof(f761,plain,(
% 1.42/0.57    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~v1_funct_1(sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_24)),
% 1.42/0.57    inference(subsumption_resolution,[],[f760,f81])).
% 1.42/0.57  fof(f81,plain,(
% 1.42/0.57    v1_funct_2(sK8,sK6,sK4)),
% 1.42/0.57    inference(cnf_transformation,[],[f53])).
% 1.42/0.57  fof(f760,plain,(
% 1.42/0.57    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_24)),
% 1.42/0.57    inference(subsumption_resolution,[],[f754,f82])).
% 1.42/0.57  fof(f754,plain,(
% 1.42/0.57    ( ! [X8,X7] : (k1_xboole_0 != k2_partfun1(sK5,sK4,X7,k9_subset_1(sK3,sK5,sK6)) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | ~v1_funct_2(X8,k4_subset_1(sK3,sK5,sK6),sK4) | ~v1_funct_1(X8) | sP1(X7,sK3,sK5,sK4,X8,sK6,sK8) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(X7,sK5,sK4) | ~v1_funct_1(X7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4)) ) | (~spl10_1 | ~spl10_24)),
% 1.42/0.57    inference(superposition,[],[f715,f540])).
% 1.42/0.57  fof(f540,plain,(
% 1.42/0.57    k1_xboole_0 = k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) | (~spl10_1 | ~spl10_24)),
% 1.42/0.57    inference(forward_demodulation,[],[f525,f505])).
% 1.42/0.57  fof(f525,plain,(
% 1.42/0.57    k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.42/0.57    inference(forward_demodulation,[],[f480,f487])).
% 1.42/0.57  fof(f480,plain,(
% 1.42/0.57    k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) = k7_relat_1(sK8,k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.42/0.57    inference(backward_demodulation,[],[f128,f355])).
% 1.42/0.57  fof(f715,plain,(
% 1.42/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | sP1(X4,X0,X2,X1,X6,X3,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1)) )),
% 1.42/0.57    inference(subsumption_resolution,[],[f90,f91])).
% 1.42/0.57  fof(f91,plain,(
% 1.42/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | ~v1_xboole_0(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f25])).
% 1.42/0.57  fof(f25,plain,(
% 1.42/0.57    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.42/0.57    inference(ennf_transformation,[],[f6])).
% 1.42/0.57  fof(f6,axiom,(
% 1.42/0.57    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.42/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.42/0.57  fof(f90,plain,(
% 1.42/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (sP1(X4,X0,X2,X1,X6,X3,X5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f44])).
% 1.42/0.57  fof(f44,plain,(
% 1.42/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (sP1(X4,X0,X2,X1,X6,X3,X5) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.42/0.57    inference(definition_folding,[],[f24,f43,f42])).
% 1.42/0.57  fof(f42,plain,(
% 1.42/0.57    ! [X5,X3,X6,X1,X2,X0,X4] : (sP0(X5,X3,X6,X1,X2,X0,X4) <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))),
% 1.42/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.42/0.57  fof(f24,plain,(
% 1.42/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.42/0.57    inference(flattening,[],[f23])).
% 1.42/0.57  fof(f23,plain,(
% 1.42/0.57    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.42/0.57    inference(ennf_transformation,[],[f16])).
% 1.42/0.57  fof(f16,axiom,(
% 1.42/0.57    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.42/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.42/0.57  fof(f951,plain,(
% 1.42/0.57    ~sP0(sK8,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,sK7) | (~spl10_1 | spl10_3 | ~spl10_18 | ~spl10_19 | ~spl10_24 | ~spl10_36)),
% 1.42/0.57    inference(resolution,[],[f925,f852])).
% 1.42/0.57  fof(f925,plain,(
% 1.42/0.57    ( ! [X0] : (~sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8) | ~sP0(sK8,sK6,X0,sK4,sK5,sK3,sK7)) ) | spl10_3),
% 1.42/0.57    inference(subsumption_resolution,[],[f922,f88])).
% 1.42/0.57  fof(f88,plain,(
% 1.42/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f58])).
% 1.42/0.57  fof(f58,plain,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : ((sP0(X0,X1,X2,X3,X4,X5,X6) | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) != X0 | k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) != X6) & ((k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X1) = X0 & k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6) | ~sP0(X0,X1,X2,X3,X4,X5,X6)))),
% 1.42/0.57    inference(rectify,[],[f57])).
% 1.42/0.57  fof(f57,plain,(
% 1.42/0.57    ! [X5,X3,X6,X1,X2,X0,X4] : ((sP0(X5,X3,X6,X1,X2,X0,X4) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | ~sP0(X5,X3,X6,X1,X2,X0,X4)))),
% 1.42/0.57    inference(flattening,[],[f56])).
% 1.42/0.57  fof(f56,plain,(
% 1.42/0.57    ! [X5,X3,X6,X1,X2,X0,X4] : ((sP0(X5,X3,X6,X1,X2,X0,X4) | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | ~sP0(X5,X3,X6,X1,X2,X0,X4)))),
% 1.42/0.57    inference(nnf_transformation,[],[f42])).
% 1.42/0.57  fof(f922,plain,(
% 1.42/0.57    ( ! [X0] : (sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,X0,sK6) | ~sP0(sK8,sK6,X0,sK4,sK5,sK3,sK7) | ~sP1(sK7,sK3,sK5,sK4,X0,sK6,sK8)) ) | spl10_3),
% 1.42/0.57    inference(superposition,[],[f137,f86])).
% 1.42/0.57  fof(f86,plain,(
% 1.42/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k1_tmap_1(X1,X3,X2,X5,X0,X6) = X4 | ~sP0(X6,X5,X4,X3,X2,X1,X0) | ~sP1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f55])).
% 1.42/0.57  fof(f137,plain,(
% 1.42/0.57    sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | spl10_3),
% 1.42/0.57    inference(avatar_component_clause,[],[f135])).
% 1.42/0.57  fof(f135,plain,(
% 1.42/0.57    spl10_3 <=> sK8 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).
% 1.42/0.57  fof(f873,plain,(
% 1.42/0.57    ~spl10_1 | spl10_2 | ~spl10_18 | ~spl10_19 | ~spl10_24 | ~spl10_36),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f872])).
% 1.42/0.57  fof(f872,plain,(
% 1.42/0.57    $false | (~spl10_1 | spl10_2 | ~spl10_18 | ~spl10_19 | ~spl10_24 | ~spl10_36)),
% 1.42/0.57    inference(trivial_inequality_removal,[],[f868])).
% 1.42/0.57  fof(f868,plain,(
% 1.42/0.57    sK7 != sK7 | (~spl10_1 | spl10_2 | ~spl10_18 | ~spl10_19 | ~spl10_24 | ~spl10_36)),
% 1.42/0.57    inference(resolution,[],[f856,f390])).
% 1.42/0.57  fof(f390,plain,(
% 1.42/0.57    ( ! [X0,X1] : (~sP0(X1,sK6,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK4,sK5,sK3,X0) | sK7 != X0) ) | spl10_2),
% 1.42/0.57    inference(superposition,[],[f133,f87])).
% 1.42/0.57  fof(f87,plain,(
% 1.42/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X5,X4,X1),X3,X2,X4) = X6 | ~sP0(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f58])).
% 1.42/0.57  fof(f133,plain,(
% 1.42/0.57    sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | spl10_2),
% 1.42/0.57    inference(avatar_component_clause,[],[f131])).
% 1.42/0.57  fof(f131,plain,(
% 1.42/0.57    spl10_2 <=> sK7 = k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5)),
% 1.42/0.57    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).
% 1.42/0.57  fof(f782,plain,(
% 1.42/0.57    spl10_36),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f781])).
% 1.42/0.57  fof(f781,plain,(
% 1.42/0.57    $false | spl10_36),
% 1.42/0.57    inference(subsumption_resolution,[],[f780,f71])).
% 1.42/0.57  fof(f780,plain,(
% 1.42/0.57    v1_xboole_0(sK4) | spl10_36),
% 1.42/0.57    inference(subsumption_resolution,[],[f779,f72])).
% 1.42/0.57  fof(f779,plain,(
% 1.42/0.57    v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_36),
% 1.42/0.57    inference(subsumption_resolution,[],[f778,f73])).
% 1.42/0.57  fof(f778,plain,(
% 1.42/0.57    ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_36),
% 1.42/0.57    inference(subsumption_resolution,[],[f777,f74])).
% 1.42/0.57  fof(f777,plain,(
% 1.42/0.57    v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_36),
% 1.42/0.57    inference(subsumption_resolution,[],[f776,f75])).
% 1.42/0.57  fof(f776,plain,(
% 1.42/0.57    ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_36),
% 1.42/0.57    inference(subsumption_resolution,[],[f775,f77])).
% 1.42/0.57  fof(f775,plain,(
% 1.42/0.57    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_36),
% 1.42/0.57    inference(subsumption_resolution,[],[f774,f78])).
% 1.42/0.57  fof(f774,plain,(
% 1.42/0.57    ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_36),
% 1.42/0.57    inference(subsumption_resolution,[],[f773,f79])).
% 1.42/0.57  fof(f773,plain,(
% 1.42/0.57    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_36),
% 1.42/0.57    inference(subsumption_resolution,[],[f772,f80])).
% 1.42/0.57  fof(f772,plain,(
% 1.42/0.57    ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_36),
% 1.42/0.57    inference(subsumption_resolution,[],[f771,f81])).
% 1.42/0.57  fof(f771,plain,(
% 1.42/0.57    ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_36),
% 1.42/0.57    inference(subsumption_resolution,[],[f770,f82])).
% 1.42/0.57  fof(f770,plain,(
% 1.42/0.57    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_36),
% 1.42/0.57    inference(resolution,[],[f768,f638])).
% 1.42/0.57  fof(f638,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (sP2(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1)) )),
% 1.42/0.57    inference(subsumption_resolution,[],[f119,f91])).
% 1.42/0.57  fof(f119,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (sP2(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f46])).
% 1.42/0.57  fof(f46,plain,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4,X5] : (sP2(X1,X3,X2,X0,X5,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.42/0.57    inference(definition_folding,[],[f41,f45])).
% 1.42/0.57  fof(f45,plain,(
% 1.42/0.57    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP2(X1,X3,X2,X0,X5,X4))),
% 1.42/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.42/0.57  fof(f41,plain,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.42/0.57    inference(flattening,[],[f40])).
% 1.42/0.57  fof(f40,plain,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.42/0.57    inference(ennf_transformation,[],[f17])).
% 1.42/0.57  fof(f17,axiom,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.42/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.42/0.57  fof(f768,plain,(
% 1.42/0.57    ~sP2(sK4,sK6,sK5,sK3,sK8,sK7) | spl10_36),
% 1.42/0.57    inference(resolution,[],[f733,f117])).
% 1.42/0.57  fof(f117,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f69])).
% 1.42/0.57  fof(f69,plain,(
% 1.42/0.57    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0))) & v1_funct_2(k1_tmap_1(X3,X0,X2,X1,X5,X4),k4_subset_1(X3,X2,X1),X0) & v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4))) | ~sP2(X0,X1,X2,X3,X4,X5))),
% 1.42/0.57    inference(rectify,[],[f68])).
% 1.42/0.57  fof(f68,plain,(
% 1.42/0.57    ! [X1,X3,X2,X0,X5,X4] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~sP2(X1,X3,X2,X0,X5,X4))),
% 1.42/0.57    inference(nnf_transformation,[],[f45])).
% 1.42/0.57  fof(f733,plain,(
% 1.42/0.57    ~v1_funct_2(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k4_subset_1(sK3,sK5,sK6),sK4) | spl10_36),
% 1.42/0.57    inference(avatar_component_clause,[],[f731])).
% 1.42/0.57  fof(f674,plain,(
% 1.42/0.57    spl10_19),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f673])).
% 1.42/0.57  fof(f673,plain,(
% 1.42/0.57    $false | spl10_19),
% 1.42/0.57    inference(subsumption_resolution,[],[f672,f71])).
% 1.42/0.57  fof(f672,plain,(
% 1.42/0.57    v1_xboole_0(sK4) | spl10_19),
% 1.42/0.57    inference(subsumption_resolution,[],[f671,f72])).
% 1.42/0.57  fof(f671,plain,(
% 1.42/0.57    v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_19),
% 1.42/0.57    inference(subsumption_resolution,[],[f670,f73])).
% 1.42/0.57  fof(f670,plain,(
% 1.42/0.57    ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_19),
% 1.42/0.57    inference(subsumption_resolution,[],[f669,f74])).
% 1.42/0.57  fof(f669,plain,(
% 1.42/0.57    v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_19),
% 1.42/0.57    inference(subsumption_resolution,[],[f668,f75])).
% 1.42/0.57  fof(f668,plain,(
% 1.42/0.57    ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_19),
% 1.42/0.57    inference(subsumption_resolution,[],[f667,f77])).
% 1.42/0.57  fof(f667,plain,(
% 1.42/0.57    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_19),
% 1.42/0.57    inference(subsumption_resolution,[],[f666,f78])).
% 1.42/0.57  fof(f666,plain,(
% 1.42/0.57    ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_19),
% 1.42/0.57    inference(subsumption_resolution,[],[f665,f79])).
% 1.42/0.57  fof(f665,plain,(
% 1.42/0.57    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_19),
% 1.42/0.57    inference(subsumption_resolution,[],[f664,f80])).
% 1.42/0.57  fof(f664,plain,(
% 1.42/0.57    ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_19),
% 1.42/0.57    inference(subsumption_resolution,[],[f663,f81])).
% 1.42/0.57  fof(f663,plain,(
% 1.42/0.57    ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_19),
% 1.42/0.57    inference(subsumption_resolution,[],[f662,f82])).
% 1.42/0.57  fof(f662,plain,(
% 1.42/0.57    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_19),
% 1.42/0.57    inference(resolution,[],[f659,f638])).
% 1.42/0.57  fof(f659,plain,(
% 1.42/0.57    ~sP2(sK4,sK6,sK5,sK3,sK8,sK7) | spl10_19),
% 1.42/0.57    inference(resolution,[],[f334,f118])).
% 1.42/0.57  fof(f118,plain,(
% 1.42/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X3,X0,X2,X1,X5,X4),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X2,X1),X0))) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f69])).
% 1.42/0.57  fof(f334,plain,(
% 1.42/0.57    ~m1_subset_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK3,sK5,sK6),sK4))) | spl10_19),
% 1.42/0.57    inference(avatar_component_clause,[],[f332])).
% 1.42/0.57  fof(f657,plain,(
% 1.42/0.57    spl10_18),
% 1.42/0.57    inference(avatar_contradiction_clause,[],[f656])).
% 1.42/0.57  fof(f656,plain,(
% 1.42/0.57    $false | spl10_18),
% 1.42/0.57    inference(subsumption_resolution,[],[f655,f71])).
% 1.42/0.57  fof(f655,plain,(
% 1.42/0.57    v1_xboole_0(sK4) | spl10_18),
% 1.42/0.57    inference(subsumption_resolution,[],[f654,f72])).
% 1.42/0.57  fof(f654,plain,(
% 1.42/0.57    v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_18),
% 1.42/0.57    inference(subsumption_resolution,[],[f653,f73])).
% 1.42/0.58  fof(f653,plain,(
% 1.42/0.58    ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_18),
% 1.42/0.58    inference(subsumption_resolution,[],[f652,f74])).
% 1.42/0.58  fof(f652,plain,(
% 1.42/0.58    v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_18),
% 1.42/0.58    inference(subsumption_resolution,[],[f651,f75])).
% 1.42/0.58  fof(f651,plain,(
% 1.42/0.58    ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_18),
% 1.42/0.58    inference(subsumption_resolution,[],[f650,f77])).
% 1.42/0.58  fof(f650,plain,(
% 1.42/0.58    ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_18),
% 1.42/0.58    inference(subsumption_resolution,[],[f649,f78])).
% 1.42/0.58  fof(f649,plain,(
% 1.42/0.58    ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_18),
% 1.42/0.58    inference(subsumption_resolution,[],[f648,f79])).
% 1.42/0.58  fof(f648,plain,(
% 1.42/0.58    ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_18),
% 1.42/0.58    inference(subsumption_resolution,[],[f647,f80])).
% 1.42/0.58  fof(f647,plain,(
% 1.42/0.58    ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_18),
% 1.42/0.58    inference(subsumption_resolution,[],[f646,f81])).
% 1.42/0.58  fof(f646,plain,(
% 1.42/0.58    ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_18),
% 1.42/0.58    inference(subsumption_resolution,[],[f645,f82])).
% 1.42/0.58  fof(f645,plain,(
% 1.42/0.58    ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_2(sK8,sK6,sK4) | ~v1_funct_1(sK8) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_2(sK7,sK5,sK4) | ~v1_funct_1(sK7) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | v1_xboole_0(sK6) | ~m1_subset_1(sK5,k1_zfmisc_1(sK3)) | v1_xboole_0(sK5) | v1_xboole_0(sK4) | spl10_18),
% 1.42/0.58    inference(resolution,[],[f638,f345])).
% 1.42/0.58  fof(f345,plain,(
% 1.42/0.58    ~sP2(sK4,sK6,sK5,sK3,sK8,sK7) | spl10_18),
% 1.42/0.58    inference(resolution,[],[f330,f116])).
% 1.42/0.58  fof(f116,plain,(
% 1.42/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X3,X0,X2,X1,X5,X4)) | ~sP2(X0,X1,X2,X3,X4,X5)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f69])).
% 1.42/0.58  fof(f330,plain,(
% 1.42/0.58    ~v1_funct_1(k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8)) | spl10_18),
% 1.42/0.58    inference(avatar_component_clause,[],[f328])).
% 1.42/0.58  fof(f521,plain,(
% 1.42/0.58    ~spl10_21 | spl10_23),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f520])).
% 1.42/0.58  fof(f520,plain,(
% 1.42/0.58    $false | (~spl10_21 | spl10_23)),
% 1.42/0.58    inference(subsumption_resolution,[],[f519,f75])).
% 1.42/0.58  fof(f519,plain,(
% 1.42/0.58    ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | (~spl10_21 | spl10_23)),
% 1.42/0.58    inference(subsumption_resolution,[],[f517,f423])).
% 1.42/0.58  fof(f423,plain,(
% 1.42/0.58    r1_xboole_0(k1_relat_1(sK8),k3_xboole_0(sK5,sK6)) | ~spl10_21),
% 1.42/0.58    inference(avatar_component_clause,[],[f422])).
% 1.42/0.58  fof(f422,plain,(
% 1.42/0.58    spl10_21 <=> r1_xboole_0(k1_relat_1(sK8),k3_xboole_0(sK5,sK6))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_21])])).
% 1.42/0.58  fof(f517,plain,(
% 1.42/0.58    ~r1_xboole_0(k1_relat_1(sK8),k3_xboole_0(sK5,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | spl10_23),
% 1.42/0.58    inference(superposition,[],[f501,f110])).
% 1.42/0.58  fof(f110,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.42/0.58    inference(cnf_transformation,[],[f34])).
% 1.42/0.58  fof(f34,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.42/0.58    inference(ennf_transformation,[],[f5])).
% 1.42/0.58  fof(f5,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.42/0.58  fof(f501,plain,(
% 1.42/0.58    ~r1_xboole_0(k1_relat_1(sK8),k9_subset_1(sK3,sK5,sK6)) | spl10_23),
% 1.42/0.58    inference(avatar_component_clause,[],[f499])).
% 1.42/0.58  fof(f499,plain,(
% 1.42/0.58    spl10_23 <=> r1_xboole_0(k1_relat_1(sK8),k9_subset_1(sK3,sK5,sK6))),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).
% 1.42/0.58  fof(f508,plain,(
% 1.42/0.58    ~spl10_23 | spl10_24 | ~spl10_1),
% 1.42/0.58    inference(avatar_split_clause,[],[f507,f127,f503,f499])).
% 1.42/0.58  fof(f507,plain,(
% 1.42/0.58    k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~r1_xboole_0(k1_relat_1(sK8),k9_subset_1(sK3,sK5,sK6)) | ~spl10_1),
% 1.42/0.58    inference(subsumption_resolution,[],[f493,f174])).
% 1.42/0.58  fof(f174,plain,(
% 1.42/0.58    v1_relat_1(sK8)),
% 1.42/0.58    inference(resolution,[],[f111,f82])).
% 1.42/0.58  fof(f111,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f35])).
% 1.42/0.58  fof(f35,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.42/0.58    inference(ennf_transformation,[],[f11])).
% 1.42/0.58  fof(f11,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.42/0.58  fof(f493,plain,(
% 1.42/0.58    k1_xboole_0 = k7_relat_1(sK7,k9_subset_1(sK3,sK5,sK6)) | ~r1_xboole_0(k1_relat_1(sK8),k9_subset_1(sK3,sK5,sK6)) | ~v1_relat_1(sK8) | ~spl10_1),
% 1.42/0.58    inference(superposition,[],[f98,f487])).
% 1.42/0.58  % (3907)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.58  
% 1.42/0.58  % (3907)Memory used [KB]: 6908
% 1.42/0.58  % (3907)Time elapsed: 0.138 s
% 1.42/0.58  % (3907)------------------------------
% 1.42/0.58  % (3907)------------------------------
% 1.42/0.58  fof(f98,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f61])).
% 1.42/0.58  fof(f61,plain,(
% 1.42/0.58    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.42/0.58    inference(nnf_transformation,[],[f29])).
% 1.42/0.58  fof(f29,plain,(
% 1.42/0.58    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.42/0.58    inference(ennf_transformation,[],[f9])).
% 1.42/0.58  fof(f9,axiom,(
% 1.42/0.58    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).
% 1.42/0.58  fof(f444,plain,(
% 1.42/0.58    ~spl10_16 | spl10_21),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f443])).
% 1.42/0.58  fof(f443,plain,(
% 1.42/0.58    $false | (~spl10_16 | spl10_21)),
% 1.42/0.58    inference(subsumption_resolution,[],[f442,f248])).
% 1.42/0.58  fof(f248,plain,(
% 1.42/0.58    r1_xboole_0(sK5,sK6)),
% 1.42/0.58    inference(resolution,[],[f247,f76])).
% 1.42/0.58  fof(f76,plain,(
% 1.42/0.58    r1_subset_1(sK5,sK6)),
% 1.42/0.58    inference(cnf_transformation,[],[f53])).
% 1.42/0.58  fof(f247,plain,(
% 1.42/0.58    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | r1_xboole_0(X0,X1)) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f246,f244])).
% 1.42/0.58  fof(f244,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~v1_xboole_0(X0)) )),
% 1.42/0.58    inference(resolution,[],[f239,f92])).
% 1.42/0.58  fof(f92,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f60])).
% 1.42/0.58  fof(f60,plain,(
% 1.42/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.42/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f26,f59])).
% 1.42/0.58  fof(f59,plain,(
% 1.42/0.58    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK9(X0,X1),X1) & r2_hidden(sK9(X0,X1),X0)))),
% 1.42/0.58    introduced(choice_axiom,[])).
% 1.42/0.58  fof(f26,plain,(
% 1.42/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.42/0.58    inference(ennf_transformation,[],[f20])).
% 1.42/0.58  fof(f20,plain,(
% 1.42/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.42/0.58    inference(rectify,[],[f3])).
% 1.42/0.58  fof(f3,axiom,(
% 1.42/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.42/0.58  fof(f239,plain,(
% 1.42/0.58    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) )),
% 1.42/0.58    inference(resolution,[],[f235,f124])).
% 1.42/0.58  fof(f124,plain,(
% 1.42/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.42/0.58    inference(equality_resolution,[],[f104])).
% 1.42/0.58  fof(f104,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.42/0.58    inference(cnf_transformation,[],[f65])).
% 1.42/0.58  fof(f65,plain,(
% 1.42/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.58    inference(flattening,[],[f64])).
% 1.42/0.58  fof(f64,plain,(
% 1.42/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.42/0.58    inference(nnf_transformation,[],[f4])).
% 1.42/0.58  fof(f4,axiom,(
% 1.42/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.42/0.58  fof(f235,plain,(
% 1.42/0.58    ( ! [X6,X4,X5] : (~r1_tarski(X6,X4) | ~r2_hidden(X5,X6) | ~v1_xboole_0(X4)) )),
% 1.42/0.58    inference(resolution,[],[f114,f109])).
% 1.42/0.58  fof(f109,plain,(
% 1.42/0.58    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f67])).
% 1.42/0.58  fof(f67,plain,(
% 1.42/0.58    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.42/0.58    inference(nnf_transformation,[],[f7])).
% 1.42/0.58  fof(f7,axiom,(
% 1.42/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.42/0.58  fof(f114,plain,(
% 1.42/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f37])).
% 1.42/0.58  fof(f37,plain,(
% 1.42/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.42/0.58    inference(ennf_transformation,[],[f8])).
% 1.42/0.58  fof(f8,axiom,(
% 1.42/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.42/0.58  fof(f246,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X0)) )),
% 1.42/0.58    inference(subsumption_resolution,[],[f99,f245])).
% 1.42/0.58  fof(f245,plain,(
% 1.42/0.58    ( ! [X2,X3] : (r1_xboole_0(X3,X2) | ~v1_xboole_0(X2)) )),
% 1.42/0.58    inference(resolution,[],[f239,f93])).
% 1.42/0.58  fof(f93,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r2_hidden(sK9(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f60])).
% 1.42/0.58  fof(f99,plain,(
% 1.42/0.58    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f62])).
% 1.42/0.58  fof(f62,plain,(
% 1.42/0.58    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.42/0.58    inference(nnf_transformation,[],[f31])).
% 1.42/0.58  fof(f31,plain,(
% 1.42/0.58    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.42/0.58    inference(flattening,[],[f30])).
% 1.42/0.58  fof(f30,plain,(
% 1.42/0.58    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.42/0.58    inference(ennf_transformation,[],[f10])).
% 1.42/0.58  fof(f10,axiom,(
% 1.42/0.58    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.42/0.58  fof(f442,plain,(
% 1.42/0.58    ~r1_xboole_0(sK5,sK6) | (~spl10_16 | spl10_21)),
% 1.42/0.58    inference(subsumption_resolution,[],[f440,f296])).
% 1.42/0.58  fof(f296,plain,(
% 1.42/0.58    r1_xboole_0(k1_relat_1(sK8),k1_xboole_0) | ~spl10_16),
% 1.42/0.58    inference(avatar_component_clause,[],[f295])).
% 1.42/0.58  fof(f295,plain,(
% 1.42/0.58    spl10_16 <=> r1_xboole_0(k1_relat_1(sK8),k1_xboole_0)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_16])])).
% 1.42/0.58  fof(f440,plain,(
% 1.42/0.58    ~r1_xboole_0(k1_relat_1(sK8),k1_xboole_0) | ~r1_xboole_0(sK5,sK6) | spl10_21),
% 1.42/0.58    inference(superposition,[],[f424,f106])).
% 1.42/0.58  fof(f106,plain,(
% 1.42/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.42/0.58    inference(cnf_transformation,[],[f66])).
% 1.42/0.58  fof(f66,plain,(
% 1.42/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.42/0.58    inference(nnf_transformation,[],[f1])).
% 1.42/0.58  fof(f1,axiom,(
% 1.42/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.42/0.58  fof(f424,plain,(
% 1.42/0.58    ~r1_xboole_0(k1_relat_1(sK8),k3_xboole_0(sK5,sK6)) | spl10_21),
% 1.42/0.58    inference(avatar_component_clause,[],[f422])).
% 1.42/0.58  fof(f324,plain,(
% 1.42/0.58    spl10_17),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f323])).
% 1.42/0.58  fof(f323,plain,(
% 1.42/0.58    $false | spl10_17),
% 1.42/0.58    inference(subsumption_resolution,[],[f320,f84])).
% 1.42/0.58  fof(f84,plain,(
% 1.42/0.58    v1_xboole_0(k1_xboole_0)),
% 1.42/0.58    inference(cnf_transformation,[],[f2])).
% 1.42/0.58  fof(f2,axiom,(
% 1.42/0.58    v1_xboole_0(k1_xboole_0)),
% 1.42/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.42/0.58  fof(f320,plain,(
% 1.42/0.58    ~v1_xboole_0(k1_xboole_0) | spl10_17),
% 1.42/0.58    inference(resolution,[],[f316,f245])).
% 1.42/0.58  fof(f316,plain,(
% 1.42/0.58    ~r1_xboole_0(k1_relat_1(sK7),k1_xboole_0) | spl10_17),
% 1.42/0.58    inference(subsumption_resolution,[],[f315,f173])).
% 1.42/0.58  fof(f173,plain,(
% 1.42/0.58    v1_relat_1(sK7)),
% 1.42/0.58    inference(resolution,[],[f111,f79])).
% 1.42/0.58  fof(f315,plain,(
% 1.42/0.58    ~r1_xboole_0(k1_relat_1(sK7),k1_xboole_0) | ~v1_relat_1(sK7) | spl10_17),
% 1.42/0.58    inference(trivial_inequality_removal,[],[f314])).
% 1.42/0.58  fof(f314,plain,(
% 1.42/0.58    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_relat_1(sK7),k1_xboole_0) | ~v1_relat_1(sK7) | spl10_17),
% 1.42/0.58    inference(superposition,[],[f301,f98])).
% 1.42/0.58  fof(f301,plain,(
% 1.42/0.58    k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0) | spl10_17),
% 1.42/0.58    inference(avatar_component_clause,[],[f299])).
% 1.42/0.58  fof(f299,plain,(
% 1.42/0.58    spl10_17 <=> k1_xboole_0 = k7_relat_1(sK7,k1_xboole_0)),
% 1.42/0.58    introduced(avatar_definition,[new_symbols(naming,[spl10_17])])).
% 1.42/0.58  fof(f310,plain,(
% 1.42/0.58    spl10_16),
% 1.42/0.58    inference(avatar_contradiction_clause,[],[f309])).
% 1.42/0.58  fof(f309,plain,(
% 1.42/0.58    $false | spl10_16),
% 1.42/0.58    inference(subsumption_resolution,[],[f306,f84])).
% 1.42/0.58  fof(f306,plain,(
% 1.42/0.58    ~v1_xboole_0(k1_xboole_0) | spl10_16),
% 1.42/0.58    inference(resolution,[],[f297,f245])).
% 1.42/0.58  fof(f297,plain,(
% 1.42/0.58    ~r1_xboole_0(k1_relat_1(sK8),k1_xboole_0) | spl10_16),
% 1.42/0.58    inference(avatar_component_clause,[],[f295])).
% 1.42/0.58  fof(f302,plain,(
% 1.42/0.58    ~spl10_16 | ~spl10_17 | spl10_1),
% 1.42/0.58    inference(avatar_split_clause,[],[f293,f127,f299,f295])).
% 1.42/0.58  fof(f293,plain,(
% 1.42/0.58    k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0) | ~r1_xboole_0(k1_relat_1(sK8),k1_xboole_0) | spl10_1),
% 1.42/0.58    inference(subsumption_resolution,[],[f292,f174])).
% 1.42/0.58  fof(f292,plain,(
% 1.42/0.58    k1_xboole_0 != k7_relat_1(sK7,k1_xboole_0) | ~r1_xboole_0(k1_relat_1(sK8),k1_xboole_0) | ~v1_relat_1(sK8) | spl10_1),
% 1.42/0.58    inference(superposition,[],[f291,f98])).
% 1.42/0.58  fof(f291,plain,(
% 1.42/0.58    k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) | spl10_1),
% 1.42/0.58    inference(subsumption_resolution,[],[f290,f77])).
% 1.42/0.58  fof(f290,plain,(
% 1.42/0.58    k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) | ~v1_funct_1(sK7) | spl10_1),
% 1.42/0.58    inference(subsumption_resolution,[],[f289,f79])).
% 1.42/0.58  fof(f289,plain,(
% 1.42/0.58    k7_relat_1(sK8,k1_xboole_0) != k7_relat_1(sK7,k1_xboole_0) | ~m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK4))) | ~v1_funct_1(sK7) | spl10_1),
% 1.42/0.58    inference(superposition,[],[f288,f115])).
% 1.42/0.58  fof(f288,plain,(
% 1.42/0.58    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0) | spl10_1),
% 1.42/0.58    inference(subsumption_resolution,[],[f287,f80])).
% 1.42/0.58  fof(f287,plain,(
% 1.42/0.58    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0) | ~v1_funct_1(sK8) | spl10_1),
% 1.42/0.58    inference(subsumption_resolution,[],[f282,f82])).
% 1.42/0.58  fof(f282,plain,(
% 1.42/0.58    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k7_relat_1(sK8,k1_xboole_0) | ~m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK4))) | ~v1_funct_1(sK8) | spl10_1),
% 1.42/0.58    inference(superposition,[],[f267,f115])).
% 1.42/0.58  fof(f267,plain,(
% 1.42/0.58    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0) | spl10_1),
% 1.42/0.58    inference(subsumption_resolution,[],[f266,f248])).
% 1.42/0.58  fof(f266,plain,(
% 1.42/0.58    k2_partfun1(sK5,sK4,sK7,k1_xboole_0) != k2_partfun1(sK6,sK4,sK8,k1_xboole_0) | ~r1_xboole_0(sK5,sK6) | spl10_1),
% 1.42/0.58    inference(superposition,[],[f265,f106])).
% 1.42/0.58  fof(f265,plain,(
% 1.42/0.58    k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6)) | spl10_1),
% 1.42/0.58    inference(subsumption_resolution,[],[f264,f75])).
% 1.42/0.58  fof(f264,plain,(
% 1.42/0.58    k2_partfun1(sK5,sK4,sK7,k3_xboole_0(sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k3_xboole_0(sK5,sK6)) | ~m1_subset_1(sK6,k1_zfmisc_1(sK3)) | spl10_1),
% 1.42/0.58    inference(superposition,[],[f129,f110])).
% 1.42/0.58  fof(f129,plain,(
% 1.42/0.58    k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6)) | spl10_1),
% 1.42/0.58    inference(avatar_component_clause,[],[f127])).
% 1.42/0.58  fof(f138,plain,(
% 1.42/0.58    ~spl10_1 | ~spl10_2 | ~spl10_3),
% 1.42/0.58    inference(avatar_split_clause,[],[f83,f135,f131,f127])).
% 1.42/0.58  fof(f83,plain,(
% 1.42/0.58    sK8 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK6) | sK7 != k2_partfun1(k4_subset_1(sK3,sK5,sK6),sK4,k1_tmap_1(sK3,sK4,sK5,sK6,sK7,sK8),sK5) | k2_partfun1(sK5,sK4,sK7,k9_subset_1(sK3,sK5,sK6)) != k2_partfun1(sK6,sK4,sK8,k9_subset_1(sK3,sK5,sK6))),
% 1.42/0.58    inference(cnf_transformation,[],[f53])).
% 1.42/0.58  % SZS output end Proof for theBenchmark
% 1.42/0.58  % (3906)------------------------------
% 1.42/0.58  % (3906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.58  % (3906)Termination reason: Refutation
% 1.42/0.58  
% 1.42/0.58  % (3906)Memory used [KB]: 6780
% 1.42/0.58  % (3906)Time elapsed: 0.120 s
% 1.42/0.58  % (3906)------------------------------
% 1.42/0.58  % (3906)------------------------------
% 1.42/0.58  % (3901)Success in time 0.212 s
%------------------------------------------------------------------------------
