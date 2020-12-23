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
% DateTime   : Thu Dec  3 13:17:28 EST 2020

% Result     : Theorem 2.38s
% Output     : Refutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :  276 (10706 expanded)
%              Number of leaves         :   47 (5091 expanded)
%              Depth                    :   29
%              Number of atoms          : 1313 (153532 expanded)
%              Number of equality atoms :  239 (34221 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f143,f572,f907,f1017,f1026,f1032,f1060,f1079,f1087,f1089,f1097,f1099,f1115,f1127,f1130,f1133,f1136])).

fof(f1136,plain,(
    ~ spl7_49 ),
    inference(avatar_contradiction_clause,[],[f1135])).

fof(f1135,plain,
    ( $false
    | ~ spl7_49 ),
    inference(subsumption_resolution,[],[f81,f1041])).

fof(f1041,plain,
    ( v1_xboole_0(sK3)
    | ~ spl7_49 ),
    inference(avatar_component_clause,[],[f1040])).

fof(f1040,plain,
    ( spl7_49
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).

fof(f81,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,
    ( ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
      | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_2(sK5,sK3,sK1)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & r1_subset_1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f30,f66,f65,f64,f63,f62,f61])).

fof(f61,plain,
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
                          ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f62,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X5,X3,X1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                    & v1_funct_2(X4,X2,X1)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(sK0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(sK0))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5
                        | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4
                        | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                      & v1_funct_2(X5,X3,sK1)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
                  & v1_funct_2(X4,X2,sK1)
                  & v1_funct_1(X4) )
              & r1_subset_1(X2,X3)
              & m1_subset_1(X3,k1_zfmisc_1(sK0))
              & ~ v1_xboole_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0))
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4
                      | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                    & v1_funct_2(X5,X3,sK1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
                & v1_funct_2(X4,X2,sK1)
                & v1_funct_1(X4) )
            & r1_subset_1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(sK0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0))
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5
                    | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4
                    | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                  & v1_funct_2(X5,X3,sK1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
              & v1_funct_2(X4,sK2,sK1)
              & v1_funct_1(X4) )
          & r1_subset_1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(sK0))
          & ~ v1_xboole_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5
                  | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4
                  | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                & v1_funct_2(X5,X3,sK1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
            & v1_funct_2(X4,sK2,sK1)
            & v1_funct_1(X4) )
        & r1_subset_1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(sK0))
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5
                | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4
                | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
              & v1_funct_2(X5,sK3,sK1)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X4,sK2,sK1)
          & v1_funct_1(X4) )
      & r1_subset_1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(sK0))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f65,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5
              | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4
              | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
            & v1_funct_2(X5,sK3,sK1)
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        & v1_funct_2(X4,sK2,sK1)
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5
            | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2)
            | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
          & v1_funct_2(X5,sK3,sK1)
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & v1_funct_2(sK4,sK2,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ? [X5] :
        ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5
          | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2)
          | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        & v1_funct_2(X5,sK3,sK1)
        & v1_funct_1(X5) )
   => ( ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
        | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
        | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      & v1_funct_2(sK5,sK3,sK1)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
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
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
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

fof(f1133,plain,(
    ~ spl7_45 ),
    inference(avatar_contradiction_clause,[],[f1132])).

fof(f1132,plain,
    ( $false
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f79,f999])).

fof(f999,plain,
    ( v1_xboole_0(sK2)
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f998])).

fof(f998,plain,
    ( spl7_45
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f79,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f67])).

fof(f1130,plain,(
    ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f1129])).

fof(f1129,plain,
    ( $false
    | ~ spl7_44 ),
    inference(subsumption_resolution,[],[f78,f996])).

fof(f996,plain,
    ( v1_xboole_0(sK1)
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f995])).

fof(f995,plain,
    ( spl7_44
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f78,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f1127,plain,(
    ~ spl7_43 ),
    inference(avatar_contradiction_clause,[],[f1126])).

fof(f1126,plain,
    ( $false
    | ~ spl7_43 ),
    inference(subsumption_resolution,[],[f77,f993])).

fof(f993,plain,
    ( v1_xboole_0(sK0)
    | ~ spl7_43 ),
    inference(avatar_component_clause,[],[f992])).

fof(f992,plain,
    ( spl7_43
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).

fof(f77,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f67])).

fof(f1115,plain,
    ( spl7_43
    | spl7_44
    | spl7_45
    | ~ spl7_46
    | spl7_49
    | ~ spl7_50
    | ~ spl7_47
    | ~ spl7_48
    | ~ spl7_20
    | ~ spl7_51
    | ~ spl7_52
    | ~ spl7_53
    | spl7_42 ),
    inference(avatar_split_clause,[],[f1114,f916,f1052,f1049,f1046,f565,f1007,f1004,f1043,f1040,f1001,f998,f995,f992])).

fof(f1001,plain,
    ( spl7_46
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).

fof(f1043,plain,
    ( spl7_50
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).

fof(f1004,plain,
    ( spl7_47
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).

fof(f1007,plain,
    ( spl7_48
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f565,plain,
    ( spl7_20
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f1046,plain,
    ( spl7_51
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).

fof(f1049,plain,
    ( spl7_52
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).

fof(f1052,plain,
    ( spl7_53
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).

fof(f916,plain,
    ( spl7_42
  <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).

fof(f1114,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl7_42 ),
    inference(resolution,[],[f917,f124])).

fof(f124,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
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
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
    inference(flattening,[],[f59])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
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

fof(f917,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | spl7_42 ),
    inference(avatar_component_clause,[],[f916])).

fof(f1099,plain,(
    spl7_53 ),
    inference(avatar_contradiction_clause,[],[f1098])).

fof(f1098,plain,
    ( $false
    | spl7_53 ),
    inference(subsumption_resolution,[],[f89,f1053])).

fof(f1053,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | spl7_53 ),
    inference(avatar_component_clause,[],[f1052])).

fof(f89,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f67])).

fof(f1097,plain,
    ( spl7_3
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f1096,f916,f141])).

fof(f141,plain,
    ( spl7_3
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f1096,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    inference(global_subsumption,[],[f77,f78,f89,f86,f353,f80,f84,f85,f82,f87,f88,f1095])).

fof(f1095,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(trivial_inequality_removal,[],[f1094])).

fof(f1094,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f1093,f768])).

fof(f768,plain,(
    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    inference(forward_demodulation,[],[f767,f452])).

fof(f452,plain,(
    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f449,f91])).

fof(f91,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f449,plain,(
    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0)) ),
    inference(resolution,[],[f431,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f431,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(global_subsumption,[],[f155,f428])).

fof(f428,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f107,f403])).

fof(f403,plain,(
    k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) ),
    inference(global_subsumption,[],[f220,f339,f402])).

fof(f402,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f219,f102])).

fof(f102,plain,(
    ! [X0] :
      ( r1_xboole_0(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( r1_xboole_0(sK6(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ? [X1] : r1_xboole_0(X1,X0)
     => r1_xboole_0(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r1_xboole_0(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ~ ( ! [X1] : ~ r1_xboole_0(X1,X0)
        & k1_xboole_0 != X0 ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( r1_xboole_0(X1,X0)
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

fof(f219,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK2)
      | k1_xboole_0 = k7_relat_1(sK4,X1) ) ),
    inference(global_subsumption,[],[f155,f216])).

fof(f216,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK2)
      | k1_xboole_0 = k7_relat_1(sK4,X1)
      | ~ v1_relat_1(sK4) ) ),
    inference(superposition,[],[f100,f196])).

fof(f196,plain,(
    sK2 = k1_relat_1(sK4) ),
    inference(global_subsumption,[],[f155,f154,f195])).

fof(f195,plain,
    ( sK2 = k1_relat_1(sK4)
    | ~ v4_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f162,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f162,plain,(
    v1_partfun1(sK4,sK2) ),
    inference(global_subsumption,[],[f78,f84,f85,f156])).

fof(f156,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_partfun1(sK4,sK2)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f86,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | v1_partfun1(X2,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f154,plain,(
    v4_relat_1(sK4,sK2) ),
    inference(resolution,[],[f86,f121])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f339,plain,(
    k1_xboole_0 != k2_relat_1(sK4) ),
    inference(global_subsumption,[],[f155,f329,f338])).

fof(f338,plain,
    ( r1_xboole_0(sK2,sK2)
    | k1_xboole_0 != k2_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(forward_demodulation,[],[f337,f196])).

fof(f337,plain,
    ( k1_xboole_0 != k2_relat_1(sK4)
    | r1_xboole_0(k1_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f109,f336])).

fof(f336,plain,(
    k2_relat_1(sK4) = k9_relat_1(sK4,sK2) ),
    inference(forward_demodulation,[],[f170,f196])).

fof(f170,plain,(
    k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4) ),
    inference(resolution,[],[f155,f97])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f109,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k9_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k9_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

fof(f329,plain,(
    ~ r1_xboole_0(sK2,sK2) ),
    inference(global_subsumption,[],[f79,f328])).

fof(f328,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f319,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_xboole_0(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f319,plain,(
    r1_tarski(sK2,sK2) ),
    inference(global_subsumption,[],[f155,f318])).

fof(f318,plain,
    ( r1_tarski(sK2,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(forward_demodulation,[],[f316,f196])).

fof(f316,plain,
    ( r1_tarski(k1_relat_1(sK4),sK2)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f108,f194])).

fof(f194,plain,(
    sK4 = k7_relat_1(sK4,sK2) ),
    inference(global_subsumption,[],[f155,f193])).

fof(f193,plain,
    ( sK4 = k7_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f154,f113])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

fof(f220,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = k2_relat_1(sK4) ),
    inference(global_subsumption,[],[f155,f217])).

fof(f217,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = k2_relat_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f98,f196])).

fof(f98,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_relat_1(X0)
      | k1_xboole_0 = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

fof(f107,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f155,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f86,f120])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f767,plain,(
    k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f766,f588])).

fof(f588,plain,(
    k1_xboole_0 = k7_relat_1(sK5,sK2) ),
    inference(resolution,[],[f251,f145])).

fof(f145,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(global_subsumption,[],[f79,f81,f144])).

fof(f144,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f83,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f83,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f67])).

fof(f251,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK3)
      | k1_xboole_0 = k7_relat_1(sK5,X1) ) ),
    inference(global_subsumption,[],[f176,f248])).

fof(f248,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,sK3)
      | k1_xboole_0 = k7_relat_1(sK5,X1)
      | ~ v1_relat_1(sK5) ) ),
    inference(superposition,[],[f100,f200])).

fof(f200,plain,(
    sK3 = k1_relat_1(sK5) ),
    inference(global_subsumption,[],[f176,f175,f199])).

fof(f199,plain,
    ( sK3 = k1_relat_1(sK5)
    | ~ v4_relat_1(sK5,sK3)
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f183,f114])).

fof(f183,plain,(
    v1_partfun1(sK5,sK3) ),
    inference(global_subsumption,[],[f78,f87,f88,f177])).

fof(f177,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | v1_partfun1(sK5,sK3)
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f89,f106])).

fof(f175,plain,(
    v4_relat_1(sK5,sK3) ),
    inference(resolution,[],[f89,f121])).

fof(f176,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f89,f120])).

fof(f766,plain,(
    k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0) ),
    inference(resolution,[],[f594,f176])).

fof(f594,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_xboole_0) = k7_relat_1(k7_relat_1(X0,sK2),k1_xboole_0) ) ),
    inference(resolution,[],[f593,f118])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)
      | ~ r1_tarski(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_tarski(X0,X1)
       => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

fof(f593,plain,(
    r1_tarski(k1_xboole_0,sK2) ),
    inference(global_subsumption,[],[f176,f592])).

fof(f592,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | ~ v1_relat_1(sK5) ),
    inference(forward_demodulation,[],[f590,f91])).

fof(f590,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK2)
    | ~ v1_relat_1(sK5) ),
    inference(superposition,[],[f108,f588])).

fof(f1093,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f1092,f182])).

fof(f182,plain,(
    ! [X6] : k2_partfun1(sK3,sK1,sK5,X6) = k7_relat_1(sK5,X6) ),
    inference(global_subsumption,[],[f87,f174])).

fof(f174,plain,(
    ! [X6] :
      ( k2_partfun1(sK3,sK1,sK5,X6) = k7_relat_1(sK5,X6)
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f89,f122])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f1092,plain,
    ( k1_xboole_0 != k2_partfun1(sK3,sK1,sK5,k1_xboole_0)
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f1091,f897])).

fof(f897,plain,(
    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    inference(forward_demodulation,[],[f896,f452])).

fof(f896,plain,(
    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f893,f403])).

fof(f893,plain,(
    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK6(sK2)),k1_xboole_0) ),
    inference(resolution,[],[f470,f155])).

fof(f470,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(k7_relat_1(X0,sK6(sK2)),k1_xboole_0) = k7_relat_1(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f430,f118])).

fof(f430,plain,(
    r1_tarski(k1_xboole_0,sK6(sK2)) ),
    inference(global_subsumption,[],[f155,f429])).

fof(f429,plain,
    ( r1_tarski(k1_xboole_0,sK6(sK2))
    | ~ v1_relat_1(sK4) ),
    inference(forward_demodulation,[],[f427,f91])).

fof(f427,plain,
    ( r1_tarski(k1_relat_1(k1_xboole_0),sK6(sK2))
    | ~ v1_relat_1(sK4) ),
    inference(superposition,[],[f108,f403])).

fof(f1091,plain,
    ( k2_partfun1(sK3,sK1,sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f1090,f161])).

fof(f161,plain,(
    ! [X6] : k2_partfun1(sK2,sK1,sK4,X6) = k7_relat_1(sK4,X6) ),
    inference(global_subsumption,[],[f84,f153])).

fof(f153,plain,(
    ! [X6] :
      ( k2_partfun1(sK2,sK1,sK4,X6) = k7_relat_1(sK4,X6)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f86,f122])).

fof(f1090,plain,
    ( k2_partfun1(sK3,sK1,sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f544,f314])).

fof(f314,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f79,f84,f85,f311])).

fof(f311,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1)))
      | ~ v1_funct_2(sK4,sK2,sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f181,f86])).

fof(f181,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1)))
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(X3) ) ),
    inference(global_subsumption,[],[f78,f81,f87,f88,f173])).

fof(f173,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1)))
      | ~ v1_funct_2(sK5,sK3,sK1)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X3) ) ),
    inference(resolution,[],[f89,f125])).

fof(f125,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
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
    inference(cnf_transformation,[],[f60])).

fof(f544,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0)))
      | k2_partfun1(sK2,X0,X1,k1_xboole_0) != k2_partfun1(sK3,X0,X2,k1_xboole_0)
      | ~ v1_funct_2(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k4_subset_1(sK0,sK2,sK3),X0)
      | ~ v1_funct_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_2(X2,sK3,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_2(X1,sK2,X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f79,f80,f539])).

fof(f539,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(sK2,X0,X1,k1_xboole_0) != k2_partfun1(sK3,X0,X2,k1_xboole_0)
      | ~ m1_subset_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0)))
      | ~ v1_funct_2(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k4_subset_1(sK0,sK2,sK3),X0)
      | ~ v1_funct_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK3) = X2
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_2(X2,sK3,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_2(X1,sK2,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f212,f146])).

fof(f146,plain,(
    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    inference(resolution,[],[f145,f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f116,f103])).

fof(f103,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f116,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
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

fof(f212,plain,(
    ! [X6,X4,X7,X5] :
      ( k2_partfun1(X4,X5,X6,k1_setfam_1(k2_tarski(X4,sK3))) != k2_partfun1(sK3,X5,X7,k1_setfam_1(k2_tarski(X4,sK3)))
      | ~ m1_subset_1(k1_tmap_1(sK0,X5,X4,sK3,X6,X7),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,X4,sK3),X5)))
      | ~ v1_funct_2(k1_tmap_1(sK0,X5,X4,sK3,X6,X7),k4_subset_1(sK0,X4,sK3),X5)
      | ~ v1_funct_1(k1_tmap_1(sK0,X5,X4,sK3,X6,X7))
      | k2_partfun1(k4_subset_1(sK0,X4,sK3),X5,k1_tmap_1(sK0,X5,X4,sK3,X6,X7),sK3) = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK3,X5)))
      | ~ v1_funct_2(X7,sK3,X5)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(X6,X4,X5)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK0))
      | v1_xboole_0(X4)
      | v1_xboole_0(X5) ) ),
    inference(global_subsumption,[],[f77,f81,f82,f209])).

fof(f209,plain,(
    ! [X6,X4,X7,X5] :
      ( k2_partfun1(X4,X5,X6,k1_setfam_1(k2_tarski(X4,sK3))) != k2_partfun1(sK3,X5,X7,k1_setfam_1(k2_tarski(X4,sK3)))
      | ~ m1_subset_1(k1_tmap_1(sK0,X5,X4,sK3,X6,X7),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,X4,sK3),X5)))
      | ~ v1_funct_2(k1_tmap_1(sK0,X5,X4,sK3,X6,X7),k4_subset_1(sK0,X4,sK3),X5)
      | ~ v1_funct_1(k1_tmap_1(sK0,X5,X4,sK3,X6,X7))
      | k2_partfun1(k4_subset_1(sK0,X4,sK3),X5,k1_tmap_1(sK0,X5,X4,sK3,X6,X7),sK3) = X7
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK3,X5)))
      | ~ v1_funct_2(X7,sK3,X5)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
      | ~ v1_funct_2(X6,X4,X5)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(sK0))
      | v1_xboole_0(X4)
      | v1_xboole_0(X5)
      | v1_xboole_0(sK0) ) ),
    inference(superposition,[],[f131,f149])).

fof(f149,plain,(
    ! [X0] : k9_subset_1(sK0,X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3)) ),
    inference(resolution,[],[f82,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) ) ),
    inference(definition_unfolding,[],[f119,f103])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f131,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
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
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6
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
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
                                & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
                                  | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
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
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
                                & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
                                  | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
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
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
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

fof(f88,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f87,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f67])).

fof(f82,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f67])).

fof(f85,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f67])).

fof(f84,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f67])).

fof(f80,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f67])).

fof(f353,plain,(
    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(global_subsumption,[],[f77,f80,f352])).

fof(f352,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f304,f82])).

fof(f304,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f79,f84,f85,f301])).

fof(f301,plain,(
    ! [X0] :
      ( v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | ~ v1_funct_2(sK4,sK2,sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f180,f86])).

fof(f180,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | v1_funct_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f78,f81,f87,f88,f172])).

fof(f172,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5))
      | ~ v1_funct_2(sK5,sK3,sK1)
      | ~ v1_funct_1(sK5)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1)))
      | ~ v1_funct_2(X2,X1,sK1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X1)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f89,f123])).

fof(f123,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
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
    inference(cnf_transformation,[],[f60])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f67])).

fof(f1089,plain,(
    spl7_52 ),
    inference(avatar_contradiction_clause,[],[f1088])).

fof(f1088,plain,
    ( $false
    | spl7_52 ),
    inference(subsumption_resolution,[],[f88,f1050])).

fof(f1050,plain,
    ( ~ v1_funct_2(sK5,sK3,sK1)
    | spl7_52 ),
    inference(avatar_component_clause,[],[f1049])).

fof(f1087,plain,
    ( spl7_2
    | ~ spl7_42 ),
    inference(avatar_split_clause,[],[f1086,f916,f138])).

fof(f138,plain,
    ( spl7_2
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f1086,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    inference(global_subsumption,[],[f77,f78,f88,f89,f86,f353,f80,f84,f85,f82,f87,f1085])).

fof(f1085,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(trivial_inequality_removal,[],[f1084])).

fof(f1084,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f1083,f768])).

fof(f1083,plain,
    ( k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0)
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f1082,f182])).

fof(f1082,plain,
    ( k1_xboole_0 != k2_partfun1(sK3,sK1,sK5,k1_xboole_0)
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f1081,f897])).

fof(f1081,plain,
    ( k2_partfun1(sK3,sK1,sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(forward_demodulation,[],[f1080,f161])).

fof(f1080,plain,
    ( k2_partfun1(sK3,sK1,sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f534,f314])).

fof(f534,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0)))
      | k2_partfun1(sK2,X0,X1,k1_xboole_0) != k2_partfun1(sK3,X0,X2,k1_xboole_0)
      | ~ v1_funct_2(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k4_subset_1(sK0,sK2,sK3),X0)
      | ~ v1_funct_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK2) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_2(X2,sK3,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_2(X1,sK2,X0)
      | ~ v1_funct_1(X1)
      | v1_xboole_0(X0) ) ),
    inference(global_subsumption,[],[f79,f80,f529])).

fof(f529,plain,(
    ! [X2,X0,X1] :
      ( k2_partfun1(sK2,X0,X1,k1_xboole_0) != k2_partfun1(sK3,X0,X2,k1_xboole_0)
      | ~ m1_subset_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0)))
      | ~ v1_funct_2(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k4_subset_1(sK0,sK2,sK3),X0)
      | ~ v1_funct_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2))
      | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK2) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0)))
      | ~ v1_funct_2(X2,sK3,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0)))
      | ~ v1_funct_2(X1,sK2,X0)
      | ~ v1_funct_1(X1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f211,f146])).

fof(f211,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK3))) != k2_partfun1(sK3,X1,X3,k1_setfam_1(k2_tarski(X0,sK3)))
      | ~ m1_subset_1(k1_tmap_1(sK0,X1,X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,X0,sK3),X1)))
      | ~ v1_funct_2(k1_tmap_1(sK0,X1,X0,sK3,X2,X3),k4_subset_1(sK0,X0,sK3),X1)
      | ~ v1_funct_1(k1_tmap_1(sK0,X1,X0,sK3,X2,X3))
      | k2_partfun1(k4_subset_1(sK0,X0,sK3),X1,k1_tmap_1(sK0,X1,X0,sK3,X2,X3),X0) = X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
      | ~ v1_funct_2(X3,sK3,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(global_subsumption,[],[f77,f81,f82,f208])).

fof(f208,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK3))) != k2_partfun1(sK3,X1,X3,k1_setfam_1(k2_tarski(X0,sK3)))
      | ~ m1_subset_1(k1_tmap_1(sK0,X1,X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,X0,sK3),X1)))
      | ~ v1_funct_2(k1_tmap_1(sK0,X1,X0,sK3,X2,X3),k4_subset_1(sK0,X0,sK3),X1)
      | ~ v1_funct_1(k1_tmap_1(sK0,X1,X0,sK3,X2,X3))
      | k2_partfun1(k4_subset_1(sK0,X0,sK3),X1,k1_tmap_1(sK0,X1,X0,sK3,X2,X3),X0) = X2
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1)))
      | ~ v1_funct_2(X3,sK3,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
      | v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | v1_xboole_0(sK0) ) ),
    inference(superposition,[],[f132,f149])).

fof(f132,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
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
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6
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
    inference(cnf_transformation,[],[f69])).

fof(f1079,plain,(
    spl7_51 ),
    inference(avatar_contradiction_clause,[],[f1078])).

fof(f1078,plain,
    ( $false
    | spl7_51 ),
    inference(subsumption_resolution,[],[f87,f1047])).

fof(f1047,plain,
    ( ~ v1_funct_1(sK5)
    | spl7_51 ),
    inference(avatar_component_clause,[],[f1046])).

fof(f1060,plain,(
    spl7_50 ),
    inference(avatar_contradiction_clause,[],[f1059])).

fof(f1059,plain,
    ( $false
    | spl7_50 ),
    inference(subsumption_resolution,[],[f82,f1044])).

fof(f1044,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | spl7_50 ),
    inference(avatar_component_clause,[],[f1043])).

fof(f1032,plain,(
    spl7_48 ),
    inference(avatar_contradiction_clause,[],[f1031])).

fof(f1031,plain,
    ( $false
    | spl7_48 ),
    inference(subsumption_resolution,[],[f85,f1008])).

fof(f1008,plain,
    ( ~ v1_funct_2(sK4,sK2,sK1)
    | spl7_48 ),
    inference(avatar_component_clause,[],[f1007])).

fof(f1026,plain,(
    spl7_47 ),
    inference(avatar_contradiction_clause,[],[f1025])).

fof(f1025,plain,
    ( $false
    | spl7_47 ),
    inference(subsumption_resolution,[],[f84,f1005])).

fof(f1005,plain,
    ( ~ v1_funct_1(sK4)
    | spl7_47 ),
    inference(avatar_component_clause,[],[f1004])).

fof(f1017,plain,(
    spl7_46 ),
    inference(avatar_contradiction_clause,[],[f1016])).

fof(f1016,plain,
    ( $false
    | spl7_46 ),
    inference(subsumption_resolution,[],[f80,f1002])).

fof(f1002,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | spl7_46 ),
    inference(avatar_component_clause,[],[f1001])).

fof(f907,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f900])).

fof(f900,plain,
    ( $false
    | spl7_1 ),
    inference(subsumption_resolution,[],[f794,f897])).

fof(f794,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | spl7_1 ),
    inference(backward_demodulation,[],[f330,f768])).

fof(f330,plain,
    ( k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | spl7_1 ),
    inference(superposition,[],[f324,f182])).

fof(f324,plain,
    ( k2_partfun1(sK3,sK1,sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | spl7_1 ),
    inference(backward_demodulation,[],[f228,f146])).

fof(f228,plain,
    ( k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3)))
    | spl7_1 ),
    inference(backward_demodulation,[],[f207,f161])).

fof(f207,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | spl7_1 ),
    inference(backward_demodulation,[],[f136,f149])).

fof(f136,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl7_1 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl7_1
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f572,plain,(
    spl7_20 ),
    inference(avatar_contradiction_clause,[],[f571])).

fof(f571,plain,
    ( $false
    | spl7_20 ),
    inference(subsumption_resolution,[],[f86,f566])).

fof(f566,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | spl7_20 ),
    inference(avatar_component_clause,[],[f565])).

fof(f143,plain,
    ( ~ spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(avatar_split_clause,[],[f90,f141,f138,f135])).

fof(f90,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:22:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.56  % (817)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.56  % (818)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.27/0.57  % (836)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.27/0.57  % (821)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.58  % (820)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.27/0.58  % (833)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.27/0.58  % (825)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.27/0.58  % (826)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.70/0.59  % (822)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.70/0.59  % (833)Refutation not found, incomplete strategy% (833)------------------------------
% 1.70/0.59  % (833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.61  % (827)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.70/0.61  % (833)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.61  
% 1.70/0.61  % (833)Memory used [KB]: 10746
% 1.70/0.61  % (833)Time elapsed: 0.148 s
% 1.70/0.61  % (833)------------------------------
% 1.70/0.61  % (833)------------------------------
% 1.70/0.61  % (839)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.70/0.61  % (841)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.70/0.61  % (815)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.70/0.61  % (837)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.70/0.62  % (829)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.70/0.62  % (823)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.70/0.62  % (828)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.70/0.62  % (831)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.70/0.62  % (842)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.70/0.62  % (835)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.70/0.62  % (824)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.70/0.62  % (838)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.70/0.62  % (834)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.70/0.62  % (845)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.70/0.63  % (832)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.70/0.63  % (819)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.70/0.63  % (830)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.70/0.63  % (844)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.70/0.63  % (843)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.70/0.63  % (840)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.70/0.64  % (826)Refutation not found, incomplete strategy% (826)------------------------------
% 1.70/0.64  % (826)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.70/0.64  % (826)Termination reason: Refutation not found, incomplete strategy
% 1.70/0.64  
% 1.70/0.64  % (826)Memory used [KB]: 11513
% 1.70/0.64  % (826)Time elapsed: 0.184 s
% 1.70/0.64  % (826)------------------------------
% 1.70/0.64  % (826)------------------------------
% 2.38/0.68  % (818)Refutation found. Thanks to Tanya!
% 2.38/0.68  % SZS status Theorem for theBenchmark
% 2.38/0.68  % SZS output start Proof for theBenchmark
% 2.38/0.68  fof(f1137,plain,(
% 2.38/0.68    $false),
% 2.38/0.68    inference(avatar_sat_refutation,[],[f143,f572,f907,f1017,f1026,f1032,f1060,f1079,f1087,f1089,f1097,f1099,f1115,f1127,f1130,f1133,f1136])).
% 2.38/0.68  fof(f1136,plain,(
% 2.38/0.68    ~spl7_49),
% 2.38/0.68    inference(avatar_contradiction_clause,[],[f1135])).
% 2.38/0.68  fof(f1135,plain,(
% 2.38/0.68    $false | ~spl7_49),
% 2.38/0.68    inference(subsumption_resolution,[],[f81,f1041])).
% 2.38/0.68  fof(f1041,plain,(
% 2.38/0.68    v1_xboole_0(sK3) | ~spl7_49),
% 2.38/0.68    inference(avatar_component_clause,[],[f1040])).
% 2.38/0.68  fof(f1040,plain,(
% 2.38/0.68    spl7_49 <=> v1_xboole_0(sK3)),
% 2.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_49])])).
% 2.38/0.68  fof(f81,plain,(
% 2.38/0.68    ~v1_xboole_0(sK3)),
% 2.38/0.68    inference(cnf_transformation,[],[f67])).
% 2.38/0.68  fof(f67,plain,(
% 2.38/0.68    ((((((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 2.38/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f30,f66,f65,f64,f63,f62,f61])).
% 2.38/0.68  fof(f61,plain,(
% 2.38/0.68    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f62,plain,(
% 2.38/0.68    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f63,plain,(
% 2.38/0.68    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f64,plain,(
% 2.38/0.68    ? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f65,plain,(
% 2.38/0.68    ? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f66,plain,(
% 2.38/0.68    ? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) => ((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f30,plain,(
% 2.38/0.68    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.38/0.68    inference(flattening,[],[f29])).
% 2.38/0.68  fof(f29,plain,(
% 2.38/0.68    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 2.38/0.68    inference(ennf_transformation,[],[f26])).
% 2.38/0.68  fof(f26,negated_conjecture,(
% 2.38/0.68    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.38/0.68    inference(negated_conjecture,[],[f25])).
% 2.38/0.68  fof(f25,conjecture,(
% 2.38/0.68    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 2.38/0.68  fof(f1133,plain,(
% 2.38/0.68    ~spl7_45),
% 2.38/0.68    inference(avatar_contradiction_clause,[],[f1132])).
% 2.38/0.68  fof(f1132,plain,(
% 2.38/0.68    $false | ~spl7_45),
% 2.38/0.68    inference(subsumption_resolution,[],[f79,f999])).
% 2.38/0.68  fof(f999,plain,(
% 2.38/0.68    v1_xboole_0(sK2) | ~spl7_45),
% 2.38/0.68    inference(avatar_component_clause,[],[f998])).
% 2.38/0.68  fof(f998,plain,(
% 2.38/0.68    spl7_45 <=> v1_xboole_0(sK2)),
% 2.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).
% 2.38/0.68  fof(f79,plain,(
% 2.38/0.68    ~v1_xboole_0(sK2)),
% 2.38/0.68    inference(cnf_transformation,[],[f67])).
% 2.38/0.68  fof(f1130,plain,(
% 2.38/0.68    ~spl7_44),
% 2.38/0.68    inference(avatar_contradiction_clause,[],[f1129])).
% 2.38/0.68  fof(f1129,plain,(
% 2.38/0.68    $false | ~spl7_44),
% 2.38/0.68    inference(subsumption_resolution,[],[f78,f996])).
% 2.38/0.68  fof(f996,plain,(
% 2.38/0.68    v1_xboole_0(sK1) | ~spl7_44),
% 2.38/0.68    inference(avatar_component_clause,[],[f995])).
% 2.38/0.68  fof(f995,plain,(
% 2.38/0.68    spl7_44 <=> v1_xboole_0(sK1)),
% 2.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).
% 2.38/0.68  fof(f78,plain,(
% 2.38/0.68    ~v1_xboole_0(sK1)),
% 2.38/0.68    inference(cnf_transformation,[],[f67])).
% 2.38/0.68  fof(f1127,plain,(
% 2.38/0.68    ~spl7_43),
% 2.38/0.68    inference(avatar_contradiction_clause,[],[f1126])).
% 2.38/0.68  fof(f1126,plain,(
% 2.38/0.68    $false | ~spl7_43),
% 2.38/0.68    inference(subsumption_resolution,[],[f77,f993])).
% 2.38/0.68  fof(f993,plain,(
% 2.38/0.68    v1_xboole_0(sK0) | ~spl7_43),
% 2.38/0.68    inference(avatar_component_clause,[],[f992])).
% 2.38/0.68  fof(f992,plain,(
% 2.38/0.68    spl7_43 <=> v1_xboole_0(sK0)),
% 2.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_43])])).
% 2.38/0.68  fof(f77,plain,(
% 2.38/0.68    ~v1_xboole_0(sK0)),
% 2.38/0.68    inference(cnf_transformation,[],[f67])).
% 2.38/0.68  fof(f1115,plain,(
% 2.38/0.68    spl7_43 | spl7_44 | spl7_45 | ~spl7_46 | spl7_49 | ~spl7_50 | ~spl7_47 | ~spl7_48 | ~spl7_20 | ~spl7_51 | ~spl7_52 | ~spl7_53 | spl7_42),
% 2.38/0.68    inference(avatar_split_clause,[],[f1114,f916,f1052,f1049,f1046,f565,f1007,f1004,f1043,f1040,f1001,f998,f995,f992])).
% 2.38/0.68  fof(f1001,plain,(
% 2.38/0.68    spl7_46 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_46])])).
% 2.38/0.68  fof(f1043,plain,(
% 2.38/0.68    spl7_50 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_50])])).
% 2.38/0.68  fof(f1004,plain,(
% 2.38/0.68    spl7_47 <=> v1_funct_1(sK4)),
% 2.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_47])])).
% 2.38/0.68  fof(f1007,plain,(
% 2.38/0.68    spl7_48 <=> v1_funct_2(sK4,sK2,sK1)),
% 2.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).
% 2.38/0.68  fof(f565,plain,(
% 2.38/0.68    spl7_20 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).
% 2.38/0.68  fof(f1046,plain,(
% 2.38/0.68    spl7_51 <=> v1_funct_1(sK5)),
% 2.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_51])])).
% 2.38/0.68  fof(f1049,plain,(
% 2.38/0.68    spl7_52 <=> v1_funct_2(sK5,sK3,sK1)),
% 2.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_52])])).
% 2.38/0.68  fof(f1052,plain,(
% 2.38/0.68    spl7_53 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_53])])).
% 2.38/0.68  fof(f916,plain,(
% 2.38/0.68    spl7_42 <=> v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 2.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_42])])).
% 2.38/0.68  fof(f1114,plain,(
% 2.38/0.68    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl7_42),
% 2.38/0.68    inference(resolution,[],[f917,f124])).
% 2.38/0.68  fof(f124,plain,(
% 2.38/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.38/0.68    inference(cnf_transformation,[],[f60])).
% 2.38/0.68  fof(f60,plain,(
% 2.38/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.38/0.68    inference(flattening,[],[f59])).
% 2.38/0.68  fof(f59,plain,(
% 2.38/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.38/0.68    inference(ennf_transformation,[],[f24])).
% 2.38/0.68  fof(f24,axiom,(
% 2.38/0.68    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 2.38/0.68  fof(f917,plain,(
% 2.38/0.68    ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | spl7_42),
% 2.38/0.68    inference(avatar_component_clause,[],[f916])).
% 2.38/0.68  fof(f1099,plain,(
% 2.38/0.68    spl7_53),
% 2.38/0.68    inference(avatar_contradiction_clause,[],[f1098])).
% 2.38/0.68  fof(f1098,plain,(
% 2.38/0.68    $false | spl7_53),
% 2.38/0.68    inference(subsumption_resolution,[],[f89,f1053])).
% 2.38/0.68  fof(f1053,plain,(
% 2.38/0.68    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | spl7_53),
% 2.38/0.68    inference(avatar_component_clause,[],[f1052])).
% 2.38/0.68  fof(f89,plain,(
% 2.38/0.68    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 2.38/0.68    inference(cnf_transformation,[],[f67])).
% 2.38/0.68  fof(f1097,plain,(
% 2.38/0.68    spl7_3 | ~spl7_42),
% 2.38/0.68    inference(avatar_split_clause,[],[f1096,f916,f141])).
% 2.38/0.68  fof(f141,plain,(
% 2.38/0.68    spl7_3 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.38/0.68    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.38/0.68  fof(f1096,plain,(
% 2.38/0.68    ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 2.38/0.68    inference(global_subsumption,[],[f77,f78,f89,f86,f353,f80,f84,f85,f82,f87,f88,f1095])).
% 2.38/0.68  fof(f1095,plain,(
% 2.38/0.68    ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 2.38/0.68    inference(trivial_inequality_removal,[],[f1094])).
% 2.38/0.68  fof(f1094,plain,(
% 2.38/0.68    k1_xboole_0 != k1_xboole_0 | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 2.38/0.68    inference(forward_demodulation,[],[f1093,f768])).
% 2.38/0.68  fof(f768,plain,(
% 2.38/0.68    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 2.38/0.68    inference(forward_demodulation,[],[f767,f452])).
% 2.38/0.68  fof(f452,plain,(
% 2.38/0.68    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_xboole_0)),
% 2.38/0.68    inference(forward_demodulation,[],[f449,f91])).
% 2.38/0.68  fof(f91,plain,(
% 2.38/0.68    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.38/0.68    inference(cnf_transformation,[],[f12])).
% 2.38/0.68  fof(f12,axiom,(
% 2.38/0.68    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 2.38/0.68  fof(f449,plain,(
% 2.38/0.68    k1_xboole_0 = k7_relat_1(k1_xboole_0,k1_relat_1(k1_xboole_0))),
% 2.38/0.68    inference(resolution,[],[f431,f96])).
% 2.38/0.68  fof(f96,plain,(
% 2.38/0.68    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 2.38/0.68    inference(cnf_transformation,[],[f33])).
% 2.38/0.68  fof(f33,plain,(
% 2.38/0.68    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.38/0.68    inference(ennf_transformation,[],[f15])).
% 2.38/0.68  fof(f15,axiom,(
% 2.38/0.68    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 2.38/0.68    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 2.38/0.68  fof(f431,plain,(
% 2.38/0.68    v1_relat_1(k1_xboole_0)),
% 2.38/0.68    inference(global_subsumption,[],[f155,f428])).
% 2.38/0.68  fof(f428,plain,(
% 2.38/0.68    v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK4)),
% 2.38/0.68    inference(superposition,[],[f107,f403])).
% 2.38/0.68  fof(f403,plain,(
% 2.38/0.68    k1_xboole_0 = k7_relat_1(sK4,sK6(sK2))),
% 2.38/0.68    inference(global_subsumption,[],[f220,f339,f402])).
% 2.38/0.68  fof(f402,plain,(
% 2.38/0.68    k1_xboole_0 = k7_relat_1(sK4,sK6(sK2)) | k1_xboole_0 = sK2),
% 2.38/0.68    inference(resolution,[],[f219,f102])).
% 2.38/0.68  fof(f102,plain,(
% 2.38/0.68    ( ! [X0] : (r1_xboole_0(sK6(X0),X0) | k1_xboole_0 = X0) )),
% 2.38/0.68    inference(cnf_transformation,[],[f72])).
% 2.38/0.68  fof(f72,plain,(
% 2.38/0.68    ! [X0] : (r1_xboole_0(sK6(X0),X0) | k1_xboole_0 = X0)),
% 2.38/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f38,f71])).
% 2.38/0.68  fof(f71,plain,(
% 2.38/0.68    ! [X0] : (? [X1] : r1_xboole_0(X1,X0) => r1_xboole_0(sK6(X0),X0))),
% 2.38/0.68    introduced(choice_axiom,[])).
% 2.38/0.68  fof(f38,plain,(
% 2.38/0.68    ! [X0] : (? [X1] : r1_xboole_0(X1,X0) | k1_xboole_0 = X0)),
% 2.38/0.68    inference(ennf_transformation,[],[f27])).
% 2.38/0.68  fof(f27,plain,(
% 2.38/0.68    ! [X0] : ~(! [X1] : ~r1_xboole_0(X1,X0) & k1_xboole_0 != X0)),
% 2.38/0.68    inference(pure_predicate_removal,[],[f19])).
% 2.38/0.69  fof(f19,axiom,(
% 2.38/0.69    ! [X0] : ~(! [X1] : ~(r1_xboole_0(X1,X0) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).
% 2.38/0.69  fof(f219,plain,(
% 2.38/0.69    ( ! [X1] : (~r1_xboole_0(X1,sK2) | k1_xboole_0 = k7_relat_1(sK4,X1)) )),
% 2.38/0.69    inference(global_subsumption,[],[f155,f216])).
% 2.38/0.69  fof(f216,plain,(
% 2.38/0.69    ( ! [X1] : (~r1_xboole_0(X1,sK2) | k1_xboole_0 = k7_relat_1(sK4,X1) | ~v1_relat_1(sK4)) )),
% 2.38/0.69    inference(superposition,[],[f100,f196])).
% 2.38/0.69  fof(f196,plain,(
% 2.38/0.69    sK2 = k1_relat_1(sK4)),
% 2.38/0.69    inference(global_subsumption,[],[f155,f154,f195])).
% 2.38/0.69  fof(f195,plain,(
% 2.38/0.69    sK2 = k1_relat_1(sK4) | ~v4_relat_1(sK4,sK2) | ~v1_relat_1(sK4)),
% 2.38/0.69    inference(resolution,[],[f162,f114])).
% 2.38/0.69  fof(f114,plain,(
% 2.38/0.69    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f75])).
% 2.38/0.69  fof(f75,plain,(
% 2.38/0.69    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.38/0.69    inference(nnf_transformation,[],[f51])).
% 2.38/0.69  fof(f51,plain,(
% 2.38/0.69    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.38/0.69    inference(flattening,[],[f50])).
% 2.38/0.69  fof(f50,plain,(
% 2.38/0.69    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.38/0.69    inference(ennf_transformation,[],[f21])).
% 2.38/0.69  fof(f21,axiom,(
% 2.38/0.69    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 2.38/0.69  fof(f162,plain,(
% 2.38/0.69    v1_partfun1(sK4,sK2)),
% 2.38/0.69    inference(global_subsumption,[],[f78,f84,f85,f156])).
% 2.38/0.69  fof(f156,plain,(
% 2.38/0.69    ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_partfun1(sK4,sK2) | v1_xboole_0(sK1)),
% 2.38/0.69    inference(resolution,[],[f86,f106])).
% 2.38/0.69  fof(f106,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | v1_partfun1(X2,X0) | v1_xboole_0(X1)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f42])).
% 2.38/0.69  fof(f42,plain,(
% 2.38/0.69    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.38/0.69    inference(flattening,[],[f41])).
% 2.38/0.69  fof(f41,plain,(
% 2.38/0.69    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.38/0.69    inference(ennf_transformation,[],[f20])).
% 2.38/0.69  fof(f20,axiom,(
% 2.38/0.69    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 2.38/0.69  fof(f154,plain,(
% 2.38/0.69    v4_relat_1(sK4,sK2)),
% 2.38/0.69    inference(resolution,[],[f86,f121])).
% 2.38/0.69  fof(f121,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f56])).
% 2.38/0.69  fof(f56,plain,(
% 2.38/0.69    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.38/0.69    inference(ennf_transformation,[],[f28])).
% 2.38/0.69  fof(f28,plain,(
% 2.38/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.38/0.69    inference(pure_predicate_removal,[],[f18])).
% 2.38/0.69  fof(f18,axiom,(
% 2.38/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.38/0.69  fof(f100,plain,(
% 2.38/0.69    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | k1_xboole_0 = k7_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f36])).
% 2.38/0.69  fof(f36,plain,(
% 2.38/0.69    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.38/0.69    inference(ennf_transformation,[],[f10])).
% 2.38/0.69  fof(f10,axiom,(
% 2.38/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 2.38/0.69  fof(f339,plain,(
% 2.38/0.69    k1_xboole_0 != k2_relat_1(sK4)),
% 2.38/0.69    inference(global_subsumption,[],[f155,f329,f338])).
% 2.38/0.69  fof(f338,plain,(
% 2.38/0.69    r1_xboole_0(sK2,sK2) | k1_xboole_0 != k2_relat_1(sK4) | ~v1_relat_1(sK4)),
% 2.38/0.69    inference(forward_demodulation,[],[f337,f196])).
% 2.38/0.69  fof(f337,plain,(
% 2.38/0.69    k1_xboole_0 != k2_relat_1(sK4) | r1_xboole_0(k1_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 2.38/0.69    inference(superposition,[],[f109,f336])).
% 2.38/0.69  fof(f336,plain,(
% 2.38/0.69    k2_relat_1(sK4) = k9_relat_1(sK4,sK2)),
% 2.38/0.69    inference(forward_demodulation,[],[f170,f196])).
% 2.38/0.69  fof(f170,plain,(
% 2.38/0.69    k9_relat_1(sK4,k1_relat_1(sK4)) = k2_relat_1(sK4)),
% 2.38/0.69    inference(resolution,[],[f155,f97])).
% 2.38/0.69  fof(f97,plain,(
% 2.38/0.69    ( ! [X0] : (~v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f34])).
% 2.38/0.69  fof(f34,plain,(
% 2.38/0.69    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.38/0.69    inference(ennf_transformation,[],[f8])).
% 2.38/0.69  fof(f8,axiom,(
% 2.38/0.69    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 2.38/0.69  fof(f109,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k1_xboole_0 != k9_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f73])).
% 2.38/0.69  fof(f73,plain,(
% 2.38/0.69    ! [X0,X1] : (((k1_xboole_0 = k9_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.38/0.69    inference(nnf_transformation,[],[f45])).
% 2.38/0.69  fof(f45,plain,(
% 2.38/0.69    ! [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.38/0.69    inference(ennf_transformation,[],[f9])).
% 2.38/0.69  fof(f9,axiom,(
% 2.38/0.69    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).
% 2.38/0.69  fof(f329,plain,(
% 2.38/0.69    ~r1_xboole_0(sK2,sK2)),
% 2.38/0.69    inference(global_subsumption,[],[f79,f328])).
% 2.38/0.69  fof(f328,plain,(
% 2.38/0.69    ~r1_xboole_0(sK2,sK2) | v1_xboole_0(sK2)),
% 2.38/0.69    inference(resolution,[],[f319,f104])).
% 2.38/0.69  fof(f104,plain,(
% 2.38/0.69    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_xboole_0(X1,X0) | v1_xboole_0(X1)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f40])).
% 2.38/0.69  fof(f40,plain,(
% 2.38/0.69    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 2.38/0.69    inference(flattening,[],[f39])).
% 2.38/0.69  fof(f39,plain,(
% 2.38/0.69    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 2.38/0.69    inference(ennf_transformation,[],[f2])).
% 2.38/0.69  fof(f2,axiom,(
% 2.38/0.69    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 2.38/0.69  fof(f319,plain,(
% 2.38/0.69    r1_tarski(sK2,sK2)),
% 2.38/0.69    inference(global_subsumption,[],[f155,f318])).
% 2.38/0.69  fof(f318,plain,(
% 2.38/0.69    r1_tarski(sK2,sK2) | ~v1_relat_1(sK4)),
% 2.38/0.69    inference(forward_demodulation,[],[f316,f196])).
% 2.38/0.69  fof(f316,plain,(
% 2.38/0.69    r1_tarski(k1_relat_1(sK4),sK2) | ~v1_relat_1(sK4)),
% 2.38/0.69    inference(superposition,[],[f108,f194])).
% 2.38/0.69  fof(f194,plain,(
% 2.38/0.69    sK4 = k7_relat_1(sK4,sK2)),
% 2.38/0.69    inference(global_subsumption,[],[f155,f193])).
% 2.38/0.69  fof(f193,plain,(
% 2.38/0.69    sK4 = k7_relat_1(sK4,sK2) | ~v1_relat_1(sK4)),
% 2.38/0.69    inference(resolution,[],[f154,f113])).
% 2.38/0.69  fof(f113,plain,(
% 2.38/0.69    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f49])).
% 2.38/0.69  fof(f49,plain,(
% 2.38/0.69    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.38/0.69    inference(flattening,[],[f48])).
% 2.38/0.69  fof(f48,plain,(
% 2.38/0.69    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.38/0.69    inference(ennf_transformation,[],[f11])).
% 2.38/0.69  fof(f11,axiom,(
% 2.38/0.69    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).
% 2.38/0.69  fof(f108,plain,(
% 2.38/0.69    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f44])).
% 2.38/0.69  fof(f44,plain,(
% 2.38/0.69    ! [X0,X1] : (r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0) | ~v1_relat_1(X1))),
% 2.38/0.69    inference(ennf_transformation,[],[f14])).
% 2.38/0.69  fof(f14,axiom,(
% 2.38/0.69    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k7_relat_1(X1,X0)),X0))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).
% 2.38/0.69  fof(f220,plain,(
% 2.38/0.69    k1_xboole_0 != sK2 | k1_xboole_0 = k2_relat_1(sK4)),
% 2.38/0.69    inference(global_subsumption,[],[f155,f217])).
% 2.38/0.69  fof(f217,plain,(
% 2.38/0.69    k1_xboole_0 != sK2 | k1_xboole_0 = k2_relat_1(sK4) | ~v1_relat_1(sK4)),
% 2.38/0.69    inference(superposition,[],[f98,f196])).
% 2.38/0.69  fof(f98,plain,(
% 2.38/0.69    ( ! [X0] : (k1_xboole_0 != k1_relat_1(X0) | k1_xboole_0 = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f70])).
% 2.38/0.69  fof(f70,plain,(
% 2.38/0.69    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.38/0.69    inference(nnf_transformation,[],[f35])).
% 2.38/0.69  fof(f35,plain,(
% 2.38/0.69    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.38/0.69    inference(ennf_transformation,[],[f13])).
% 2.38/0.69  fof(f13,axiom,(
% 2.38/0.69    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).
% 2.38/0.69  fof(f107,plain,(
% 2.38/0.69    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f43])).
% 2.38/0.69  fof(f43,plain,(
% 2.38/0.69    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.38/0.69    inference(ennf_transformation,[],[f6])).
% 2.38/0.69  fof(f6,axiom,(
% 2.38/0.69    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 2.38/0.69  fof(f155,plain,(
% 2.38/0.69    v1_relat_1(sK4)),
% 2.38/0.69    inference(resolution,[],[f86,f120])).
% 2.38/0.69  fof(f120,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f55])).
% 2.38/0.69  fof(f55,plain,(
% 2.38/0.69    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.38/0.69    inference(ennf_transformation,[],[f17])).
% 2.38/0.69  fof(f17,axiom,(
% 2.38/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.38/0.69  fof(f767,plain,(
% 2.38/0.69    k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(k1_xboole_0,k1_xboole_0)),
% 2.38/0.69    inference(forward_demodulation,[],[f766,f588])).
% 2.38/0.69  fof(f588,plain,(
% 2.38/0.69    k1_xboole_0 = k7_relat_1(sK5,sK2)),
% 2.38/0.69    inference(resolution,[],[f251,f145])).
% 2.38/0.69  fof(f145,plain,(
% 2.38/0.69    r1_xboole_0(sK2,sK3)),
% 2.38/0.69    inference(global_subsumption,[],[f79,f81,f144])).
% 2.38/0.69  fof(f144,plain,(
% 2.38/0.69    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2)),
% 2.38/0.69    inference(resolution,[],[f83,f111])).
% 2.38/0.69  fof(f111,plain,(
% 2.38/0.69    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f74])).
% 2.38/0.69  fof(f74,plain,(
% 2.38/0.69    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.38/0.69    inference(nnf_transformation,[],[f47])).
% 2.38/0.69  fof(f47,plain,(
% 2.38/0.69    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 2.38/0.69    inference(flattening,[],[f46])).
% 2.38/0.69  fof(f46,plain,(
% 2.38/0.69    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 2.38/0.69    inference(ennf_transformation,[],[f16])).
% 2.38/0.69  fof(f16,axiom,(
% 2.38/0.69    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 2.38/0.69  fof(f83,plain,(
% 2.38/0.69    r1_subset_1(sK2,sK3)),
% 2.38/0.69    inference(cnf_transformation,[],[f67])).
% 2.38/0.69  fof(f251,plain,(
% 2.38/0.69    ( ! [X1] : (~r1_xboole_0(X1,sK3) | k1_xboole_0 = k7_relat_1(sK5,X1)) )),
% 2.38/0.69    inference(global_subsumption,[],[f176,f248])).
% 2.38/0.69  fof(f248,plain,(
% 2.38/0.69    ( ! [X1] : (~r1_xboole_0(X1,sK3) | k1_xboole_0 = k7_relat_1(sK5,X1) | ~v1_relat_1(sK5)) )),
% 2.38/0.69    inference(superposition,[],[f100,f200])).
% 2.38/0.69  fof(f200,plain,(
% 2.38/0.69    sK3 = k1_relat_1(sK5)),
% 2.38/0.69    inference(global_subsumption,[],[f176,f175,f199])).
% 2.38/0.69  fof(f199,plain,(
% 2.38/0.69    sK3 = k1_relat_1(sK5) | ~v4_relat_1(sK5,sK3) | ~v1_relat_1(sK5)),
% 2.38/0.69    inference(resolution,[],[f183,f114])).
% 2.38/0.69  fof(f183,plain,(
% 2.38/0.69    v1_partfun1(sK5,sK3)),
% 2.38/0.69    inference(global_subsumption,[],[f78,f87,f88,f177])).
% 2.38/0.69  fof(f177,plain,(
% 2.38/0.69    ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | v1_partfun1(sK5,sK3) | v1_xboole_0(sK1)),
% 2.38/0.69    inference(resolution,[],[f89,f106])).
% 2.38/0.69  fof(f175,plain,(
% 2.38/0.69    v4_relat_1(sK5,sK3)),
% 2.38/0.69    inference(resolution,[],[f89,f121])).
% 2.38/0.69  fof(f176,plain,(
% 2.38/0.69    v1_relat_1(sK5)),
% 2.38/0.69    inference(resolution,[],[f89,f120])).
% 2.38/0.69  fof(f766,plain,(
% 2.38/0.69    k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(k7_relat_1(sK5,sK2),k1_xboole_0)),
% 2.38/0.69    inference(resolution,[],[f594,f176])).
% 2.38/0.69  fof(f594,plain,(
% 2.38/0.69    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k7_relat_1(k7_relat_1(X0,sK2),k1_xboole_0)) )),
% 2.38/0.69    inference(resolution,[],[f593,f118])).
% 2.38/0.69  fof(f118,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~v1_relat_1(X2)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f53])).
% 2.38/0.69  fof(f53,plain,(
% 2.38/0.69    ! [X0,X1,X2] : (k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1) | ~v1_relat_1(X2))),
% 2.38/0.69    inference(flattening,[],[f52])).
% 2.38/0.69  fof(f52,plain,(
% 2.38/0.69    ! [X0,X1,X2] : ((k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0) | ~r1_tarski(X0,X1)) | ~v1_relat_1(X2))),
% 2.38/0.69    inference(ennf_transformation,[],[f7])).
% 2.38/0.69  fof(f7,axiom,(
% 2.38/0.69    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_tarski(X0,X1) => k7_relat_1(k7_relat_1(X2,X1),X0) = k7_relat_1(X2,X0)))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).
% 2.38/0.69  fof(f593,plain,(
% 2.38/0.69    r1_tarski(k1_xboole_0,sK2)),
% 2.38/0.69    inference(global_subsumption,[],[f176,f592])).
% 2.38/0.69  fof(f592,plain,(
% 2.38/0.69    r1_tarski(k1_xboole_0,sK2) | ~v1_relat_1(sK5)),
% 2.38/0.69    inference(forward_demodulation,[],[f590,f91])).
% 2.38/0.69  fof(f590,plain,(
% 2.38/0.69    r1_tarski(k1_relat_1(k1_xboole_0),sK2) | ~v1_relat_1(sK5)),
% 2.38/0.69    inference(superposition,[],[f108,f588])).
% 2.38/0.69  fof(f1093,plain,(
% 2.38/0.69    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 2.38/0.69    inference(forward_demodulation,[],[f1092,f182])).
% 2.38/0.69  fof(f182,plain,(
% 2.38/0.69    ( ! [X6] : (k2_partfun1(sK3,sK1,sK5,X6) = k7_relat_1(sK5,X6)) )),
% 2.38/0.69    inference(global_subsumption,[],[f87,f174])).
% 2.38/0.69  fof(f174,plain,(
% 2.38/0.69    ( ! [X6] : (k2_partfun1(sK3,sK1,sK5,X6) = k7_relat_1(sK5,X6) | ~v1_funct_1(sK5)) )),
% 2.38/0.69    inference(resolution,[],[f89,f122])).
% 2.38/0.69  fof(f122,plain,(
% 2.38/0.69    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f58])).
% 2.38/0.69  fof(f58,plain,(
% 2.38/0.69    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.38/0.69    inference(flattening,[],[f57])).
% 2.38/0.69  fof(f57,plain,(
% 2.38/0.69    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.38/0.69    inference(ennf_transformation,[],[f22])).
% 2.38/0.69  fof(f22,axiom,(
% 2.38/0.69    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 2.38/0.69  fof(f1092,plain,(
% 2.38/0.69    k1_xboole_0 != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 2.38/0.69    inference(forward_demodulation,[],[f1091,f897])).
% 2.38/0.69  fof(f897,plain,(
% 2.38/0.69    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 2.38/0.69    inference(forward_demodulation,[],[f896,f452])).
% 2.38/0.69  fof(f896,plain,(
% 2.38/0.69    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k1_xboole_0,k1_xboole_0)),
% 2.38/0.69    inference(forward_demodulation,[],[f893,f403])).
% 2.38/0.69  fof(f893,plain,(
% 2.38/0.69    k7_relat_1(sK4,k1_xboole_0) = k7_relat_1(k7_relat_1(sK4,sK6(sK2)),k1_xboole_0)),
% 2.38/0.69    inference(resolution,[],[f470,f155])).
% 2.38/0.69  fof(f470,plain,(
% 2.38/0.69    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(k7_relat_1(X0,sK6(sK2)),k1_xboole_0) = k7_relat_1(X0,k1_xboole_0)) )),
% 2.38/0.69    inference(resolution,[],[f430,f118])).
% 2.38/0.69  fof(f430,plain,(
% 2.38/0.69    r1_tarski(k1_xboole_0,sK6(sK2))),
% 2.38/0.69    inference(global_subsumption,[],[f155,f429])).
% 2.38/0.69  fof(f429,plain,(
% 2.38/0.69    r1_tarski(k1_xboole_0,sK6(sK2)) | ~v1_relat_1(sK4)),
% 2.38/0.69    inference(forward_demodulation,[],[f427,f91])).
% 2.38/0.69  fof(f427,plain,(
% 2.38/0.69    r1_tarski(k1_relat_1(k1_xboole_0),sK6(sK2)) | ~v1_relat_1(sK4)),
% 2.38/0.69    inference(superposition,[],[f108,f403])).
% 2.38/0.69  fof(f1091,plain,(
% 2.38/0.69    k2_partfun1(sK3,sK1,sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 2.38/0.69    inference(forward_demodulation,[],[f1090,f161])).
% 2.38/0.69  fof(f161,plain,(
% 2.38/0.69    ( ! [X6] : (k2_partfun1(sK2,sK1,sK4,X6) = k7_relat_1(sK4,X6)) )),
% 2.38/0.69    inference(global_subsumption,[],[f84,f153])).
% 2.38/0.69  fof(f153,plain,(
% 2.38/0.69    ( ! [X6] : (k2_partfun1(sK2,sK1,sK4,X6) = k7_relat_1(sK4,X6) | ~v1_funct_1(sK4)) )),
% 2.38/0.69    inference(resolution,[],[f86,f122])).
% 2.38/0.69  fof(f1090,plain,(
% 2.38/0.69    k2_partfun1(sK3,sK1,sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 2.38/0.69    inference(resolution,[],[f544,f314])).
% 2.38/0.69  fof(f314,plain,(
% 2.38/0.69    ( ! [X0] : (m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 2.38/0.69    inference(global_subsumption,[],[f79,f84,f85,f311])).
% 2.38/0.69  fof(f311,plain,(
% 2.38/0.69    ( ! [X0] : (m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 2.38/0.69    inference(resolution,[],[f181,f86])).
% 2.38/0.69  fof(f181,plain,(
% 2.38/0.69    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(X3)) )),
% 2.38/0.69    inference(global_subsumption,[],[f78,f81,f87,f88,f173])).
% 2.38/0.69  fof(f173,plain,(
% 2.38/0.69    ( ! [X4,X5,X3] : (m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 2.38/0.69    inference(resolution,[],[f89,f125])).
% 2.38/0.69  fof(f125,plain,(
% 2.38/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f60])).
% 2.38/0.69  fof(f544,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0))) | k2_partfun1(sK2,X0,X1,k1_xboole_0) != k2_partfun1(sK3,X0,X2,k1_xboole_0) | ~v1_funct_2(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k4_subset_1(sK0,sK2,sK3),X0) | ~v1_funct_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2)) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | ~v1_funct_2(X2,sK3,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_2(X1,sK2,X0) | ~v1_funct_1(X1) | v1_xboole_0(X0)) )),
% 2.38/0.69    inference(global_subsumption,[],[f79,f80,f539])).
% 2.38/0.69  fof(f539,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (k2_partfun1(sK2,X0,X1,k1_xboole_0) != k2_partfun1(sK3,X0,X2,k1_xboole_0) | ~m1_subset_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0))) | ~v1_funct_2(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k4_subset_1(sK0,sK2,sK3),X0) | ~v1_funct_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2)) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK3) = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | ~v1_funct_2(X2,sK3,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_2(X1,sK2,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 2.38/0.69    inference(superposition,[],[f212,f146])).
% 2.38/0.69  fof(f146,plain,(
% 2.38/0.69    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 2.38/0.69    inference(resolution,[],[f145,f127])).
% 2.38/0.69  fof(f127,plain,(
% 2.38/0.69    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.38/0.69    inference(definition_unfolding,[],[f116,f103])).
% 2.38/0.69  fof(f103,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 2.38/0.69    inference(cnf_transformation,[],[f5])).
% 2.38/0.69  fof(f5,axiom,(
% 2.38/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 2.38/0.69  fof(f116,plain,(
% 2.38/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f76])).
% 2.38/0.69  fof(f76,plain,(
% 2.38/0.69    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.38/0.69    inference(nnf_transformation,[],[f1])).
% 2.38/0.69  fof(f1,axiom,(
% 2.38/0.69    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 2.38/0.69  fof(f212,plain,(
% 2.38/0.69    ( ! [X6,X4,X7,X5] : (k2_partfun1(X4,X5,X6,k1_setfam_1(k2_tarski(X4,sK3))) != k2_partfun1(sK3,X5,X7,k1_setfam_1(k2_tarski(X4,sK3))) | ~m1_subset_1(k1_tmap_1(sK0,X5,X4,sK3,X6,X7),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,X4,sK3),X5))) | ~v1_funct_2(k1_tmap_1(sK0,X5,X4,sK3,X6,X7),k4_subset_1(sK0,X4,sK3),X5) | ~v1_funct_1(k1_tmap_1(sK0,X5,X4,sK3,X6,X7)) | k2_partfun1(k4_subset_1(sK0,X4,sK3),X5,k1_tmap_1(sK0,X5,X4,sK3,X6,X7),sK3) = X7 | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK3,X5))) | ~v1_funct_2(X7,sK3,X5) | ~v1_funct_1(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(X6,X4,X5) | ~v1_funct_1(X6) | ~m1_subset_1(X4,k1_zfmisc_1(sK0)) | v1_xboole_0(X4) | v1_xboole_0(X5)) )),
% 2.38/0.69    inference(global_subsumption,[],[f77,f81,f82,f209])).
% 2.38/0.69  fof(f209,plain,(
% 2.38/0.69    ( ! [X6,X4,X7,X5] : (k2_partfun1(X4,X5,X6,k1_setfam_1(k2_tarski(X4,sK3))) != k2_partfun1(sK3,X5,X7,k1_setfam_1(k2_tarski(X4,sK3))) | ~m1_subset_1(k1_tmap_1(sK0,X5,X4,sK3,X6,X7),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,X4,sK3),X5))) | ~v1_funct_2(k1_tmap_1(sK0,X5,X4,sK3,X6,X7),k4_subset_1(sK0,X4,sK3),X5) | ~v1_funct_1(k1_tmap_1(sK0,X5,X4,sK3,X6,X7)) | k2_partfun1(k4_subset_1(sK0,X4,sK3),X5,k1_tmap_1(sK0,X5,X4,sK3,X6,X7),sK3) = X7 | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(sK3,X5))) | ~v1_funct_2(X7,sK3,X5) | ~v1_funct_1(X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) | ~v1_funct_2(X6,X4,X5) | ~v1_funct_1(X6) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(sK0)) | v1_xboole_0(X4) | v1_xboole_0(X5) | v1_xboole_0(sK0)) )),
% 2.38/0.69    inference(superposition,[],[f131,f149])).
% 2.38/0.69  fof(f149,plain,(
% 2.38/0.69    ( ! [X0] : (k9_subset_1(sK0,X0,sK3) = k1_setfam_1(k2_tarski(X0,sK3))) )),
% 2.38/0.69    inference(resolution,[],[f82,f128])).
% 2.38/0.69  fof(f128,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))) )),
% 2.38/0.69    inference(definition_unfolding,[],[f119,f103])).
% 2.38/0.69  fof(f119,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.38/0.69    inference(cnf_transformation,[],[f54])).
% 2.38/0.69  fof(f54,plain,(
% 2.38/0.69    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.38/0.69    inference(ennf_transformation,[],[f3])).
% 2.38/0.69  fof(f3,axiom,(
% 2.38/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 2.38/0.69  fof(f131,plain,(
% 2.38/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.38/0.69    inference(equality_resolution,[],[f94])).
% 2.38/0.69  fof(f94,plain,(
% 2.38/0.69    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f69])).
% 2.38/0.69  fof(f69,plain,(
% 2.38/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.38/0.69    inference(flattening,[],[f68])).
% 2.38/0.69  fof(f68,plain,(
% 2.38/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.38/0.69    inference(nnf_transformation,[],[f32])).
% 2.38/0.69  fof(f32,plain,(
% 2.38/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.38/0.69    inference(flattening,[],[f31])).
% 2.38/0.69  fof(f31,plain,(
% 2.38/0.69    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 2.38/0.69    inference(ennf_transformation,[],[f23])).
% 2.38/0.69  fof(f23,axiom,(
% 2.38/0.69    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 2.38/0.69    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 2.38/0.69  fof(f88,plain,(
% 2.38/0.69    v1_funct_2(sK5,sK3,sK1)),
% 2.38/0.69    inference(cnf_transformation,[],[f67])).
% 2.38/0.69  fof(f87,plain,(
% 2.38/0.69    v1_funct_1(sK5)),
% 2.38/0.69    inference(cnf_transformation,[],[f67])).
% 2.38/0.69  fof(f82,plain,(
% 2.38/0.69    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 2.38/0.69    inference(cnf_transformation,[],[f67])).
% 2.38/0.69  fof(f85,plain,(
% 2.38/0.69    v1_funct_2(sK4,sK2,sK1)),
% 2.38/0.69    inference(cnf_transformation,[],[f67])).
% 2.38/0.69  fof(f84,plain,(
% 2.38/0.69    v1_funct_1(sK4)),
% 2.38/0.69    inference(cnf_transformation,[],[f67])).
% 2.38/0.69  fof(f80,plain,(
% 2.38/0.69    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 2.38/0.69    inference(cnf_transformation,[],[f67])).
% 2.38/0.69  fof(f353,plain,(
% 2.38/0.69    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 2.38/0.69    inference(global_subsumption,[],[f77,f80,f352])).
% 2.38/0.69  fof(f352,plain,(
% 2.38/0.69    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 2.38/0.69    inference(resolution,[],[f304,f82])).
% 2.38/0.69  fof(f304,plain,(
% 2.38/0.69    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 2.38/0.69    inference(global_subsumption,[],[f79,f84,f85,f301])).
% 2.38/0.69  fof(f301,plain,(
% 2.38/0.69    ( ! [X0] : (v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 2.38/0.69    inference(resolution,[],[f180,f86])).
% 2.38/0.69  fof(f180,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | v1_funct_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5)) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.38/0.69    inference(global_subsumption,[],[f78,f81,f87,f88,f172])).
% 2.38/0.69  fof(f172,plain,(
% 2.38/0.69    ( ! [X2,X0,X1] : (v1_funct_1(k1_tmap_1(X0,sK1,X1,sK3,X2,sK5)) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,sK1))) | ~v1_funct_2(X2,X1,sK1) | ~v1_funct_1(X2) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | v1_xboole_0(sK3) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X1) | v1_xboole_0(sK1) | v1_xboole_0(X0)) )),
% 2.38/0.69    inference(resolution,[],[f89,f123])).
% 2.38/0.69  fof(f123,plain,(
% 2.38/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.38/0.69    inference(cnf_transformation,[],[f60])).
% 2.38/0.69  fof(f86,plain,(
% 2.38/0.69    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 2.38/0.69    inference(cnf_transformation,[],[f67])).
% 2.38/0.69  fof(f1089,plain,(
% 2.38/0.69    spl7_52),
% 2.38/0.69    inference(avatar_contradiction_clause,[],[f1088])).
% 2.38/0.69  fof(f1088,plain,(
% 2.38/0.69    $false | spl7_52),
% 2.38/0.69    inference(subsumption_resolution,[],[f88,f1050])).
% 2.38/0.69  fof(f1050,plain,(
% 2.38/0.69    ~v1_funct_2(sK5,sK3,sK1) | spl7_52),
% 2.38/0.69    inference(avatar_component_clause,[],[f1049])).
% 2.38/0.69  fof(f1087,plain,(
% 2.38/0.69    spl7_2 | ~spl7_42),
% 2.38/0.69    inference(avatar_split_clause,[],[f1086,f916,f138])).
% 2.38/0.69  fof(f138,plain,(
% 2.38/0.69    spl7_2 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 2.38/0.69    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.38/0.70  fof(f1086,plain,(
% 2.38/0.70    ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 2.38/0.70    inference(global_subsumption,[],[f77,f78,f88,f89,f86,f353,f80,f84,f85,f82,f87,f1085])).
% 2.38/0.70  fof(f1085,plain,(
% 2.38/0.70    ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 2.38/0.70    inference(trivial_inequality_removal,[],[f1084])).
% 2.38/0.70  fof(f1084,plain,(
% 2.38/0.70    k1_xboole_0 != k1_xboole_0 | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 2.38/0.70    inference(forward_demodulation,[],[f1083,f768])).
% 2.38/0.70  fof(f1083,plain,(
% 2.38/0.70    k1_xboole_0 != k7_relat_1(sK5,k1_xboole_0) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 2.38/0.70    inference(forward_demodulation,[],[f1082,f182])).
% 2.38/0.70  fof(f1082,plain,(
% 2.38/0.70    k1_xboole_0 != k2_partfun1(sK3,sK1,sK5,k1_xboole_0) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 2.38/0.70    inference(forward_demodulation,[],[f1081,f897])).
% 2.38/0.70  fof(f1081,plain,(
% 2.38/0.70    k2_partfun1(sK3,sK1,sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 2.38/0.70    inference(forward_demodulation,[],[f1080,f161])).
% 2.38/0.70  fof(f1080,plain,(
% 2.38/0.70    k2_partfun1(sK3,sK1,sK5,k1_xboole_0) != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | v1_xboole_0(sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 2.38/0.70    inference(resolution,[],[f534,f314])).
% 2.38/0.70  fof(f534,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0))) | k2_partfun1(sK2,X0,X1,k1_xboole_0) != k2_partfun1(sK3,X0,X2,k1_xboole_0) | ~v1_funct_2(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k4_subset_1(sK0,sK2,sK3),X0) | ~v1_funct_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2)) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK2) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | ~v1_funct_2(X2,sK3,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_2(X1,sK2,X0) | ~v1_funct_1(X1) | v1_xboole_0(X0)) )),
% 2.38/0.70    inference(global_subsumption,[],[f79,f80,f529])).
% 2.38/0.70  fof(f529,plain,(
% 2.38/0.70    ( ! [X2,X0,X1] : (k2_partfun1(sK2,X0,X1,k1_xboole_0) != k2_partfun1(sK3,X0,X2,k1_xboole_0) | ~m1_subset_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),X0))) | ~v1_funct_2(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),k4_subset_1(sK0,sK2,sK3),X0) | ~v1_funct_1(k1_tmap_1(sK0,X0,sK2,sK3,X1,X2)) | k2_partfun1(k4_subset_1(sK0,sK2,sK3),X0,k1_tmap_1(sK0,X0,sK2,sK3,X1,X2),sK2) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK3,X0))) | ~v1_funct_2(X2,sK3,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,X0))) | ~v1_funct_2(X1,sK2,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 2.38/0.70    inference(superposition,[],[f211,f146])).
% 2.38/0.70  fof(f211,plain,(
% 2.38/0.70    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK3))) != k2_partfun1(sK3,X1,X3,k1_setfam_1(k2_tarski(X0,sK3))) | ~m1_subset_1(k1_tmap_1(sK0,X1,X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,X0,sK3),X1))) | ~v1_funct_2(k1_tmap_1(sK0,X1,X0,sK3,X2,X3),k4_subset_1(sK0,X0,sK3),X1) | ~v1_funct_1(k1_tmap_1(sK0,X1,X0,sK3,X2,X3)) | k2_partfun1(k4_subset_1(sK0,X0,sK3),X1,k1_tmap_1(sK0,X1,X0,sK3,X2,X3),X0) = X2 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) | ~v1_funct_2(X3,sK3,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 2.38/0.70    inference(global_subsumption,[],[f77,f81,f82,f208])).
% 2.38/0.70  fof(f208,plain,(
% 2.38/0.70    ( ! [X2,X0,X3,X1] : (k2_partfun1(X0,X1,X2,k1_setfam_1(k2_tarski(X0,sK3))) != k2_partfun1(sK3,X1,X3,k1_setfam_1(k2_tarski(X0,sK3))) | ~m1_subset_1(k1_tmap_1(sK0,X1,X0,sK3,X2,X3),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,X0,sK3),X1))) | ~v1_funct_2(k1_tmap_1(sK0,X1,X0,sK3,X2,X3),k4_subset_1(sK0,X0,sK3),X1) | ~v1_funct_1(k1_tmap_1(sK0,X1,X0,sK3,X2,X3)) | k2_partfun1(k4_subset_1(sK0,X0,sK3),X1,k1_tmap_1(sK0,X1,X0,sK3,X2,X3),X0) = X2 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,X1))) | ~v1_funct_2(X3,sK3,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(sK0)) )),
% 2.38/0.70    inference(superposition,[],[f132,f149])).
% 2.38/0.70  fof(f132,plain,(
% 2.38/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.38/0.70    inference(equality_resolution,[],[f93])).
% 2.38/0.70  fof(f93,plain,(
% 2.38/0.70    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 2.38/0.70    inference(cnf_transformation,[],[f69])).
% 2.38/0.70  fof(f1079,plain,(
% 2.38/0.70    spl7_51),
% 2.38/0.70    inference(avatar_contradiction_clause,[],[f1078])).
% 2.38/0.70  fof(f1078,plain,(
% 2.38/0.70    $false | spl7_51),
% 2.38/0.70    inference(subsumption_resolution,[],[f87,f1047])).
% 2.38/0.70  fof(f1047,plain,(
% 2.38/0.70    ~v1_funct_1(sK5) | spl7_51),
% 2.38/0.70    inference(avatar_component_clause,[],[f1046])).
% 2.38/0.70  fof(f1060,plain,(
% 2.38/0.70    spl7_50),
% 2.38/0.70    inference(avatar_contradiction_clause,[],[f1059])).
% 2.38/0.70  fof(f1059,plain,(
% 2.38/0.70    $false | spl7_50),
% 2.38/0.70    inference(subsumption_resolution,[],[f82,f1044])).
% 2.38/0.70  fof(f1044,plain,(
% 2.38/0.70    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | spl7_50),
% 2.38/0.70    inference(avatar_component_clause,[],[f1043])).
% 2.38/0.70  fof(f1032,plain,(
% 2.38/0.70    spl7_48),
% 2.38/0.70    inference(avatar_contradiction_clause,[],[f1031])).
% 2.38/0.70  fof(f1031,plain,(
% 2.38/0.70    $false | spl7_48),
% 2.38/0.70    inference(subsumption_resolution,[],[f85,f1008])).
% 2.38/0.70  fof(f1008,plain,(
% 2.38/0.70    ~v1_funct_2(sK4,sK2,sK1) | spl7_48),
% 2.38/0.70    inference(avatar_component_clause,[],[f1007])).
% 2.38/0.70  fof(f1026,plain,(
% 2.38/0.70    spl7_47),
% 2.38/0.70    inference(avatar_contradiction_clause,[],[f1025])).
% 2.38/0.70  fof(f1025,plain,(
% 2.38/0.70    $false | spl7_47),
% 2.38/0.70    inference(subsumption_resolution,[],[f84,f1005])).
% 2.38/0.70  fof(f1005,plain,(
% 2.38/0.70    ~v1_funct_1(sK4) | spl7_47),
% 2.38/0.70    inference(avatar_component_clause,[],[f1004])).
% 2.38/0.70  fof(f1017,plain,(
% 2.38/0.70    spl7_46),
% 2.38/0.70    inference(avatar_contradiction_clause,[],[f1016])).
% 2.38/0.70  fof(f1016,plain,(
% 2.38/0.70    $false | spl7_46),
% 2.38/0.70    inference(subsumption_resolution,[],[f80,f1002])).
% 2.38/0.70  fof(f1002,plain,(
% 2.38/0.70    ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | spl7_46),
% 2.38/0.70    inference(avatar_component_clause,[],[f1001])).
% 2.38/0.70  fof(f907,plain,(
% 2.38/0.70    spl7_1),
% 2.38/0.70    inference(avatar_contradiction_clause,[],[f900])).
% 2.38/0.70  fof(f900,plain,(
% 2.38/0.70    $false | spl7_1),
% 2.38/0.70    inference(subsumption_resolution,[],[f794,f897])).
% 2.38/0.70  fof(f794,plain,(
% 2.38/0.70    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | spl7_1),
% 2.38/0.70    inference(backward_demodulation,[],[f330,f768])).
% 2.38/0.70  fof(f330,plain,(
% 2.38/0.70    k7_relat_1(sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | spl7_1),
% 2.38/0.70    inference(superposition,[],[f324,f182])).
% 2.38/0.70  fof(f324,plain,(
% 2.38/0.70    k2_partfun1(sK3,sK1,sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | spl7_1),
% 2.38/0.70    inference(backward_demodulation,[],[f228,f146])).
% 2.38/0.70  fof(f228,plain,(
% 2.38/0.70    k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK4,k1_setfam_1(k2_tarski(sK2,sK3))) | spl7_1),
% 2.38/0.70    inference(backward_demodulation,[],[f207,f161])).
% 2.38/0.70  fof(f207,plain,(
% 2.38/0.70    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k2_partfun1(sK3,sK1,sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | spl7_1),
% 2.38/0.70    inference(backward_demodulation,[],[f136,f149])).
% 2.38/0.70  fof(f136,plain,(
% 2.38/0.70    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl7_1),
% 2.38/0.70    inference(avatar_component_clause,[],[f135])).
% 2.38/0.70  fof(f135,plain,(
% 2.38/0.70    spl7_1 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 2.38/0.70    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.38/0.70  fof(f572,plain,(
% 2.38/0.70    spl7_20),
% 2.38/0.70    inference(avatar_contradiction_clause,[],[f571])).
% 2.38/0.70  fof(f571,plain,(
% 2.38/0.70    $false | spl7_20),
% 2.38/0.70    inference(subsumption_resolution,[],[f86,f566])).
% 2.38/0.70  fof(f566,plain,(
% 2.38/0.70    ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | spl7_20),
% 2.38/0.70    inference(avatar_component_clause,[],[f565])).
% 2.38/0.70  fof(f143,plain,(
% 2.38/0.70    ~spl7_1 | ~spl7_2 | ~spl7_3),
% 2.38/0.70    inference(avatar_split_clause,[],[f90,f141,f138,f135])).
% 2.38/0.70  fof(f90,plain,(
% 2.38/0.70    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 2.38/0.70    inference(cnf_transformation,[],[f67])).
% 2.38/0.70  % SZS output end Proof for theBenchmark
% 2.38/0.70  % (818)------------------------------
% 2.38/0.70  % (818)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.38/0.70  % (818)Termination reason: Refutation
% 2.38/0.70  
% 2.38/0.70  % (818)Memory used [KB]: 13304
% 2.38/0.70  % (818)Time elapsed: 0.252 s
% 2.38/0.70  % (818)------------------------------
% 2.38/0.70  % (818)------------------------------
% 2.38/0.70  % (814)Success in time 0.331 s
%------------------------------------------------------------------------------
