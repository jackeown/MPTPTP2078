%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:37 EST 2020

% Result     : Theorem 3.10s
% Output     : Refutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :  239 (3882 expanded)
%              Number of leaves         :   29 (1756 expanded)
%              Depth                    :   40
%              Number of atoms          : 1320 (53348 expanded)
%              Number of equality atoms :  230 (12139 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2010,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f129,f1929,f1988,f1990])).

fof(f1990,plain,
    ( ~ spl6_1
    | spl6_2 ),
    inference(avatar_contradiction_clause,[],[f1989])).

fof(f1989,plain,
    ( $false
    | ~ spl6_1
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1968,f1986])).

fof(f1986,plain,
    ( k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1985,f1856])).

fof(f1856,plain,(
    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    inference(resolution,[],[f1345,f141])).

fof(f141,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f103,f75])).

fof(f75,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f25,f51,f50,f49,f48,f47,f46])).

fof(f46,plain,
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

fof(f47,plain,
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

fof(f48,plain,
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

fof(f49,plain,
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

fof(f50,plain,
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

fof(f51,plain,
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1345,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k1_xboole_0 = k7_relat_1(X6,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f1333,f1264])).

fof(f1264,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f1256,f1254])).

fof(f1254,plain,(
    k1_xboole_0 = k3_xboole_0(sK3,k1_relat_1(sK4)) ),
    inference(resolution,[],[f568,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f568,plain,(
    r1_xboole_0(sK3,k1_relat_1(sK4)) ),
    inference(resolution,[],[f545,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f545,plain,(
    r1_xboole_0(k1_relat_1(sK4),sK3) ),
    inference(trivial_inequality_removal,[],[f543])).

fof(f543,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_relat_1(sK4),sK3) ),
    inference(superposition,[],[f168,f450])).

fof(f450,plain,(
    k1_xboole_0 = k7_relat_1(sK4,sK3) ),
    inference(forward_demodulation,[],[f447,f251])).

fof(f251,plain,(
    sK4 = k7_relat_1(sK4,sK2) ),
    inference(subsumption_resolution,[],[f250,f140])).

fof(f140,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f103,f72])).

fof(f72,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f250,plain,
    ( sK4 = k7_relat_1(sK4,sK2)
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f155,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f155,plain,(
    v4_relat_1(sK4,sK2) ),
    inference(resolution,[],[f104,f72])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f447,plain,(
    k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,sK2),sK3) ),
    inference(resolution,[],[f258,f140])).

fof(f258,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK2),sK3) ) ),
    inference(resolution,[],[f161,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f161,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f160,f65])).

fof(f65,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f160,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f159,f67])).

fof(f67,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f159,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f87,f69])).

fof(f69,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f168,plain,(
    ! [X4] :
      ( k1_xboole_0 != k7_relat_1(sK4,X4)
      | r1_xboole_0(k1_relat_1(sK4),X4) ) ),
    inference(resolution,[],[f84,f140])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | r1_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f1256,plain,(
    k1_relat_1(k1_xboole_0) = k3_xboole_0(sK3,k1_relat_1(sK4)) ),
    inference(superposition,[],[f544,f82])).

fof(f82,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f544,plain,(
    k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(sK4),sK3) ),
    inference(superposition,[],[f164,f450])).

fof(f164,plain,(
    ! [X4] : k1_relat_1(k7_relat_1(sK4,X4)) = k3_xboole_0(k1_relat_1(sK4),X4) ),
    inference(resolution,[],[f83,f140])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f1333,plain,(
    ! [X6] :
      ( k1_xboole_0 = k7_relat_1(X6,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(X6) ) ),
    inference(resolution,[],[f636,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,k1_relat_1(X0))
      | k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).

fof(f636,plain,(
    ! [X0] : r1_xboole_0(k1_relat_1(k1_xboole_0),X0) ),
    inference(trivial_inequality_removal,[],[f634])).

fof(f634,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_relat_1(k1_xboole_0),X0) ) ),
    inference(superposition,[],[f166,f416])).

fof(f416,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(subsumption_resolution,[],[f415,f130])).

fof(f130,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f81,f115])).

fof(f115,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f81,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f415,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[],[f311,f89])).

fof(f311,plain,(
    ! [X0] : v4_relat_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f157,f136])).

fof(f136,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(resolution,[],[f96,f113])).

fof(f113,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
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

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f157,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v4_relat_1(X1,X0) ) ),
    inference(superposition,[],[f104,f115])).

fof(f166,plain,(
    ! [X0] :
      ( k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
      | r1_xboole_0(k1_relat_1(k1_xboole_0),X0) ) ),
    inference(resolution,[],[f84,f130])).

fof(f1985,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1984,f260])).

fof(f260,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f161,f93])).

fof(f1984,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) = k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f1983,f173])).

fof(f173,plain,(
    ! [X1] : k9_subset_1(sK0,X1,sK3) = k3_xboole_0(X1,sK3) ),
    inference(resolution,[],[f101,f68])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1983,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1 ),
    inference(forward_demodulation,[],[f119,f200])).

fof(f200,plain,(
    ! [X1] : k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1) ),
    inference(subsumption_resolution,[],[f196,f73])).

fof(f73,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f52])).

fof(f196,plain,(
    ! [X1] :
      ( k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f105,f75])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f119,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl6_1
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1968,plain,
    ( k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | spl6_2 ),
    inference(forward_demodulation,[],[f1967,f1856])).

fof(f1967,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | spl6_2 ),
    inference(forward_demodulation,[],[f1966,f260])).

fof(f1966,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | spl6_2 ),
    inference(forward_demodulation,[],[f1965,f173])).

fof(f1965,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_2 ),
    inference(forward_demodulation,[],[f1964,f200])).

fof(f1964,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1963,f63])).

fof(f63,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f52])).

fof(f1963,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK0)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1962,f64])).

fof(f64,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f1962,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1961,f65])).

fof(f1961,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1960,f66])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f52])).

fof(f1960,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1959,f67])).

fof(f1959,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1958,f68])).

fof(f1958,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1957,f70])).

fof(f70,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f1957,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1956,f71])).

fof(f71,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f1956,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1955,f72])).

fof(f1955,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1954,f73])).

fof(f1954,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
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
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1953,f74])).

fof(f74,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f1953,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
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
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1952,f75])).

fof(f1952,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
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
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1951,f480])).

fof(f480,plain,(
    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f479,f63])).

fof(f479,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f477,f66])).

fof(f477,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f332,f68])).

fof(f332,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f331,f65])).

fof(f331,plain,(
    ! [X0] :
      ( v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f330,f70])).

fof(f330,plain,(
    ! [X0] :
      ( v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f325,f71])).

fof(f325,plain,(
    ! [X0] :
      ( v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | ~ v1_funct_2(sK4,sK2,sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f212,f72])).

fof(f212,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5))
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f211,f64])).

fof(f211,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f210,f67])).

fof(f210,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f209,f73])).

fof(f209,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5))
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
    inference(subsumption_resolution,[],[f202,f74])).

fof(f202,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5))
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
    inference(resolution,[],[f106,f75])).

fof(f106,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f1951,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
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
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1950,f526])).

fof(f526,plain,(
    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f525,f63])).

fof(f525,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f523,f66])).

fof(f523,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f366,f68])).

fof(f366,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f365,f65])).

fof(f365,plain,(
    ! [X0] :
      ( v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f364,f70])).

fof(f364,plain,(
    ! [X0] :
      ( v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f359,f71])).

fof(f359,plain,(
    ! [X0] :
      ( v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1)
      | ~ v1_funct_2(sK4,sK2,sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f237,f72])).

fof(f237,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1)
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f236,f64])).

fof(f236,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f235,f67])).

fof(f235,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f234,f73])).

fof(f234,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1)
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
    inference(subsumption_resolution,[],[f227,f74])).

fof(f227,plain,(
    ! [X4,X5,X3] :
      ( v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1)
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
    inference(resolution,[],[f107,f75])).

fof(f107,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
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
    inference(cnf_transformation,[],[f45])).

fof(f1950,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
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
    | spl6_2 ),
    inference(subsumption_resolution,[],[f1120,f124])).

fof(f124,plain,
    ( sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl6_2
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1120,plain,
    ( sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
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
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f534,f112])).

fof(f112,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
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
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f534,plain,(
    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    inference(subsumption_resolution,[],[f533,f63])).

fof(f533,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f531,f66])).

fof(f531,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f399,f68])).

fof(f399,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f398,f65])).

fof(f398,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f397,f70])).

fof(f397,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f392,f71])).

fof(f392,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1)))
      | ~ v1_funct_2(sK4,sK2,sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f249,f72])).

fof(f249,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1)))
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f248,f64])).

fof(f248,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f247,f67])).

fof(f247,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | v1_xboole_0(sK3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(sK1)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f246,f73])).

fof(f246,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1)))
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
    inference(subsumption_resolution,[],[f239,f74])).

fof(f239,plain,(
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
    inference(resolution,[],[f108,f75])).

fof(f108,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f1988,plain,
    ( ~ spl6_1
    | spl6_3 ),
    inference(avatar_contradiction_clause,[],[f1987])).

fof(f1987,plain,
    ( $false
    | ~ spl6_1
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1986,f1949])).

fof(f1949,plain,
    ( k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | spl6_3 ),
    inference(forward_demodulation,[],[f1948,f1856])).

fof(f1948,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | spl6_3 ),
    inference(forward_demodulation,[],[f1947,f260])).

fof(f1947,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | spl6_3 ),
    inference(forward_demodulation,[],[f1946,f173])).

fof(f1946,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_3 ),
    inference(forward_demodulation,[],[f1945,f200])).

fof(f1945,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1944,f63])).

fof(f1944,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1943,f64])).

fof(f1943,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1942,f65])).

fof(f1942,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1941,f66])).

fof(f1941,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1940,f67])).

fof(f1940,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1939,f68])).

fof(f1939,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1938,f70])).

fof(f1938,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1937,f71])).

fof(f1937,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1936,f72])).

fof(f1936,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1935,f73])).

fof(f1935,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
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
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1934,f74])).

fof(f1934,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
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
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1933,f75])).

fof(f1933,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
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
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1932,f480])).

fof(f1932,plain,
    ( ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
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
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1931,f526])).

fof(f1931,plain,
    ( ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
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
    | spl6_3 ),
    inference(subsumption_resolution,[],[f1121,f128])).

fof(f128,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl6_3
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f1121,plain,
    ( sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
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
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f534,f111])).

fof(f111,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
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
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
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
    inference(cnf_transformation,[],[f54])).

fof(f1929,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f1928])).

fof(f1928,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f1922,f1855])).

fof(f1855,plain,(
    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    inference(resolution,[],[f1345,f140])).

fof(f1922,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | spl6_1 ),
    inference(superposition,[],[f287,f1856])).

fof(f287,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | spl6_1 ),
    inference(forward_demodulation,[],[f286,f199])).

fof(f199,plain,(
    ! [X0] : k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) ),
    inference(subsumption_resolution,[],[f195,f70])).

fof(f195,plain,(
    ! [X0] :
      ( k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f105,f72])).

fof(f286,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | spl6_1 ),
    inference(forward_demodulation,[],[f285,f260])).

fof(f285,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | spl6_1 ),
    inference(forward_demodulation,[],[f284,f200])).

fof(f284,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3))
    | spl6_1 ),
    inference(superposition,[],[f120,f173])).

fof(f120,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f129,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f76,f126,f122,f118])).

fof(f76,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:27:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.51  % (18496)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.52  % (18485)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (18503)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.53  % (18484)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.54  % (18492)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.54  % (18478)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.56  % (18504)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.56  % (18500)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.56  % (18501)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.56  % (18486)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 1.63/0.56  % (18491)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.63/0.57  % (18497)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.63/0.57  % (18498)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.63/0.57  % (18488)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.63/0.57  % (18483)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.63/0.57  % (18489)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.63/0.57  % (18494)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.63/0.58  % (18487)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 1.63/0.58  % (18495)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.63/0.58  % (18505)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.63/0.58  % (18480)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.63/0.58  % (18502)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.84/0.61  % (18499)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.84/0.62  % (18506)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.84/0.62  % (18490)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 1.84/0.64  % (18482)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 2.35/0.69  % (18485)Refutation not found, incomplete strategy% (18485)------------------------------
% 2.35/0.69  % (18485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.35/0.69  % (18485)Termination reason: Refutation not found, incomplete strategy
% 2.35/0.69  
% 2.35/0.69  % (18485)Memory used [KB]: 7419
% 2.35/0.69  % (18485)Time elapsed: 0.280 s
% 2.35/0.69  % (18485)------------------------------
% 2.35/0.69  % (18485)------------------------------
% 2.35/0.69  % (18486)Refutation not found, incomplete strategy% (18486)------------------------------
% 2.35/0.69  % (18486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.35/0.69  % (18486)Termination reason: Refutation not found, incomplete strategy
% 2.35/0.69  
% 2.35/0.69  % (18486)Memory used [KB]: 11513
% 2.35/0.69  % (18486)Time elapsed: 0.261 s
% 2.35/0.69  % (18486)------------------------------
% 2.35/0.69  % (18486)------------------------------
% 3.10/0.77  % (18494)Refutation not found, incomplete strategy% (18494)------------------------------
% 3.10/0.77  % (18494)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.77  % (18494)Termination reason: Refutation not found, incomplete strategy
% 3.10/0.77  
% 3.10/0.77  % (18494)Memory used [KB]: 8187
% 3.10/0.77  % (18494)Time elapsed: 0.370 s
% 3.10/0.77  % (18494)------------------------------
% 3.10/0.77  % (18494)------------------------------
% 3.10/0.81  % (18489)Refutation not found, incomplete strategy% (18489)------------------------------
% 3.10/0.81  % (18489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.81  % (18489)Termination reason: Refutation not found, incomplete strategy
% 3.10/0.81  
% 3.10/0.81  % (18489)Memory used [KB]: 6268
% 3.10/0.81  % (18489)Time elapsed: 0.345 s
% 3.10/0.81  % (18489)------------------------------
% 3.10/0.81  % (18489)------------------------------
% 3.10/0.83  % (18490)Refutation found. Thanks to Tanya!
% 3.10/0.83  % SZS status Theorem for theBenchmark
% 3.10/0.83  % SZS output start Proof for theBenchmark
% 3.10/0.83  fof(f2010,plain,(
% 3.10/0.83    $false),
% 3.10/0.83    inference(avatar_sat_refutation,[],[f129,f1929,f1988,f1990])).
% 3.10/0.83  fof(f1990,plain,(
% 3.10/0.83    ~spl6_1 | spl6_2),
% 3.10/0.83    inference(avatar_contradiction_clause,[],[f1989])).
% 3.10/0.83  fof(f1989,plain,(
% 3.10/0.83    $false | (~spl6_1 | spl6_2)),
% 3.10/0.83    inference(subsumption_resolution,[],[f1968,f1986])).
% 3.10/0.83  fof(f1986,plain,(
% 3.10/0.83    k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | ~spl6_1),
% 3.10/0.83    inference(forward_demodulation,[],[f1985,f1856])).
% 3.10/0.83  fof(f1856,plain,(
% 3.10/0.83    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 3.10/0.83    inference(resolution,[],[f1345,f141])).
% 3.10/0.83  fof(f141,plain,(
% 3.10/0.83    v1_relat_1(sK5)),
% 3.10/0.83    inference(resolution,[],[f103,f75])).
% 3.10/0.83  fof(f75,plain,(
% 3.10/0.83    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 3.10/0.83    inference(cnf_transformation,[],[f52])).
% 3.10/0.83  fof(f52,plain,(
% 3.10/0.83    ((((((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 3.10/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f25,f51,f50,f49,f48,f47,f46])).
% 3.10/0.83  fof(f46,plain,(
% 3.10/0.83    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 3.10/0.83    introduced(choice_axiom,[])).
% 3.10/0.83  fof(f47,plain,(
% 3.10/0.83    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 3.10/0.83    introduced(choice_axiom,[])).
% 3.10/0.83  fof(f48,plain,(
% 3.10/0.83    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2))),
% 3.10/0.83    introduced(choice_axiom,[])).
% 3.10/0.83  fof(f49,plain,(
% 3.10/0.83    ? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3))),
% 3.10/0.83    introduced(choice_axiom,[])).
% 3.10/0.83  fof(f50,plain,(
% 3.10/0.83    ? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4))),
% 3.10/0.83    introduced(choice_axiom,[])).
% 3.10/0.83  fof(f51,plain,(
% 3.10/0.83    ? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) => ((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5))),
% 3.10/0.83    introduced(choice_axiom,[])).
% 3.10/0.83  fof(f25,plain,(
% 3.10/0.83    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.10/0.83    inference(flattening,[],[f24])).
% 3.10/0.83  fof(f24,plain,(
% 3.10/0.83    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 3.10/0.83    inference(ennf_transformation,[],[f22])).
% 3.10/0.83  fof(f22,negated_conjecture,(
% 3.10/0.83    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.10/0.83    inference(negated_conjecture,[],[f21])).
% 3.10/0.83  fof(f21,conjecture,(
% 3.10/0.83    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 3.10/0.83  fof(f103,plain,(
% 3.10/0.83    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f40])).
% 3.10/0.83  fof(f40,plain,(
% 3.10/0.83    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.83    inference(ennf_transformation,[],[f16])).
% 3.10/0.83  fof(f16,axiom,(
% 3.10/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 3.10/0.83  fof(f1345,plain,(
% 3.10/0.83    ( ! [X6] : (~v1_relat_1(X6) | k1_xboole_0 = k7_relat_1(X6,k1_xboole_0)) )),
% 3.10/0.83    inference(forward_demodulation,[],[f1333,f1264])).
% 3.10/0.83  fof(f1264,plain,(
% 3.10/0.83    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.10/0.83    inference(forward_demodulation,[],[f1256,f1254])).
% 3.10/0.83  fof(f1254,plain,(
% 3.10/0.83    k1_xboole_0 = k3_xboole_0(sK3,k1_relat_1(sK4))),
% 3.10/0.83    inference(resolution,[],[f568,f93])).
% 3.10/0.83  fof(f93,plain,(
% 3.10/0.83    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 3.10/0.83    inference(cnf_transformation,[],[f59])).
% 3.10/0.83  fof(f59,plain,(
% 3.10/0.83    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 3.10/0.83    inference(nnf_transformation,[],[f2])).
% 3.10/0.83  fof(f2,axiom,(
% 3.10/0.83    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 3.10/0.83  fof(f568,plain,(
% 3.10/0.83    r1_xboole_0(sK3,k1_relat_1(sK4))),
% 3.10/0.83    inference(resolution,[],[f545,f86])).
% 3.10/0.83  fof(f86,plain,(
% 3.10/0.83    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f31])).
% 3.10/0.83  fof(f31,plain,(
% 3.10/0.83    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.10/0.83    inference(ennf_transformation,[],[f3])).
% 3.10/0.83  fof(f3,axiom,(
% 3.10/0.83    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 3.10/0.83  fof(f545,plain,(
% 3.10/0.83    r1_xboole_0(k1_relat_1(sK4),sK3)),
% 3.10/0.83    inference(trivial_inequality_removal,[],[f543])).
% 3.10/0.83  fof(f543,plain,(
% 3.10/0.83    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(sK4),sK3)),
% 3.10/0.83    inference(superposition,[],[f168,f450])).
% 3.10/0.83  fof(f450,plain,(
% 3.10/0.83    k1_xboole_0 = k7_relat_1(sK4,sK3)),
% 3.10/0.83    inference(forward_demodulation,[],[f447,f251])).
% 3.10/0.83  fof(f251,plain,(
% 3.10/0.83    sK4 = k7_relat_1(sK4,sK2)),
% 3.10/0.83    inference(subsumption_resolution,[],[f250,f140])).
% 3.10/0.83  fof(f140,plain,(
% 3.10/0.83    v1_relat_1(sK4)),
% 3.10/0.83    inference(resolution,[],[f103,f72])).
% 3.10/0.83  fof(f72,plain,(
% 3.10/0.83    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 3.10/0.83    inference(cnf_transformation,[],[f52])).
% 3.10/0.83  fof(f250,plain,(
% 3.10/0.83    sK4 = k7_relat_1(sK4,sK2) | ~v1_relat_1(sK4)),
% 3.10/0.83    inference(resolution,[],[f155,f89])).
% 3.10/0.83  fof(f89,plain,(
% 3.10/0.83    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f35])).
% 3.10/0.83  fof(f35,plain,(
% 3.10/0.83    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.10/0.83    inference(flattening,[],[f34])).
% 3.10/0.83  fof(f34,plain,(
% 3.10/0.83    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.10/0.83    inference(ennf_transformation,[],[f12])).
% 3.10/0.83  fof(f12,axiom,(
% 3.10/0.83    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 3.10/0.83  fof(f155,plain,(
% 3.10/0.83    v4_relat_1(sK4,sK2)),
% 3.10/0.83    inference(resolution,[],[f104,f72])).
% 3.10/0.83  fof(f104,plain,(
% 3.10/0.83    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f41])).
% 3.10/0.83  fof(f41,plain,(
% 3.10/0.83    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.10/0.83    inference(ennf_transformation,[],[f23])).
% 3.10/0.83  fof(f23,plain,(
% 3.10/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.10/0.83    inference(pure_predicate_removal,[],[f17])).
% 3.10/0.83  fof(f17,axiom,(
% 3.10/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 3.10/0.83  fof(f447,plain,(
% 3.10/0.83    k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,sK2),sK3)),
% 3.10/0.83    inference(resolution,[],[f258,f140])).
% 3.10/0.83  fof(f258,plain,(
% 3.10/0.83    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,sK2),sK3)) )),
% 3.10/0.83    inference(resolution,[],[f161,f100])).
% 3.10/0.83  fof(f100,plain,(
% 3.10/0.83    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f37])).
% 3.10/0.83  fof(f37,plain,(
% 3.10/0.83    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 3.10/0.83    inference(flattening,[],[f36])).
% 3.10/0.83  fof(f36,plain,(
% 3.10/0.83    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 3.10/0.83    inference(ennf_transformation,[],[f11])).
% 3.10/0.83  fof(f11,axiom,(
% 3.10/0.83    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 3.10/0.83  fof(f161,plain,(
% 3.10/0.83    r1_xboole_0(sK2,sK3)),
% 3.10/0.83    inference(subsumption_resolution,[],[f160,f65])).
% 3.10/0.83  fof(f65,plain,(
% 3.10/0.83    ~v1_xboole_0(sK2)),
% 3.10/0.83    inference(cnf_transformation,[],[f52])).
% 3.10/0.83  fof(f160,plain,(
% 3.10/0.83    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2)),
% 3.10/0.83    inference(subsumption_resolution,[],[f159,f67])).
% 3.10/0.83  fof(f67,plain,(
% 3.10/0.83    ~v1_xboole_0(sK3)),
% 3.10/0.83    inference(cnf_transformation,[],[f52])).
% 3.10/0.83  fof(f159,plain,(
% 3.10/0.83    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2)),
% 3.10/0.83    inference(resolution,[],[f87,f69])).
% 3.10/0.83  fof(f69,plain,(
% 3.10/0.83    r1_subset_1(sK2,sK3)),
% 3.10/0.83    inference(cnf_transformation,[],[f52])).
% 3.10/0.83  fof(f87,plain,(
% 3.10/0.83    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f56])).
% 3.10/0.83  fof(f56,plain,(
% 3.10/0.83    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.10/0.83    inference(nnf_transformation,[],[f33])).
% 3.10/0.83  fof(f33,plain,(
% 3.10/0.83    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.10/0.83    inference(flattening,[],[f32])).
% 3.10/0.83  fof(f32,plain,(
% 3.10/0.83    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.10/0.83    inference(ennf_transformation,[],[f15])).
% 3.10/0.83  fof(f15,axiom,(
% 3.10/0.83    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 3.10/0.83  fof(f168,plain,(
% 3.10/0.83    ( ! [X4] : (k1_xboole_0 != k7_relat_1(sK4,X4) | r1_xboole_0(k1_relat_1(sK4),X4)) )),
% 3.10/0.83    inference(resolution,[],[f84,f140])).
% 3.10/0.83  fof(f84,plain,(
% 3.10/0.83    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_xboole_0 != k7_relat_1(X1,X0) | r1_xboole_0(k1_relat_1(X1),X0)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f55])).
% 3.10/0.83  fof(f55,plain,(
% 3.10/0.83    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.10/0.83    inference(nnf_transformation,[],[f30])).
% 3.10/0.83  fof(f30,plain,(
% 3.10/0.83    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.10/0.83    inference(ennf_transformation,[],[f14])).
% 3.10/0.83  fof(f14,axiom,(
% 3.10/0.83    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 3.10/0.83  fof(f1256,plain,(
% 3.10/0.83    k1_relat_1(k1_xboole_0) = k3_xboole_0(sK3,k1_relat_1(sK4))),
% 3.10/0.83    inference(superposition,[],[f544,f82])).
% 3.10/0.83  fof(f82,plain,(
% 3.10/0.83    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f1])).
% 3.10/0.83  fof(f1,axiom,(
% 3.10/0.83    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.10/0.83  fof(f544,plain,(
% 3.10/0.83    k1_relat_1(k1_xboole_0) = k3_xboole_0(k1_relat_1(sK4),sK3)),
% 3.10/0.83    inference(superposition,[],[f164,f450])).
% 3.10/0.83  fof(f164,plain,(
% 3.10/0.83    ( ! [X4] : (k1_relat_1(k7_relat_1(sK4,X4)) = k3_xboole_0(k1_relat_1(sK4),X4)) )),
% 3.10/0.83    inference(resolution,[],[f83,f140])).
% 3.10/0.83  fof(f83,plain,(
% 3.10/0.83    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f29])).
% 3.10/0.83  fof(f29,plain,(
% 3.10/0.83    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 3.10/0.83    inference(ennf_transformation,[],[f13])).
% 3.10/0.83  fof(f13,axiom,(
% 3.10/0.83    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 3.10/0.83  fof(f1333,plain,(
% 3.10/0.83    ( ! [X6] : (k1_xboole_0 = k7_relat_1(X6,k1_relat_1(k1_xboole_0)) | ~v1_relat_1(X6)) )),
% 3.10/0.83    inference(resolution,[],[f636,f80])).
% 3.10/0.83  fof(f80,plain,(
% 3.10/0.83    ( ! [X0,X1] : (~r1_xboole_0(X1,k1_relat_1(X0)) | k1_xboole_0 = k7_relat_1(X0,X1) | ~v1_relat_1(X0)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f28])).
% 3.10/0.83  fof(f28,plain,(
% 3.10/0.83    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.10/0.83    inference(ennf_transformation,[],[f10])).
% 3.10/0.83  fof(f10,axiom,(
% 3.10/0.83    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t187_relat_1)).
% 3.10/0.83  fof(f636,plain,(
% 3.10/0.83    ( ! [X0] : (r1_xboole_0(k1_relat_1(k1_xboole_0),X0)) )),
% 3.10/0.83    inference(trivial_inequality_removal,[],[f634])).
% 3.10/0.83  fof(f634,plain,(
% 3.10/0.83    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_relat_1(k1_xboole_0),X0)) )),
% 3.10/0.83    inference(superposition,[],[f166,f416])).
% 3.10/0.83  fof(f416,plain,(
% 3.10/0.83    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f415,f130])).
% 3.10/0.83  fof(f130,plain,(
% 3.10/0.83    v1_relat_1(k1_xboole_0)),
% 3.10/0.83    inference(superposition,[],[f81,f115])).
% 3.10/0.83  fof(f115,plain,(
% 3.10/0.83    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.10/0.83    inference(equality_resolution,[],[f99])).
% 3.10/0.83  fof(f99,plain,(
% 3.10/0.83    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.10/0.83    inference(cnf_transformation,[],[f62])).
% 3.10/0.83  fof(f62,plain,(
% 3.10/0.83    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.10/0.83    inference(flattening,[],[f61])).
% 3.10/0.83  fof(f61,plain,(
% 3.10/0.83    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.10/0.83    inference(nnf_transformation,[],[f5])).
% 3.10/0.83  fof(f5,axiom,(
% 3.10/0.83    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.10/0.83  fof(f81,plain,(
% 3.10/0.83    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.10/0.83    inference(cnf_transformation,[],[f9])).
% 3.10/0.83  fof(f9,axiom,(
% 3.10/0.83    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 3.10/0.83  fof(f415,plain,(
% 3.10/0.83    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 3.10/0.83    inference(resolution,[],[f311,f89])).
% 3.10/0.83  fof(f311,plain,(
% 3.10/0.83    ( ! [X0] : (v4_relat_1(k1_xboole_0,X0)) )),
% 3.10/0.83    inference(resolution,[],[f157,f136])).
% 3.10/0.83  fof(f136,plain,(
% 3.10/0.83    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 3.10/0.83    inference(resolution,[],[f96,f113])).
% 3.10/0.83  fof(f113,plain,(
% 3.10/0.83    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.10/0.83    inference(equality_resolution,[],[f91])).
% 3.10/0.83  fof(f91,plain,(
% 3.10/0.83    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.10/0.83    inference(cnf_transformation,[],[f58])).
% 3.10/0.83  fof(f58,plain,(
% 3.10/0.83    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.10/0.83    inference(flattening,[],[f57])).
% 3.10/0.83  fof(f57,plain,(
% 3.10/0.83    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.10/0.83    inference(nnf_transformation,[],[f4])).
% 3.10/0.83  fof(f4,axiom,(
% 3.10/0.83    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.10/0.83  fof(f96,plain,(
% 3.10/0.83    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.10/0.83    inference(cnf_transformation,[],[f60])).
% 3.10/0.83  fof(f60,plain,(
% 3.10/0.83    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.10/0.83    inference(nnf_transformation,[],[f8])).
% 3.10/0.83  fof(f8,axiom,(
% 3.10/0.83    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 3.10/0.83  fof(f157,plain,(
% 3.10/0.83    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v4_relat_1(X1,X0)) )),
% 3.10/0.83    inference(superposition,[],[f104,f115])).
% 3.10/0.83  fof(f166,plain,(
% 3.10/0.83    ( ! [X0] : (k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) | r1_xboole_0(k1_relat_1(k1_xboole_0),X0)) )),
% 3.10/0.83    inference(resolution,[],[f84,f130])).
% 3.10/0.83  fof(f1985,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0) | ~spl6_1),
% 3.10/0.83    inference(forward_demodulation,[],[f1984,f260])).
% 3.10/0.83  fof(f260,plain,(
% 3.10/0.83    k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 3.10/0.83    inference(resolution,[],[f161,f93])).
% 3.10/0.83  fof(f1984,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) = k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | ~spl6_1),
% 3.10/0.83    inference(forward_demodulation,[],[f1983,f173])).
% 3.10/0.83  fof(f173,plain,(
% 3.10/0.83    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k3_xboole_0(X1,sK3)) )),
% 3.10/0.83    inference(resolution,[],[f101,f68])).
% 3.10/0.83  fof(f68,plain,(
% 3.10/0.83    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 3.10/0.83    inference(cnf_transformation,[],[f52])).
% 3.10/0.83  fof(f101,plain,(
% 3.10/0.83    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f38])).
% 3.10/0.83  fof(f38,plain,(
% 3.10/0.83    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.10/0.83    inference(ennf_transformation,[],[f7])).
% 3.10/0.83  fof(f7,axiom,(
% 3.10/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 3.10/0.83  fof(f1983,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | ~spl6_1),
% 3.10/0.83    inference(forward_demodulation,[],[f119,f200])).
% 3.10/0.83  fof(f200,plain,(
% 3.10/0.83    ( ! [X1] : (k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f196,f73])).
% 3.10/0.83  fof(f73,plain,(
% 3.10/0.83    v1_funct_1(sK5)),
% 3.10/0.83    inference(cnf_transformation,[],[f52])).
% 3.10/0.83  fof(f196,plain,(
% 3.10/0.83    ( ! [X1] : (k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1) | ~v1_funct_1(sK5)) )),
% 3.10/0.83    inference(resolution,[],[f105,f75])).
% 3.10/0.83  fof(f105,plain,(
% 3.10/0.83    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f43])).
% 3.10/0.83  fof(f43,plain,(
% 3.10/0.83    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.10/0.83    inference(flattening,[],[f42])).
% 3.10/0.83  fof(f42,plain,(
% 3.10/0.83    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.10/0.83    inference(ennf_transformation,[],[f18])).
% 3.10/0.83  fof(f18,axiom,(
% 3.10/0.83    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 3.10/0.83  fof(f119,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~spl6_1),
% 3.10/0.83    inference(avatar_component_clause,[],[f118])).
% 3.10/0.83  fof(f118,plain,(
% 3.10/0.83    spl6_1 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 3.10/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 3.10/0.83  fof(f1968,plain,(
% 3.10/0.83    k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | spl6_2),
% 3.10/0.83    inference(forward_demodulation,[],[f1967,f1856])).
% 3.10/0.83  fof(f1967,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | spl6_2),
% 3.10/0.83    inference(forward_demodulation,[],[f1966,f260])).
% 3.10/0.83  fof(f1966,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | spl6_2),
% 3.10/0.83    inference(forward_demodulation,[],[f1965,f173])).
% 3.10/0.83  fof(f1965,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_2),
% 3.10/0.83    inference(forward_demodulation,[],[f1964,f200])).
% 3.10/0.83  fof(f1964,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1963,f63])).
% 3.10/0.83  fof(f63,plain,(
% 3.10/0.83    ~v1_xboole_0(sK0)),
% 3.10/0.83    inference(cnf_transformation,[],[f52])).
% 3.10/0.83  fof(f1963,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK0) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1962,f64])).
% 3.10/0.83  fof(f64,plain,(
% 3.10/0.83    ~v1_xboole_0(sK1)),
% 3.10/0.83    inference(cnf_transformation,[],[f52])).
% 3.10/0.83  fof(f1962,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1961,f65])).
% 3.10/0.83  fof(f1961,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1960,f66])).
% 3.10/0.83  fof(f66,plain,(
% 3.10/0.83    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 3.10/0.83    inference(cnf_transformation,[],[f52])).
% 3.10/0.83  fof(f1960,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1959,f67])).
% 3.10/0.83  fof(f1959,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1958,f68])).
% 3.10/0.83  fof(f1958,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1957,f70])).
% 3.10/0.83  fof(f70,plain,(
% 3.10/0.83    v1_funct_1(sK4)),
% 3.10/0.83    inference(cnf_transformation,[],[f52])).
% 3.10/0.83  fof(f1957,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1956,f71])).
% 3.10/0.83  fof(f71,plain,(
% 3.10/0.83    v1_funct_2(sK4,sK2,sK1)),
% 3.10/0.83    inference(cnf_transformation,[],[f52])).
% 3.10/0.83  fof(f1956,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1955,f72])).
% 3.10/0.83  fof(f1955,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1954,f73])).
% 3.10/0.83  fof(f1954,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1953,f74])).
% 3.10/0.83  fof(f74,plain,(
% 3.10/0.83    v1_funct_2(sK5,sK3,sK1)),
% 3.10/0.83    inference(cnf_transformation,[],[f52])).
% 3.10/0.83  fof(f1953,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1952,f75])).
% 3.10/0.83  fof(f1952,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1951,f480])).
% 3.10/0.83  fof(f480,plain,(
% 3.10/0.83    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 3.10/0.83    inference(subsumption_resolution,[],[f479,f63])).
% 3.10/0.83  fof(f479,plain,(
% 3.10/0.83    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v1_xboole_0(sK0)),
% 3.10/0.83    inference(subsumption_resolution,[],[f477,f66])).
% 3.10/0.83  fof(f477,plain,(
% 3.10/0.83    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 3.10/0.83    inference(resolution,[],[f332,f68])).
% 3.10/0.83  fof(f332,plain,(
% 3.10/0.83    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f331,f65])).
% 3.10/0.83  fof(f331,plain,(
% 3.10/0.83    ( ! [X0] : (v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f330,f70])).
% 3.10/0.83  fof(f330,plain,(
% 3.10/0.83    ( ! [X0] : (v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f325,f71])).
% 3.10/0.83  fof(f325,plain,(
% 3.10/0.83    ( ! [X0] : (v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(resolution,[],[f212,f72])).
% 3.10/0.83  fof(f212,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5)) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f211,f64])).
% 3.10/0.83  fof(f211,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f210,f67])).
% 3.10/0.83  fof(f210,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f209,f73])).
% 3.10/0.83  fof(f209,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5)) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f202,f74])).
% 3.10/0.83  fof(f202,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5)) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(resolution,[],[f106,f75])).
% 3.10/0.83  fof(f106,plain,(
% 3.10/0.83    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f45])).
% 3.10/0.83  fof(f45,plain,(
% 3.10/0.83    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 3.10/0.83    inference(flattening,[],[f44])).
% 3.10/0.83  fof(f44,plain,(
% 3.10/0.83    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 3.10/0.83    inference(ennf_transformation,[],[f20])).
% 3.10/0.83  fof(f20,axiom,(
% 3.10/0.83    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 3.10/0.83  fof(f1951,plain,(
% 3.10/0.83    ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1950,f526])).
% 3.10/0.83  fof(f526,plain,(
% 3.10/0.83    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 3.10/0.83    inference(subsumption_resolution,[],[f525,f63])).
% 3.10/0.83  fof(f525,plain,(
% 3.10/0.83    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0)),
% 3.10/0.83    inference(subsumption_resolution,[],[f523,f66])).
% 3.10/0.83  fof(f523,plain,(
% 3.10/0.83    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 3.10/0.83    inference(resolution,[],[f366,f68])).
% 3.10/0.83  fof(f366,plain,(
% 3.10/0.83    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f365,f65])).
% 3.10/0.83  fof(f365,plain,(
% 3.10/0.83    ( ! [X0] : (v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f364,f70])).
% 3.10/0.83  fof(f364,plain,(
% 3.10/0.83    ( ! [X0] : (v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f359,f71])).
% 3.10/0.83  fof(f359,plain,(
% 3.10/0.83    ( ! [X0] : (v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(resolution,[],[f237,f72])).
% 3.10/0.83  fof(f237,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f236,f64])).
% 3.10/0.83  fof(f236,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f235,f67])).
% 3.10/0.83  fof(f235,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f234,f73])).
% 3.10/0.83  fof(f234,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f227,f74])).
% 3.10/0.83  fof(f227,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(resolution,[],[f107,f75])).
% 3.10/0.83  fof(f107,plain,(
% 3.10/0.83    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f45])).
% 3.10/0.83  fof(f1950,plain,(
% 3.10/0.83    ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 3.10/0.83    inference(subsumption_resolution,[],[f1120,f124])).
% 3.10/0.83  fof(f124,plain,(
% 3.10/0.83    sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | spl6_2),
% 3.10/0.83    inference(avatar_component_clause,[],[f122])).
% 3.10/0.83  fof(f122,plain,(
% 3.10/0.83    spl6_2 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 3.10/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 3.10/0.83  fof(f1120,plain,(
% 3.10/0.83    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 3.10/0.83    inference(resolution,[],[f534,f112])).
% 3.10/0.83  fof(f112,plain,(
% 3.10/0.83    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(equality_resolution,[],[f77])).
% 3.10/0.83  fof(f77,plain,(
% 3.10/0.83    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f54])).
% 3.10/0.83  fof(f54,plain,(
% 3.10/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.10/0.83    inference(flattening,[],[f53])).
% 3.10/0.83  fof(f53,plain,(
% 3.10/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.10/0.83    inference(nnf_transformation,[],[f27])).
% 3.10/0.83  fof(f27,plain,(
% 3.10/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.10/0.83    inference(flattening,[],[f26])).
% 3.10/0.83  fof(f26,plain,(
% 3.10/0.83    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.10/0.83    inference(ennf_transformation,[],[f19])).
% 3.10/0.83  fof(f19,axiom,(
% 3.10/0.83    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 3.10/0.83    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 3.10/0.83  fof(f534,plain,(
% 3.10/0.83    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 3.10/0.83    inference(subsumption_resolution,[],[f533,f63])).
% 3.10/0.83  fof(f533,plain,(
% 3.10/0.83    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK0)),
% 3.10/0.83    inference(subsumption_resolution,[],[f531,f66])).
% 3.10/0.83  fof(f531,plain,(
% 3.10/0.83    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 3.10/0.83    inference(resolution,[],[f399,f68])).
% 3.10/0.83  fof(f399,plain,(
% 3.10/0.83    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f398,f65])).
% 3.10/0.83  fof(f398,plain,(
% 3.10/0.83    ( ! [X0] : (m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f397,f70])).
% 3.10/0.83  fof(f397,plain,(
% 3.10/0.83    ( ! [X0] : (m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f392,f71])).
% 3.10/0.83  fof(f392,plain,(
% 3.10/0.83    ( ! [X0] : (m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(resolution,[],[f249,f72])).
% 3.10/0.83  fof(f249,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f248,f64])).
% 3.10/0.83  fof(f248,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f247,f67])).
% 3.10/0.83  fof(f247,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f246,f73])).
% 3.10/0.83  fof(f246,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f239,f74])).
% 3.10/0.83  fof(f239,plain,(
% 3.10/0.83    ( ! [X4,X5,X3] : (m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 3.10/0.83    inference(resolution,[],[f108,f75])).
% 3.10/0.83  fof(f108,plain,(
% 3.10/0.83    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f45])).
% 3.10/0.83  fof(f1988,plain,(
% 3.10/0.83    ~spl6_1 | spl6_3),
% 3.10/0.83    inference(avatar_contradiction_clause,[],[f1987])).
% 3.10/0.83  fof(f1987,plain,(
% 3.10/0.83    $false | (~spl6_1 | spl6_3)),
% 3.10/0.83    inference(subsumption_resolution,[],[f1986,f1949])).
% 3.10/0.83  fof(f1949,plain,(
% 3.10/0.83    k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | spl6_3),
% 3.10/0.83    inference(forward_demodulation,[],[f1948,f1856])).
% 3.10/0.83  fof(f1948,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | spl6_3),
% 3.10/0.83    inference(forward_demodulation,[],[f1947,f260])).
% 3.10/0.83  fof(f1947,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | spl6_3),
% 3.10/0.83    inference(forward_demodulation,[],[f1946,f173])).
% 3.10/0.83  fof(f1946,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_3),
% 3.10/0.83    inference(forward_demodulation,[],[f1945,f200])).
% 3.10/0.83  fof(f1945,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1944,f63])).
% 3.10/0.83  fof(f1944,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK0) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1943,f64])).
% 3.10/0.83  fof(f1943,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1942,f65])).
% 3.10/0.83  fof(f1942,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1941,f66])).
% 3.10/0.83  fof(f1941,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1940,f67])).
% 3.10/0.83  fof(f1940,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1939,f68])).
% 3.10/0.83  fof(f1939,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1938,f70])).
% 3.10/0.83  fof(f1938,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1937,f71])).
% 3.10/0.83  fof(f1937,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1936,f72])).
% 3.10/0.83  fof(f1936,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1935,f73])).
% 3.10/0.83  fof(f1935,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1934,f74])).
% 3.10/0.83  fof(f1934,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1933,f75])).
% 3.10/0.83  fof(f1933,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1932,f480])).
% 3.10/0.83  fof(f1932,plain,(
% 3.10/0.83    ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1931,f526])).
% 3.10/0.83  fof(f1931,plain,(
% 3.10/0.83    ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_3),
% 3.10/0.83    inference(subsumption_resolution,[],[f1121,f128])).
% 3.10/0.83  fof(f128,plain,(
% 3.10/0.83    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | spl6_3),
% 3.10/0.83    inference(avatar_component_clause,[],[f126])).
% 3.10/0.83  fof(f126,plain,(
% 3.10/0.83    spl6_3 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 3.10/0.83    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 3.10/0.83  fof(f1121,plain,(
% 3.10/0.83    sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 3.10/0.83    inference(resolution,[],[f534,f111])).
% 3.10/0.83  fof(f111,plain,(
% 3.10/0.83    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(equality_resolution,[],[f78])).
% 3.10/0.83  fof(f78,plain,(
% 3.10/0.83    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.10/0.83    inference(cnf_transformation,[],[f54])).
% 3.10/0.83  fof(f1929,plain,(
% 3.10/0.83    spl6_1),
% 3.10/0.83    inference(avatar_contradiction_clause,[],[f1928])).
% 3.10/0.83  fof(f1928,plain,(
% 3.10/0.83    $false | spl6_1),
% 3.10/0.83    inference(subsumption_resolution,[],[f1922,f1855])).
% 3.10/0.83  fof(f1855,plain,(
% 3.10/0.83    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 3.10/0.83    inference(resolution,[],[f1345,f140])).
% 3.10/0.83  fof(f1922,plain,(
% 3.10/0.83    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | spl6_1),
% 3.10/0.83    inference(superposition,[],[f287,f1856])).
% 3.10/0.83  fof(f287,plain,(
% 3.10/0.83    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | spl6_1),
% 3.10/0.83    inference(forward_demodulation,[],[f286,f199])).
% 3.10/0.83  fof(f199,plain,(
% 3.10/0.83    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0)) )),
% 3.10/0.83    inference(subsumption_resolution,[],[f195,f70])).
% 3.10/0.83  fof(f195,plain,(
% 3.10/0.83    ( ! [X0] : (k7_relat_1(sK4,X0) = k2_partfun1(sK2,sK1,sK4,X0) | ~v1_funct_1(sK4)) )),
% 3.10/0.83    inference(resolution,[],[f105,f72])).
% 3.10/0.83  fof(f286,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | spl6_1),
% 3.10/0.83    inference(forward_demodulation,[],[f285,f260])).
% 3.10/0.83  fof(f285,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | spl6_1),
% 3.10/0.83    inference(forward_demodulation,[],[f284,f200])).
% 3.10/0.83  fof(f284,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) | spl6_1),
% 3.10/0.83    inference(superposition,[],[f120,f173])).
% 3.10/0.83  fof(f120,plain,(
% 3.10/0.83    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_1),
% 3.10/0.83    inference(avatar_component_clause,[],[f118])).
% 3.10/0.83  fof(f129,plain,(
% 3.10/0.83    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 3.10/0.83    inference(avatar_split_clause,[],[f76,f126,f122,f118])).
% 3.10/0.83  fof(f76,plain,(
% 3.10/0.83    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 3.10/0.83    inference(cnf_transformation,[],[f52])).
% 3.10/0.83  % SZS output end Proof for theBenchmark
% 3.10/0.83  % (18490)------------------------------
% 3.10/0.83  % (18490)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.10/0.83  % (18490)Termination reason: Refutation
% 3.10/0.83  
% 3.10/0.83  % (18490)Memory used [KB]: 11897
% 3.10/0.83  % (18490)Time elapsed: 0.331 s
% 3.10/0.83  % (18490)------------------------------
% 3.10/0.83  % (18490)------------------------------
% 3.10/0.83  % (18472)Success in time 0.481 s
%------------------------------------------------------------------------------
