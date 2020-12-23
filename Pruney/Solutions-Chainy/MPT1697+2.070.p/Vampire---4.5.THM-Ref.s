%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:39 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  214 (2376 expanded)
%              Number of leaves         :   26 (1138 expanded)
%              Depth                    :   40
%              Number of atoms          : 1291 (35702 expanded)
%              Number of equality atoms :  188 (7825 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1096,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f118,f1026,f1074,f1076])).

fof(f1076,plain,
    ( ~ spl8_1
    | spl8_2 ),
    inference(avatar_contradiction_clause,[],[f1075])).

fof(f1075,plain,
    ( $false
    | ~ spl8_1
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1064,f1072])).

fof(f1072,plain,
    ( k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f1071,f978])).

fof(f978,plain,(
    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    inference(superposition,[],[f961,f304])).

fof(f304,plain,(
    sK5 = k7_relat_1(sK5,k1_relat_1(sK5)) ),
    inference(subsumption_resolution,[],[f302,f129])).

fof(f129,plain,(
    v1_relat_1(sK5) ),
    inference(resolution,[],[f95,f70])).

fof(f70,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f42,f41,f40,f39,f38,f37])).

fof(f37,plain,
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

fof(f38,plain,
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

fof(f39,plain,
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

fof(f40,plain,
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

fof(f41,plain,
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

fof(f42,plain,
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f302,plain,
    ( sK5 = k7_relat_1(sK5,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5) ),
    inference(resolution,[],[f238,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f238,plain,(
    v4_relat_1(sK5,k1_relat_1(sK5)) ),
    inference(resolution,[],[f130,f129])).

fof(f130,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | v4_relat_1(X0,k1_relat_1(X0)) ) ),
    inference(resolution,[],[f82,f104])).

fof(f104,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X1),X0)
      | v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f961,plain,(
    ! [X1] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,X1),k1_xboole_0) ),
    inference(resolution,[],[f315,f129])).

fof(f315,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0) ) ),
    inference(resolution,[],[f236,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)
      | ~ r1_xboole_0(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r1_xboole_0(X0,X1)
       => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

fof(f236,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(resolution,[],[f126,f72])).

fof(f72,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f79,f76])).

fof(f76,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK6(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f47,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK6(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f79,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK7(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK7(X0,X1),X1)
          & r2_hidden(sK7(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK7(X0,X1),X1)
        & r2_hidden(sK7(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
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
    inference(rectify,[],[f4])).

fof(f4,axiom,(
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

fof(f1071,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f1070,f197])).

fof(f197,plain,(
    k1_xboole_0 = k3_xboole_0(sK2,sK3) ),
    inference(resolution,[],[f144,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
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

fof(f144,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(subsumption_resolution,[],[f143,f60])).

fof(f60,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f143,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK2) ),
    inference(subsumption_resolution,[],[f142,f62])).

fof(f62,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f142,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2) ),
    inference(resolution,[],[f83,f64])).

fof(f64,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f1070,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) = k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f1069,f146])).

fof(f146,plain,(
    ! [X1] : k9_subset_1(sK0,X1,sK3) = k3_xboole_0(X1,sK3) ),
    inference(resolution,[],[f94,f63])).

fof(f63,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f1069,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl8_1 ),
    inference(forward_demodulation,[],[f108,f152])).

fof(f152,plain,(
    ! [X1] : k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1) ),
    inference(subsumption_resolution,[],[f150,f68])).

fof(f68,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f43])).

fof(f150,plain,(
    ! [X1] :
      ( k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)
      | ~ v1_funct_1(sK5) ) ),
    inference(resolution,[],[f96,f70])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f108,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl8_1
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f1064,plain,
    ( k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | spl8_2 ),
    inference(forward_demodulation,[],[f1063,f978])).

fof(f1063,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | spl8_2 ),
    inference(forward_demodulation,[],[f1062,f197])).

fof(f1062,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | spl8_2 ),
    inference(forward_demodulation,[],[f1061,f146])).

fof(f1061,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl8_2 ),
    inference(forward_demodulation,[],[f1060,f152])).

fof(f1060,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1059,f58])).

fof(f58,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f1059,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK0)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1058,f59])).

fof(f59,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f1058,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1057,f60])).

fof(f1057,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1056,f61])).

fof(f61,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f43])).

fof(f1056,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1055,f62])).

fof(f1055,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1054,f63])).

fof(f1054,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1053,f65])).

fof(f65,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f1053,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1052,f66])).

fof(f66,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f1052,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1051,f67])).

fof(f67,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f43])).

fof(f1051,plain,
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
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1050,f68])).

fof(f1050,plain,
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
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1049,f69])).

fof(f69,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f1049,plain,
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
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1048,f70])).

fof(f1048,plain,
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
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1047,f348])).

fof(f348,plain,(
    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) ),
    inference(subsumption_resolution,[],[f347,f58])).

fof(f347,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f345,f61])).

fof(f345,plain,
    ( v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f255,f63])).

fof(f255,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f254,f60])).

fof(f254,plain,(
    ! [X0] :
      ( v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f253,f65])).

fof(f253,plain,(
    ! [X0] :
      ( v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f249,f66])).

fof(f249,plain,(
    ! [X0] :
      ( v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5))
      | ~ v1_funct_2(sK4,sK2,sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f162,f67])).

fof(f162,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5))
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f161,f59])).

fof(f161,plain,(
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
    inference(subsumption_resolution,[],[f160,f62])).

fof(f160,plain,(
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
    inference(subsumption_resolution,[],[f159,f68])).

fof(f159,plain,(
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
    inference(subsumption_resolution,[],[f154,f69])).

fof(f154,plain,(
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
    inference(resolution,[],[f97,f70])).

fof(f97,plain,(
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
    inference(cnf_transformation,[],[f36])).

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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f1047,plain,
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
    | spl8_2 ),
    inference(subsumption_resolution,[],[f1046,f372])).

fof(f372,plain,(
    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) ),
    inference(subsumption_resolution,[],[f371,f58])).

fof(f371,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f369,f61])).

fof(f369,plain,
    ( v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f275,f63])).

fof(f275,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f274,f60])).

fof(f274,plain,(
    ! [X0] :
      ( v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f273,f65])).

fof(f273,plain,(
    ! [X0] :
      ( v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f269,f66])).

fof(f269,plain,(
    ! [X0] :
      ( v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1)
      | ~ v1_funct_2(sK4,sK2,sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f172,f67])).

fof(f172,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1)
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f171,f59])).

fof(f171,plain,(
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
    inference(subsumption_resolution,[],[f170,f62])).

fof(f170,plain,(
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
    inference(subsumption_resolution,[],[f169,f68])).

fof(f169,plain,(
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
    inference(subsumption_resolution,[],[f164,f69])).

fof(f164,plain,(
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
    inference(resolution,[],[f98,f70])).

fof(f98,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f1046,plain,
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
    | spl8_2 ),
    inference(subsumption_resolution,[],[f874,f113])).

fof(f113,plain,
    ( sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl8_2
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f874,plain,
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
    inference(resolution,[],[f380,f103])).

fof(f103,plain,(
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
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
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
    inference(flattening,[],[f44])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f22])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f380,plain,(
    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) ),
    inference(subsumption_resolution,[],[f379,f58])).

fof(f379,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | v1_xboole_0(sK0) ),
    inference(subsumption_resolution,[],[f377,f61])).

fof(f377,plain,
    ( m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK0) ),
    inference(resolution,[],[f295,f63])).

fof(f295,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1)))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f294,f60])).

fof(f294,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1)))
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f293,f65])).

fof(f293,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1)))
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f289,f66])).

fof(f289,plain,(
    ! [X0] :
      ( m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1)))
      | ~ v1_funct_2(sK4,sK2,sK1)
      | ~ v1_funct_1(sK4)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X0))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
      | v1_xboole_0(sK2)
      | v1_xboole_0(X0) ) ),
    inference(resolution,[],[f182,f67])).

fof(f182,plain,(
    ! [X4,X5,X3] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1)))
      | m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1)))
      | ~ v1_funct_2(X5,X4,sK1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | v1_xboole_0(X4)
      | v1_xboole_0(X3) ) ),
    inference(subsumption_resolution,[],[f181,f59])).

fof(f181,plain,(
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
    inference(subsumption_resolution,[],[f180,f62])).

fof(f180,plain,(
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
    inference(subsumption_resolution,[],[f179,f68])).

fof(f179,plain,(
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
    inference(subsumption_resolution,[],[f174,f69])).

fof(f174,plain,(
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
    inference(resolution,[],[f99,f70])).

fof(f99,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f1074,plain,
    ( ~ spl8_1
    | spl8_3 ),
    inference(avatar_contradiction_clause,[],[f1073])).

fof(f1073,plain,
    ( $false
    | ~ spl8_1
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1072,f1045])).

fof(f1045,plain,
    ( k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | spl8_3 ),
    inference(forward_demodulation,[],[f1044,f978])).

fof(f1044,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | spl8_3 ),
    inference(forward_demodulation,[],[f1043,f197])).

fof(f1043,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | spl8_3 ),
    inference(forward_demodulation,[],[f1042,f146])).

fof(f1042,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl8_3 ),
    inference(forward_demodulation,[],[f1041,f152])).

fof(f1041,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1040,f58])).

fof(f1040,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK0)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1039,f59])).

fof(f1039,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1038,f60])).

fof(f1038,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1037,f61])).

fof(f1037,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1036,f62])).

fof(f1036,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1035,f63])).

fof(f1035,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1034,f65])).

fof(f1034,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1033,f66])).

fof(f1033,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1032,f67])).

fof(f1032,plain,
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
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1031,f68])).

fof(f1031,plain,
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
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1030,f69])).

fof(f1030,plain,
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
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1029,f70])).

fof(f1029,plain,
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
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1028,f348])).

fof(f1028,plain,
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
    | spl8_3 ),
    inference(subsumption_resolution,[],[f1027,f372])).

fof(f1027,plain,
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
    | spl8_3 ),
    inference(subsumption_resolution,[],[f875,f117])).

fof(f117,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl8_3
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f875,plain,
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
    inference(resolution,[],[f380,f102])).

fof(f102,plain,(
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
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
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
    inference(cnf_transformation,[],[f45])).

fof(f1026,plain,(
    spl8_1 ),
    inference(avatar_contradiction_clause,[],[f1025])).

fof(f1025,plain,
    ( $false
    | spl8_1 ),
    inference(subsumption_resolution,[],[f1023,f977])).

fof(f977,plain,(
    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    inference(superposition,[],[f960,f301])).

fof(f301,plain,(
    sK4 = k7_relat_1(sK4,k1_relat_1(sK4)) ),
    inference(subsumption_resolution,[],[f299,f128])).

fof(f128,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f95,f67])).

fof(f299,plain,
    ( sK4 = k7_relat_1(sK4,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(resolution,[],[f237,f85])).

fof(f237,plain,(
    v4_relat_1(sK4,k1_relat_1(sK4)) ),
    inference(resolution,[],[f130,f128])).

fof(f960,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0) ),
    inference(resolution,[],[f315,f128])).

fof(f1023,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | spl8_1 ),
    inference(superposition,[],[f223,f978])).

fof(f223,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | spl8_1 ),
    inference(forward_demodulation,[],[f222,f151])).

fof(f151,plain,(
    ! [X0] : k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) ),
    inference(subsumption_resolution,[],[f149,f65])).

fof(f149,plain,(
    ! [X0] :
      ( k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
      | ~ v1_funct_1(sK4) ) ),
    inference(resolution,[],[f96,f67])).

fof(f222,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | spl8_1 ),
    inference(forward_demodulation,[],[f221,f197])).

fof(f221,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3))
    | spl8_1 ),
    inference(forward_demodulation,[],[f220,f152])).

fof(f220,plain,
    ( k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3))
    | spl8_1 ),
    inference(superposition,[],[f109,f146])).

fof(f109,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl8_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f118,plain,
    ( ~ spl8_1
    | ~ spl8_2
    | ~ spl8_3 ),
    inference(avatar_split_clause,[],[f71,f115,f111,f107])).

fof(f71,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:52:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (24900)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (24892)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (24902)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.52  % (24890)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (24887)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (24892)Refutation not found, incomplete strategy% (24892)------------------------------
% 0.22/0.53  % (24892)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (24892)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (24892)Memory used [KB]: 6780
% 0.22/0.53  % (24892)Time elapsed: 0.043 s
% 0.22/0.53  % (24892)------------------------------
% 0.22/0.53  % (24892)------------------------------
% 0.22/0.53  % (24897)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (24894)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.22/0.53  % (24891)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (24893)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.53  % (24905)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.54  % (24900)Refutation not found, incomplete strategy% (24900)------------------------------
% 0.22/0.54  % (24900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (24900)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (24900)Memory used [KB]: 7931
% 0.22/0.54  % (24900)Time elapsed: 0.058 s
% 0.22/0.54  % (24900)------------------------------
% 0.22/0.54  % (24900)------------------------------
% 0.22/0.54  % (24889)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.54  % (24908)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.22/0.54  % (24901)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.54  % (24899)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.54  % (24903)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.22/0.54  % (24909)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.54  % (24907)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.55  % (24912)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.22/0.55  % (24888)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.55  % (24904)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.22/0.56  % (24895)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.22/0.56  % (24906)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.56  % (24896)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.56  % (24898)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.56  % (24911)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.22/0.56  % (24910)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.57  % (24893)Refutation not found, incomplete strategy% (24893)------------------------------
% 0.22/0.57  % (24893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (24897)Refutation found. Thanks to Tanya!
% 1.66/0.58  % SZS status Theorem for theBenchmark
% 1.66/0.58  % SZS output start Proof for theBenchmark
% 1.66/0.58  fof(f1096,plain,(
% 1.66/0.58    $false),
% 1.66/0.58    inference(avatar_sat_refutation,[],[f118,f1026,f1074,f1076])).
% 1.66/0.58  fof(f1076,plain,(
% 1.66/0.58    ~spl8_1 | spl8_2),
% 1.66/0.58    inference(avatar_contradiction_clause,[],[f1075])).
% 1.66/0.58  fof(f1075,plain,(
% 1.66/0.58    $false | (~spl8_1 | spl8_2)),
% 1.66/0.58    inference(subsumption_resolution,[],[f1064,f1072])).
% 1.66/0.58  fof(f1072,plain,(
% 1.66/0.58    k1_xboole_0 = k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | ~spl8_1),
% 1.66/0.58    inference(forward_demodulation,[],[f1071,f978])).
% 1.66/0.58  fof(f978,plain,(
% 1.66/0.58    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 1.66/0.58    inference(superposition,[],[f961,f304])).
% 1.66/0.58  fof(f304,plain,(
% 1.66/0.58    sK5 = k7_relat_1(sK5,k1_relat_1(sK5))),
% 1.66/0.58    inference(subsumption_resolution,[],[f302,f129])).
% 1.66/0.58  fof(f129,plain,(
% 1.66/0.58    v1_relat_1(sK5)),
% 1.66/0.58    inference(resolution,[],[f95,f70])).
% 1.66/0.58  fof(f70,plain,(
% 1.66/0.58    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 1.66/0.58    inference(cnf_transformation,[],[f43])).
% 1.66/0.58  fof(f43,plain,(
% 1.66/0.58    ((((((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 1.66/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f42,f41,f40,f39,f38,f37])).
% 1.66/0.58  fof(f37,plain,(
% 1.66/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 1.66/0.58    introduced(choice_axiom,[])).
% 1.66/0.58  fof(f38,plain,(
% 1.66/0.58    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 1.66/0.58    introduced(choice_axiom,[])).
% 1.66/0.58  fof(f39,plain,(
% 1.66/0.58    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2))),
% 1.66/0.58    introduced(choice_axiom,[])).
% 1.66/0.58  fof(f40,plain,(
% 1.66/0.58    ? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3))),
% 1.66/0.58    introduced(choice_axiom,[])).
% 1.66/0.58  fof(f41,plain,(
% 1.66/0.58    ? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4))),
% 1.66/0.58    introduced(choice_axiom,[])).
% 1.66/0.58  fof(f42,plain,(
% 1.66/0.58    ? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) => ((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5))),
% 1.66/0.58    introduced(choice_axiom,[])).
% 1.66/0.58  fof(f20,plain,(
% 1.66/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.66/0.58    inference(flattening,[],[f19])).
% 1.66/0.58  fof(f19,plain,(
% 1.66/0.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 1.66/0.58    inference(ennf_transformation,[],[f17])).
% 1.66/0.58  fof(f17,negated_conjecture,(
% 1.66/0.58    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.66/0.58    inference(negated_conjecture,[],[f16])).
% 1.66/0.58  fof(f16,conjecture,(
% 1.66/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tmap_1)).
% 1.66/0.58  fof(f95,plain,(
% 1.66/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f32])).
% 1.66/0.58  fof(f32,plain,(
% 1.66/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.66/0.58    inference(ennf_transformation,[],[f12])).
% 1.66/0.58  fof(f12,axiom,(
% 1.66/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.66/0.58  fof(f302,plain,(
% 1.66/0.58    sK5 = k7_relat_1(sK5,k1_relat_1(sK5)) | ~v1_relat_1(sK5)),
% 1.66/0.58    inference(resolution,[],[f238,f85])).
% 1.66/0.58  fof(f85,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f28])).
% 1.66/0.58  fof(f28,plain,(
% 1.66/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.66/0.58    inference(flattening,[],[f27])).
% 1.66/0.58  fof(f27,plain,(
% 1.66/0.58    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.66/0.58    inference(ennf_transformation,[],[f10])).
% 1.66/0.58  fof(f10,axiom,(
% 1.66/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 1.66/0.58  fof(f238,plain,(
% 1.66/0.58    v4_relat_1(sK5,k1_relat_1(sK5))),
% 1.66/0.58    inference(resolution,[],[f130,f129])).
% 1.66/0.58  fof(f130,plain,(
% 1.66/0.58    ( ! [X0] : (~v1_relat_1(X0) | v4_relat_1(X0,k1_relat_1(X0))) )),
% 1.66/0.58    inference(resolution,[],[f82,f104])).
% 1.66/0.58  fof(f104,plain,(
% 1.66/0.58    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.66/0.58    inference(equality_resolution,[],[f87])).
% 1.66/0.58  fof(f87,plain,(
% 1.66/0.58    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.66/0.58    inference(cnf_transformation,[],[f55])).
% 1.66/0.58  fof(f55,plain,(
% 1.66/0.58    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.58    inference(flattening,[],[f54])).
% 1.66/0.58  fof(f54,plain,(
% 1.66/0.58    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.66/0.58    inference(nnf_transformation,[],[f5])).
% 1.66/0.58  fof(f5,axiom,(
% 1.66/0.58    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.66/0.58  fof(f82,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~r1_tarski(k1_relat_1(X1),X0) | v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f52])).
% 1.66/0.58  fof(f52,plain,(
% 1.66/0.58    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.66/0.58    inference(nnf_transformation,[],[f24])).
% 1.66/0.58  fof(f24,plain,(
% 1.66/0.58    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.66/0.58    inference(ennf_transformation,[],[f8])).
% 1.66/0.58  fof(f8,axiom,(
% 1.66/0.58    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.66/0.58  fof(f961,plain,(
% 1.66/0.58    ( ! [X1] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK5,X1),k1_xboole_0)) )),
% 1.66/0.58    inference(resolution,[],[f315,f129])).
% 1.66/0.58  fof(f315,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~v1_relat_1(X0) | k1_xboole_0 = k7_relat_1(k7_relat_1(X0,X1),k1_xboole_0)) )),
% 1.66/0.58    inference(resolution,[],[f236,f93])).
% 1.66/0.58  fof(f93,plain,(
% 1.66/0.58    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~v1_relat_1(X2)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f30])).
% 1.66/0.58  fof(f30,plain,(
% 1.66/0.58    ! [X0,X1,X2] : (k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1) | ~v1_relat_1(X2))),
% 1.66/0.58    inference(flattening,[],[f29])).
% 1.66/0.58  fof(f29,plain,(
% 1.66/0.58    ! [X0,X1,X2] : ((k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1) | ~r1_xboole_0(X0,X1)) | ~v1_relat_1(X2))),
% 1.66/0.58    inference(ennf_transformation,[],[f9])).
% 1.66/0.58  fof(f9,axiom,(
% 1.66/0.58    ! [X0,X1,X2] : (v1_relat_1(X2) => (r1_xboole_0(X0,X1) => k1_xboole_0 = k7_relat_1(k7_relat_1(X2,X0),X1)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).
% 1.66/0.58  fof(f236,plain,(
% 1.66/0.58    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.66/0.58    inference(resolution,[],[f126,f72])).
% 1.66/0.58  fof(f72,plain,(
% 1.66/0.58    v1_xboole_0(k1_xboole_0)),
% 1.66/0.58    inference(cnf_transformation,[],[f3])).
% 1.66/0.58  fof(f3,axiom,(
% 1.66/0.58    v1_xboole_0(k1_xboole_0)),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.66/0.58  fof(f126,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~v1_xboole_0(X1) | r1_xboole_0(X0,X1)) )),
% 1.66/0.58    inference(resolution,[],[f79,f76])).
% 1.66/0.58  fof(f76,plain,(
% 1.66/0.58    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f49])).
% 1.66/0.58  fof(f49,plain,(
% 1.66/0.58    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK6(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.66/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f47,f48])).
% 1.66/0.58  fof(f48,plain,(
% 1.66/0.58    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK6(X0),X0))),
% 1.66/0.58    introduced(choice_axiom,[])).
% 1.66/0.58  fof(f47,plain,(
% 1.66/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.66/0.58    inference(rectify,[],[f46])).
% 1.66/0.58  fof(f46,plain,(
% 1.66/0.58    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.66/0.58    inference(nnf_transformation,[],[f1])).
% 1.66/0.58  fof(f1,axiom,(
% 1.66/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.66/0.58  fof(f79,plain,(
% 1.66/0.58    ( ! [X0,X1] : (r2_hidden(sK7(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f51])).
% 1.66/0.58  fof(f51,plain,(
% 1.66/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.66/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f23,f50])).
% 1.66/0.58  fof(f50,plain,(
% 1.66/0.58    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK7(X0,X1),X1) & r2_hidden(sK7(X0,X1),X0)))),
% 1.66/0.58    introduced(choice_axiom,[])).
% 1.66/0.58  fof(f23,plain,(
% 1.66/0.58    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.66/0.58    inference(ennf_transformation,[],[f18])).
% 1.66/0.58  fof(f18,plain,(
% 1.66/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.66/0.58    inference(rectify,[],[f4])).
% 1.66/0.58  fof(f4,axiom,(
% 1.66/0.58    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.66/0.58  fof(f1071,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) = k7_relat_1(sK5,k1_xboole_0) | ~spl8_1),
% 1.66/0.58    inference(forward_demodulation,[],[f1070,f197])).
% 1.66/0.58  fof(f197,plain,(
% 1.66/0.58    k1_xboole_0 = k3_xboole_0(sK2,sK3)),
% 1.66/0.58    inference(resolution,[],[f144,f89])).
% 1.66/0.58  fof(f89,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.66/0.58    inference(cnf_transformation,[],[f56])).
% 1.66/0.58  fof(f56,plain,(
% 1.66/0.58    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.66/0.58    inference(nnf_transformation,[],[f2])).
% 1.66/0.58  fof(f2,axiom,(
% 1.66/0.58    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.66/0.58  fof(f144,plain,(
% 1.66/0.58    r1_xboole_0(sK2,sK3)),
% 1.66/0.58    inference(subsumption_resolution,[],[f143,f60])).
% 1.66/0.58  fof(f60,plain,(
% 1.66/0.58    ~v1_xboole_0(sK2)),
% 1.66/0.58    inference(cnf_transformation,[],[f43])).
% 1.66/0.58  fof(f143,plain,(
% 1.66/0.58    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK2)),
% 1.66/0.58    inference(subsumption_resolution,[],[f142,f62])).
% 1.66/0.58  fof(f62,plain,(
% 1.66/0.58    ~v1_xboole_0(sK3)),
% 1.66/0.58    inference(cnf_transformation,[],[f43])).
% 1.66/0.58  fof(f142,plain,(
% 1.66/0.58    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2)),
% 1.66/0.58    inference(resolution,[],[f83,f64])).
% 1.66/0.58  fof(f64,plain,(
% 1.66/0.58    r1_subset_1(sK2,sK3)),
% 1.66/0.58    inference(cnf_transformation,[],[f43])).
% 1.66/0.58  fof(f83,plain,(
% 1.66/0.58    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f53])).
% 1.66/0.58  fof(f53,plain,(
% 1.66/0.58    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.66/0.58    inference(nnf_transformation,[],[f26])).
% 1.66/0.58  fof(f26,plain,(
% 1.66/0.58    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.66/0.58    inference(flattening,[],[f25])).
% 1.66/0.58  fof(f25,plain,(
% 1.66/0.58    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.66/0.58    inference(ennf_transformation,[],[f11])).
% 1.66/0.58  fof(f11,axiom,(
% 1.66/0.58    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 1.66/0.58  fof(f1070,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) = k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | ~spl8_1),
% 1.66/0.58    inference(forward_demodulation,[],[f1069,f146])).
% 1.66/0.58  fof(f146,plain,(
% 1.66/0.58    ( ! [X1] : (k9_subset_1(sK0,X1,sK3) = k3_xboole_0(X1,sK3)) )),
% 1.66/0.58    inference(resolution,[],[f94,f63])).
% 1.66/0.58  fof(f63,plain,(
% 1.66/0.58    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 1.66/0.58    inference(cnf_transformation,[],[f43])).
% 1.66/0.58  fof(f94,plain,(
% 1.66/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(X0)) | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f31])).
% 1.66/0.58  fof(f31,plain,(
% 1.66/0.58    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.66/0.58    inference(ennf_transformation,[],[f6])).
% 1.66/0.58  fof(f6,axiom,(
% 1.66/0.58    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.66/0.58  fof(f1069,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | ~spl8_1),
% 1.66/0.58    inference(forward_demodulation,[],[f108,f152])).
% 1.66/0.58  fof(f152,plain,(
% 1.66/0.58    ( ! [X1] : (k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f150,f68])).
% 1.66/0.58  fof(f68,plain,(
% 1.66/0.58    v1_funct_1(sK5)),
% 1.66/0.58    inference(cnf_transformation,[],[f43])).
% 1.66/0.58  fof(f150,plain,(
% 1.66/0.58    ( ! [X1] : (k2_partfun1(sK3,sK1,sK5,X1) = k7_relat_1(sK5,X1) | ~v1_funct_1(sK5)) )),
% 1.66/0.58    inference(resolution,[],[f96,f70])).
% 1.66/0.58  fof(f96,plain,(
% 1.66/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~v1_funct_1(X2)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f34])).
% 1.66/0.58  fof(f34,plain,(
% 1.66/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.66/0.58    inference(flattening,[],[f33])).
% 1.66/0.58  fof(f33,plain,(
% 1.66/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.66/0.58    inference(ennf_transformation,[],[f13])).
% 1.66/0.58  fof(f13,axiom,(
% 1.66/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 1.66/0.58  fof(f108,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~spl8_1),
% 1.66/0.58    inference(avatar_component_clause,[],[f107])).
% 1.66/0.58  fof(f107,plain,(
% 1.66/0.58    spl8_1 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.66/0.58  fof(f1064,plain,(
% 1.66/0.58    k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | spl8_2),
% 1.66/0.58    inference(forward_demodulation,[],[f1063,f978])).
% 1.66/0.58  fof(f1063,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | spl8_2),
% 1.66/0.58    inference(forward_demodulation,[],[f1062,f197])).
% 1.66/0.58  fof(f1062,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | spl8_2),
% 1.66/0.58    inference(forward_demodulation,[],[f1061,f146])).
% 1.66/0.58  fof(f1061,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | spl8_2),
% 1.66/0.58    inference(forward_demodulation,[],[f1060,f152])).
% 1.66/0.58  fof(f1060,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f1059,f58])).
% 1.66/0.58  fof(f58,plain,(
% 1.66/0.58    ~v1_xboole_0(sK0)),
% 1.66/0.58    inference(cnf_transformation,[],[f43])).
% 1.66/0.58  fof(f1059,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK0) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f1058,f59])).
% 1.66/0.58  fof(f59,plain,(
% 1.66/0.58    ~v1_xboole_0(sK1)),
% 1.66/0.58    inference(cnf_transformation,[],[f43])).
% 1.66/0.58  fof(f1058,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f1057,f60])).
% 1.66/0.58  fof(f1057,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f1056,f61])).
% 1.66/0.58  fof(f61,plain,(
% 1.66/0.58    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 1.66/0.58    inference(cnf_transformation,[],[f43])).
% 1.66/0.58  fof(f1056,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f1055,f62])).
% 1.66/0.58  fof(f1055,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f1054,f63])).
% 1.66/0.58  fof(f1054,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f1053,f65])).
% 1.66/0.58  fof(f65,plain,(
% 1.66/0.58    v1_funct_1(sK4)),
% 1.66/0.58    inference(cnf_transformation,[],[f43])).
% 1.66/0.58  fof(f1053,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f1052,f66])).
% 1.66/0.58  fof(f66,plain,(
% 1.66/0.58    v1_funct_2(sK4,sK2,sK1)),
% 1.66/0.58    inference(cnf_transformation,[],[f43])).
% 1.66/0.58  fof(f1052,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f1051,f67])).
% 1.66/0.58  fof(f67,plain,(
% 1.66/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 1.66/0.58    inference(cnf_transformation,[],[f43])).
% 1.66/0.58  fof(f1051,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f1050,f68])).
% 1.66/0.58  fof(f1050,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f1049,f69])).
% 1.66/0.58  fof(f69,plain,(
% 1.66/0.58    v1_funct_2(sK5,sK3,sK1)),
% 1.66/0.58    inference(cnf_transformation,[],[f43])).
% 1.66/0.58  fof(f1049,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f1048,f70])).
% 1.66/0.58  fof(f1048,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f1047,f348])).
% 1.66/0.58  fof(f348,plain,(
% 1.66/0.58    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5))),
% 1.66/0.58    inference(subsumption_resolution,[],[f347,f58])).
% 1.66/0.58  fof(f347,plain,(
% 1.66/0.58    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | v1_xboole_0(sK0)),
% 1.66/0.58    inference(subsumption_resolution,[],[f345,f61])).
% 1.66/0.58  fof(f345,plain,(
% 1.66/0.58    v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 1.66/0.58    inference(resolution,[],[f255,f63])).
% 1.66/0.58  fof(f255,plain,(
% 1.66/0.58    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f254,f60])).
% 1.66/0.58  fof(f254,plain,(
% 1.66/0.58    ( ! [X0] : (v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f253,f65])).
% 1.66/0.58  fof(f253,plain,(
% 1.66/0.58    ( ! [X0] : (v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f249,f66])).
% 1.66/0.58  fof(f249,plain,(
% 1.66/0.58    ( ! [X0] : (v1_funct_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5)) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(resolution,[],[f162,f67])).
% 1.66/0.58  fof(f162,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5)) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f161,f59])).
% 1.66/0.58  fof(f161,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f160,f62])).
% 1.66/0.58  fof(f160,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f159,f68])).
% 1.66/0.58  fof(f159,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5)) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f154,f69])).
% 1.66/0.58  fof(f154,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (v1_funct_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5)) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(resolution,[],[f97,f70])).
% 1.66/0.58  fof(f97,plain,(
% 1.66/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f36])).
% 1.66/0.58  fof(f36,plain,(
% 1.66/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 1.66/0.58    inference(flattening,[],[f35])).
% 1.66/0.58  fof(f35,plain,(
% 1.66/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 1.66/0.58    inference(ennf_transformation,[],[f15])).
% 1.66/0.58  fof(f15,axiom,(
% 1.66/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 1.66/0.58  fof(f1047,plain,(
% 1.66/0.58    ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f1046,f372])).
% 1.66/0.58  fof(f372,plain,(
% 1.66/0.58    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1)),
% 1.66/0.58    inference(subsumption_resolution,[],[f371,f58])).
% 1.66/0.58  fof(f371,plain,(
% 1.66/0.58    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | v1_xboole_0(sK0)),
% 1.66/0.58    inference(subsumption_resolution,[],[f369,f61])).
% 1.66/0.58  fof(f369,plain,(
% 1.66/0.58    v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 1.66/0.58    inference(resolution,[],[f275,f63])).
% 1.66/0.58  fof(f275,plain,(
% 1.66/0.58    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f274,f60])).
% 1.66/0.58  fof(f274,plain,(
% 1.66/0.58    ( ! [X0] : (v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f273,f65])).
% 1.66/0.58  fof(f273,plain,(
% 1.66/0.58    ( ! [X0] : (v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f269,f66])).
% 1.66/0.58  fof(f269,plain,(
% 1.66/0.58    ( ! [X0] : (v1_funct_2(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(X0,sK2,sK3),sK1) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(resolution,[],[f172,f67])).
% 1.66/0.58  fof(f172,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f171,f59])).
% 1.66/0.58  fof(f171,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f170,f62])).
% 1.66/0.58  fof(f170,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f169,f68])).
% 1.66/0.58  fof(f169,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f164,f69])).
% 1.66/0.58  fof(f164,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (v1_funct_2(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k4_subset_1(X3,X4,sK3),sK1) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(resolution,[],[f98,f70])).
% 1.66/0.58  fof(f98,plain,(
% 1.66/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f36])).
% 1.66/0.58  fof(f1046,plain,(
% 1.66/0.58    ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_2),
% 1.66/0.58    inference(subsumption_resolution,[],[f874,f113])).
% 1.66/0.58  fof(f113,plain,(
% 1.66/0.58    sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | spl8_2),
% 1.66/0.58    inference(avatar_component_clause,[],[f111])).
% 1.66/0.58  fof(f111,plain,(
% 1.66/0.58    spl8_2 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.66/0.58  fof(f874,plain,(
% 1.66/0.58    sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 1.66/0.58    inference(resolution,[],[f380,f103])).
% 1.66/0.58  fof(f103,plain,(
% 1.66/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(equality_resolution,[],[f73])).
% 1.66/0.58  fof(f73,plain,(
% 1.66/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f45])).
% 1.66/0.58  fof(f45,plain,(
% 1.66/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.66/0.58    inference(flattening,[],[f44])).
% 1.66/0.58  fof(f44,plain,(
% 1.66/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.66/0.58    inference(nnf_transformation,[],[f22])).
% 1.66/0.58  fof(f22,plain,(
% 1.66/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.66/0.58    inference(flattening,[],[f21])).
% 1.66/0.58  fof(f21,plain,(
% 1.66/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.66/0.58    inference(ennf_transformation,[],[f14])).
% 1.66/0.58  fof(f14,axiom,(
% 1.66/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 1.66/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tmap_1)).
% 1.66/0.58  fof(f380,plain,(
% 1.66/0.58    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1)))),
% 1.66/0.58    inference(subsumption_resolution,[],[f379,f58])).
% 1.66/0.58  fof(f379,plain,(
% 1.66/0.58    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | v1_xboole_0(sK0)),
% 1.66/0.58    inference(subsumption_resolution,[],[f377,f61])).
% 1.66/0.58  fof(f377,plain,(
% 1.66/0.58    m1_subset_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(sK0,sK2,sK3),sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK0)),
% 1.66/0.58    inference(resolution,[],[f295,f63])).
% 1.66/0.58  fof(f295,plain,(
% 1.66/0.58    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(X0)) | m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f294,f60])).
% 1.66/0.58  fof(f294,plain,(
% 1.66/0.58    ( ! [X0] : (m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f293,f65])).
% 1.66/0.58  fof(f293,plain,(
% 1.66/0.58    ( ! [X0] : (m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1))) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f289,f66])).
% 1.66/0.58  fof(f289,plain,(
% 1.66/0.58    ( ! [X0] : (m1_subset_1(k1_tmap_1(X0,sK1,sK2,sK3,sK4,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,sK2,sK3),sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(X0)) | v1_xboole_0(sK2) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(resolution,[],[f182,f67])).
% 1.66/0.58  fof(f182,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f181,f59])).
% 1.66/0.58  fof(f181,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f180,f62])).
% 1.66/0.58  fof(f180,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f179,f68])).
% 1.66/0.58  fof(f179,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f174,f69])).
% 1.66/0.58  fof(f174,plain,(
% 1.66/0.58    ( ! [X4,X5,X3] : (m1_subset_1(k1_tmap_1(X3,sK1,X4,sK3,X5,sK5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X3,X4,sK3),sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X4,sK1))) | ~v1_funct_2(X5,X4,sK1) | ~v1_funct_1(X5) | ~m1_subset_1(sK3,k1_zfmisc_1(X3)) | v1_xboole_0(sK3) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | v1_xboole_0(sK1) | v1_xboole_0(X3)) )),
% 1.66/0.58    inference(resolution,[],[f99,f70])).
% 1.66/0.58  fof(f99,plain,(
% 1.66/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f36])).
% 1.66/0.58  fof(f1074,plain,(
% 1.66/0.58    ~spl8_1 | spl8_3),
% 1.66/0.58    inference(avatar_contradiction_clause,[],[f1073])).
% 1.66/0.58  fof(f1073,plain,(
% 1.66/0.58    $false | (~spl8_1 | spl8_3)),
% 1.66/0.58    inference(subsumption_resolution,[],[f1072,f1045])).
% 1.66/0.58  fof(f1045,plain,(
% 1.66/0.58    k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | spl8_3),
% 1.66/0.58    inference(forward_demodulation,[],[f1044,f978])).
% 1.66/0.58  fof(f1044,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | spl8_3),
% 1.66/0.58    inference(forward_demodulation,[],[f1043,f197])).
% 1.66/0.58  fof(f1043,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | spl8_3),
% 1.66/0.58    inference(forward_demodulation,[],[f1042,f146])).
% 1.66/0.58  fof(f1042,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | spl8_3),
% 1.66/0.58    inference(forward_demodulation,[],[f1041,f152])).
% 1.66/0.58  fof(f1041,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f1040,f58])).
% 1.66/0.58  fof(f1040,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK0) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f1039,f59])).
% 1.66/0.58  fof(f1039,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f1038,f60])).
% 1.66/0.58  fof(f1038,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f1037,f61])).
% 1.66/0.58  fof(f1037,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f1036,f62])).
% 1.66/0.58  fof(f1036,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f1035,f63])).
% 1.66/0.58  fof(f1035,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f1034,f65])).
% 1.66/0.58  fof(f1034,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f1033,f66])).
% 1.66/0.58  fof(f1033,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f1032,f67])).
% 1.66/0.58  fof(f1032,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f1031,f68])).
% 1.66/0.58  fof(f1031,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f1030,f69])).
% 1.66/0.58  fof(f1030,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f1029,f70])).
% 1.66/0.58  fof(f1029,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f1028,f348])).
% 1.66/0.58  fof(f1028,plain,(
% 1.66/0.58    ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f1027,f372])).
% 1.66/0.58  fof(f1027,plain,(
% 1.66/0.58    ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl8_3),
% 1.66/0.58    inference(subsumption_resolution,[],[f875,f117])).
% 1.66/0.58  fof(f117,plain,(
% 1.66/0.58    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | spl8_3),
% 1.66/0.58    inference(avatar_component_clause,[],[f115])).
% 1.66/0.58  fof(f115,plain,(
% 1.66/0.58    spl8_3 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 1.66/0.58    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.66/0.58  fof(f875,plain,(
% 1.66/0.58    sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | ~v1_funct_2(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),k4_subset_1(sK0,sK2,sK3),sK1) | ~v1_funct_1(k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5)) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0)),
% 1.66/0.58    inference(resolution,[],[f380,f102])).
% 1.66/0.58  fof(f102,plain,(
% 1.66/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(equality_resolution,[],[f74])).
% 1.66/0.58  fof(f74,plain,(
% 1.66/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 1.66/0.58    inference(cnf_transformation,[],[f45])).
% 1.66/0.58  fof(f1026,plain,(
% 1.66/0.58    spl8_1),
% 1.66/0.58    inference(avatar_contradiction_clause,[],[f1025])).
% 1.66/0.58  fof(f1025,plain,(
% 1.66/0.58    $false | spl8_1),
% 1.66/0.58    inference(subsumption_resolution,[],[f1023,f977])).
% 1.66/0.58  fof(f977,plain,(
% 1.66/0.58    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 1.66/0.58    inference(superposition,[],[f960,f301])).
% 1.66/0.58  fof(f301,plain,(
% 1.66/0.58    sK4 = k7_relat_1(sK4,k1_relat_1(sK4))),
% 1.66/0.58    inference(subsumption_resolution,[],[f299,f128])).
% 1.66/0.58  fof(f128,plain,(
% 1.66/0.58    v1_relat_1(sK4)),
% 1.66/0.58    inference(resolution,[],[f95,f67])).
% 1.66/0.58  fof(f299,plain,(
% 1.66/0.58    sK4 = k7_relat_1(sK4,k1_relat_1(sK4)) | ~v1_relat_1(sK4)),
% 1.66/0.58    inference(resolution,[],[f237,f85])).
% 1.66/0.58  fof(f237,plain,(
% 1.66/0.58    v4_relat_1(sK4,k1_relat_1(sK4))),
% 1.66/0.58    inference(resolution,[],[f130,f128])).
% 1.66/0.58  fof(f960,plain,(
% 1.66/0.58    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k7_relat_1(sK4,X0),k1_xboole_0)) )),
% 1.66/0.58    inference(resolution,[],[f315,f128])).
% 1.66/0.58  fof(f1023,plain,(
% 1.66/0.58    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | spl8_1),
% 1.66/0.58    inference(superposition,[],[f223,f978])).
% 1.66/0.58  fof(f223,plain,(
% 1.66/0.58    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | spl8_1),
% 1.66/0.58    inference(forward_demodulation,[],[f222,f151])).
% 1.66/0.58  fof(f151,plain,(
% 1.66/0.58    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)) )),
% 1.66/0.58    inference(subsumption_resolution,[],[f149,f65])).
% 1.66/0.58  fof(f149,plain,(
% 1.66/0.58    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0) | ~v1_funct_1(sK4)) )),
% 1.66/0.58    inference(resolution,[],[f96,f67])).
% 1.66/0.58  fof(f222,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | spl8_1),
% 1.66/0.58    inference(forward_demodulation,[],[f221,f197])).
% 1.66/0.58  fof(f221,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k7_relat_1(sK5,k3_xboole_0(sK2,sK3)) | spl8_1),
% 1.66/0.58    inference(forward_demodulation,[],[f220,f152])).
% 1.66/0.58  fof(f220,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k3_xboole_0(sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k3_xboole_0(sK2,sK3)) | spl8_1),
% 1.66/0.58    inference(superposition,[],[f109,f146])).
% 1.66/0.58  fof(f109,plain,(
% 1.66/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl8_1),
% 1.66/0.58    inference(avatar_component_clause,[],[f107])).
% 1.66/0.58  fof(f118,plain,(
% 1.66/0.58    ~spl8_1 | ~spl8_2 | ~spl8_3),
% 1.66/0.58    inference(avatar_split_clause,[],[f71,f115,f111,f107])).
% 1.66/0.58  fof(f71,plain,(
% 1.66/0.58    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 1.66/0.58    inference(cnf_transformation,[],[f43])).
% 1.66/0.58  % SZS output end Proof for theBenchmark
% 1.66/0.58  % (24897)------------------------------
% 1.66/0.58  % (24897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.58  % (24897)Termination reason: Refutation
% 1.66/0.58  
% 1.66/0.58  % (24897)Memory used [KB]: 11385
% 1.66/0.58  % (24897)Time elapsed: 0.133 s
% 1.66/0.58  % (24897)------------------------------
% 1.66/0.58  % (24897)------------------------------
% 1.66/0.58  % (24886)Success in time 0.219 s
%------------------------------------------------------------------------------
